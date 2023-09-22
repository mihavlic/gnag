use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    fmt::{Debug, Display},
    io,
    ops::Deref,
    sync::mpsc,
    time::Duration,
};

use anyhow::{bail, Context};
use gnag::{ast::ParsedFile, ctx::SpanExt, file::ConvertedFile, Node, StrSpan};
use gnag_gen::LoweredFile;
use lsp::{
    connection::{Connection, ReceiveIter},
    error::ProtocolError,
    msg::{ErrorCode, Message, RequestId, Response},
};
use lsp_types::TextDocumentContentChangeEvent;
use serde::Deserialize;
use serde_json::Value;

use linemap::{LineMap, Utf16Pos};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BinaryConfigValue {
    Disable,
    #[default]
    Enable,
}

impl From<BinaryConfigValue> for bool {
    fn from(value: BinaryConfigValue) -> Self {
        value == BinaryConfigValue::Enable
    }
}

pub struct Config {
    pub semantic_tokens: bool,
    pub diagnostics_on_save: bool,
}

impl Config {
    pub fn new(mut value: Value) -> anyhow::Result<Self> {
        let Value::Object(fields) = &mut value else {
            bail!("json::Value is not an object!");
        };

        let semantic_tokens = read_field(fields, "semanticTokens")?;
        let diagnostics_on_save = read_field(fields, "diagnosticsOnSave")?;

        Ok(Self {
            semantic_tokens: semantic_tokens,
            diagnostics_on_save: diagnostics_on_save,
        })
    }
}

fn read_field<T: for<'de> Deserialize<'de>>(
    fields: &mut serde_json::Map<String, Value>,
    name: &str,
) -> anyhow::Result<T> {
    let field = fields
        .remove(name)
        .with_context(|| format!("Expected field config.{name}"))?;

    let typename = std::any::type_name::<T>();
    serde_json::from_value::<T>(field.clone())
        .with_context(|| format!("Expected type {typename}, got {field}"))
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FileUrl(String);

impl From<lsp_types::Url> for FileUrl {
    fn from(value: lsp_types::Url) -> Self {
        FileUrl(value.into())
    }
}

impl Debug for FileUrl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Deref for FileUrl {
    type Target = FileUrlRef;
    fn deref(&self) -> &Self::Target {
        self.0.as_str().into()
    }
}

impl std::borrow::Borrow<FileUrlRef> for FileUrl {
    fn borrow(&self) -> &FileUrlRef {
        self.deref()
    }
}

#[repr(transparent)]
#[derive(PartialEq, Eq, Hash)]
pub struct FileUrlRef(str);

impl AsRef<FileUrlRef> for lsp_types::Url {
    fn as_ref(&self) -> &FileUrlRef {
        <&FileUrlRef>::from(self)
    }
}

impl From<&str> for &FileUrlRef {
    fn from(value: &str) -> Self {
        // SAFETY: FileUrlRef is repr(transparent)
        unsafe { std::mem::transmute::<&str, &FileUrlRef>(value) }
    }
}

impl From<&lsp_types::Url> for &FileUrlRef {
    fn from(value: &lsp_types::Url) -> Self {
        value.as_str().into()
    }
}

impl Debug for FileUrlRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

pub struct LspFile {
    version: i32,

    src: String,
    linemap: LineMap,

    parsed: RefCell<Option<ParsedFile>>,
    converted: RefCell<Option<ConvertedFile>>,
    lowered: RefCell<Option<LoweredFile>>,
}

impl std::borrow::Borrow<str> for LspFile {
    fn borrow(&self) -> &str {
        &self.src
    }
}

impl LspFile {
    fn new(version: i32, src: String) -> Self {
        Self {
            version,
            linemap: LineMap::new(&src),
            src,
            parsed: Default::default(),
            converted: Default::default(),
            lowered: Default::default(),
        }
    }
    fn update(&mut self, change: &TextDocumentContentChangeEvent) {
        // https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_didChange
        // if change.range is None, replace the whole file
        if let Some(range) = change.range {
            let start = Utf16Pos {
                line: range.start.line,
                character: range.start.character,
            };
            let end = Utf16Pos {
                line: range.end.line,
                character: range.end.character,
            };
            self.linemap
                .replace_utf16_range(&mut self.src, start..end, &change.text);
        } else {
            self.linemap.replace_whole(&mut self.src, &change.text);
        }

        self.parsed = Default::default();
        self.converted = Default::default();
        self.lowered = Default::default();
    }
    pub fn src(&self) -> &str {
        &self.src
    }
    pub fn get_parsed(&self) -> Ref<ParsedFile> {
        if let Ok(some) = Ref::filter_map(self.parsed.borrow(), |a| a.as_ref()) {
            return some;
        }

        _ = self.parsed.borrow_mut().insert(ParsedFile::new(&self.src));

        Ref::map(self.parsed.borrow(), |a| a.as_ref().unwrap())
    }
    pub fn get_converted(&self) -> Ref<ConvertedFile> {
        if let Ok(some) = Ref::filter_map(self.converted.borrow(), |a| a.as_ref()) {
            return some;
        }

        let parsed = self.get_parsed();
        _ = self
            .converted
            .borrow_mut()
            .insert(ConvertedFile::new(&self.src, &parsed));

        Ref::map(self.converted.borrow(), |a| a.as_ref().unwrap())
    }
    pub fn get_lowered(&self) -> Ref<LoweredFile> {
        if let Ok(some) = Ref::filter_map(self.lowered.borrow(), |a| a.as_ref()) {
            return some;
        }

        let converted = self.get_converted();
        _ = self
            .lowered
            .borrow_mut()
            .insert(LoweredFile::new(&self.src, &converted));

        Ref::map(self.lowered.borrow(), |a| a.as_ref().unwrap())
    }
    pub fn lsp_to_offset(&self, pos: lsp_types::Position) -> linemap::Offset {
        let pos = Utf16Pos {
            line: pos.line,
            character: pos.character,
        };
        self.linemap.utf16_to_offset(&self.src, pos)
    }
    pub fn offset_to_lsp(&self, pos: linemap::Offset) -> lsp_types::Position {
        let utf16 = self.linemap.offset_to_utf16(&self.src, pos);
        lsp_types::Position {
            line: utf16.line,
            character: utf16.character,
        }
    }
    pub fn lsp_to_span(&self, span: lsp_types::Range) -> StrSpan {
        let start = self.lsp_to_offset(span.start);
        let end = self.lsp_to_offset(span.end);
        StrSpan { start, end }
    }
    pub fn span_to_lsp(&self, span: StrSpan) -> lsp_types::Range {
        let start = self.offset_to_lsp(span.start);
        let end = self.offset_to_lsp(span.end);
        lsp_types::Range { start, end }
    }
}

// pub struct DoubleDeref<'a, 'b, A: ?Sized, B: ?Sized>(pub &'a A, pub &'b B);

// impl<'a, 'b, A, B> DoubleDeref<'a, 'b, A, B> {
//     // pub fn new(a: &'a A, b: &'b B) {
//     //     Self { a, b }
//     // }
//     pub fn a(&self) -> &'a A {
//         self.0
//     }
//     pub fn b(&self) -> &'b B {
//         self.1
//     }
// }

// impl<'a, 'b, A, B> Deref for DoubleDeref<'a, 'b, A, B> {
//     type Target = A;
//     fn deref(&self) -> &Self::Target {
//         self.0
//     }
// }

// pub trait WithDoubleDeref {
//     fn with_double_deref<'a, 'b, T>(&'a self, file: &'b T) -> DoubleDeref<'a, 'b, Self, T> {
//         DoubleDeref(self, file)
//     }
// }
// impl<T> WithDoubleDeref for T {}

pub trait ParsedFileExt {
    fn this(&self) -> &ParsedFile;

    fn find_leaf_cst_node_lsp(
        &self,
        file: &LspFile,
        pos: lsp_types::Position,
    ) -> Option<&gnag::Node> {
        let offset = file.lsp_to_offset(pos);
        self.find_leaf_cst_node(offset)
    }
    fn find_leaf_cst_node(&self, pos: linemap::Offset) -> Option<&gnag::Node> {
        let this = self.this();

        this.root.find_leaf(pos, &this.arena)
    }
    fn find_covering_cst_node_lsp(
        &self,
        file: &LspFile,
        span: lsp_types::Range,
    ) -> Option<&gnag::Node> {
        let span = file.lsp_to_span(span);
        self.find_covering_cst_node(span)
    }
    fn find_covering_cst_node(&self, span: StrSpan) -> Option<&gnag::Node> {
        let this = self.this();

        this.root.find_covering(span, &this.arena)
    }
    fn trim_selection(&self, file: &LspFile, span: StrSpan) -> StrSpan {
        let selection = span.resolve(file);
        let trim = selection.trim();

        let start_diff = trim.as_ptr() as usize - selection.as_ptr() as usize;
        let len_diff = selection.len() - trim.len();

        let start_diff = u32::try_from(start_diff).unwrap();
        let len_diff = u32::try_from(len_diff).unwrap();

        StrSpan {
            start: span.start + start_diff,
            end: (span.end + start_diff) - len_diff,
        }
    }
    fn node_identifier_text<'b>(&self, file: &'b LspFile, node: &Node) -> Option<&'b str> {
        if node.kind == gnag::NodeKind::Token(gnag::TokenKind::Ident) {
            Some(node.span.resolve(file))
        } else {
            None
        }
    }
}

impl ParsedFileExt for ParsedFile {
    fn this(&self) -> &ParsedFile {
        self
    }
}

pub struct Ctx {
    config: Config,
    connection: Connection,
    files: HashMap<FileUrl, LspFile>,
}

impl Ctx {
    pub fn new(config: Config, connection: Connection) -> Ctx {
        Ctx {
            config,
            connection,
            files: HashMap::new(),
        }
    }
    pub fn config(&self) -> &Config {
        &self.config
    }
    pub fn file_opened(&mut self, file: FileUrl, contents: String, version: i32) {
        if self.files.contains_key(&file) {
            log::warn!("File {file:?} opened twice.");
        }

        self.files.insert(file, LspFile::new(version, contents));
    }
    pub fn file_closed(&mut self, file: &FileUrlRef) {
        self.files.remove(file);
    }
    pub fn modify_file(
        &mut self,
        file: &FileUrlRef,
        new_version: i32,
        changes: &[TextDocumentContentChangeEvent],
    ) -> Result<(), ModifyFileError> {
        if let Some(file) = self.files.get_mut(file) {
            if file.version > new_version {
                return Err(ModifyFileError::VersionLower);
            }

            for change in changes {
                file.update(change);
            }

            Ok(())
        } else {
            Err(ModifyFileError::FileNotOpened)
        }
    }
    pub fn get_file(&mut self, file: &FileUrlRef) -> Option<&LspFile> {
        self.files.get(file)
    }
    // pub fn response(
    //     &self,
    //     id: RequestId,
    //     response: impl serde::Serialize,
    // ) -> Result<(), mpsc::SendError<Message>> {
    //     self.send(Message::Response(Response {
    //         id,
    //         result: Some(serde_json::to_value(response).unwrap()),
    //         error: None,
    //     }))
    // }
    pub fn error(
        &self,
        id: RequestId,
        code: ErrorCode,
        message: impl ToString,
    ) -> Result<(), mpsc::SendError<Message>> {
        self.send(Response::new_err(id, code, message.to_string()))
    }

    pub fn send(&self, message: impl Into<Message>) -> Result<(), mpsc::SendError<Message>> {
        self.connection.send(message)
    }
    pub fn receive(&self) -> Result<io::Result<Message>, mpsc::RecvError> {
        self.connection.receive()
    }
    pub fn receive_timeout(
        &self,
        timeout: Duration,
    ) -> Result<io::Result<Message>, mpsc::RecvTimeoutError> {
        self.connection.receive_timeout(timeout)
    }
    pub fn try_receive(&self) -> Result<io::Result<Message>, mpsc::TryRecvError> {
        self.connection.try_receive()
    }
    pub fn receive_iter(&self) -> ReceiveIter<'_> {
        self.connection.receive_iter()
    }
    pub fn shutdown_and_exit(&self, id: RequestId) -> Result<(), ProtocolError> {
        self.connection.shutdown_and_exit(id)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModifyFileError {
    FileNotOpened,
    VersionLower,
}

impl Display for ModifyFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self, f)
    }
}

impl std::error::Error for ModifyFileError {}
