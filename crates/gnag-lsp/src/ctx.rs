use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    io,
    ops::{self, Deref},
    sync::mpsc,
    time::Duration,
};

use anyhow::{bail, Context};
use gnag::{Node, StrSpan};
use lsp::{
    connection::{Connection, ReceiveIter},
    error::ProtocolError,
    msg::{ErrorCode, Message, RequestId, Response},
};
use lsp_types::TextDocumentContentChangeEvent;
use serde::Deserialize;
use serde_json::Value;

use crate::linemap::{LineMap, Utf16Pos};

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

impl ops::Deref for FileUrl {
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

pub struct File {
    version: i32,
    dirty: bool,
    pub linemap: LineMap,
    pub contents: String,
    pub ast_ir: gnag::file::File,
    pub root: gnag::Node,
    pub arena: Vec<gnag::Node>,
    pub parse_errors: Vec<gnag::ParseError>,
    pub convert_errors: Vec<gnag::ParseError>,
}

impl File {
    fn new(version: i32, contents: String) -> Self {
        let linemap = LineMap::new(&contents);
        let (ast_ir, parse_errors, convert_errors, arena, root) =
            gnag::file::File::new_from_string(&contents);
        Self {
            version,
            dirty: false,
            linemap,
            contents,
            ast_ir,
            root,
            arena,
            parse_errors,
            convert_errors,
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
                .replace_utf16_range(&mut self.contents, start..end, &change.text);
        } else {
            self.linemap.replace_whole(&mut self.contents, &change.text);
        }

        self.dirty = true;
        self.ast_ir = Default::default();
        // self.root = Default::default();
        self.arena = Default::default();
        self.parse_errors = Default::default();
        self.convert_errors = Default::default();
    }
    fn update_public(&mut self) {
        if self.dirty {
            // TODO reuse the public fields' allocations
            let (ast_ir, parse_errors, convert_errors, arena, root) =
                gnag::file::File::new_from_string(&self.contents);

            self.ast_ir = ast_ir;
            self.parse_errors = parse_errors;
            self.convert_errors = convert_errors;
            self.arena = arena;
            self.root = root;

            self.dirty = false;
        }
    }
    pub fn lsp_to_offset(&self, pos: lsp_types::Position) -> crate::linemap::Offset {
        let pos = Utf16Pos {
            line: pos.line,
            character: pos.character,
        };
        self.linemap.utf16_to_offset(&self.contents, pos)
    }
    pub fn offset_to_lsp(&self, pos: crate::linemap::Offset) -> lsp_types::Position {
        let utf16 = self.linemap.offset_to_utf16(&self.contents, pos);
        lsp_types::Position {
            line: utf16.line,
            character: utf16.character,
        }
    }
    pub fn span_to_lsp(&self, span: StrSpan) -> lsp_types::Range {
        let start = self.offset_to_lsp(span.start);
        let end = self.offset_to_lsp(span.end);
        lsp_types::Range { start, end }
    }
    pub fn find_leaf_cst_node_lsp(&self, pos: lsp_types::Position) -> Option<gnag::Node> {
        let offset = self.lsp_to_offset(pos);
        self.root.find(offset, &self.arena)
    }
    pub fn find_leaf_cst_node(&self, pos: crate::linemap::Offset) -> Option<gnag::Node> {
        self.root.find(pos, &self.arena)
    }
    pub fn node_identifier_text(&self, node: &Node) -> Option<&str> {
        if node.kind == gnag::NodeKind::Token(gnag::TokenKind::Ident) {
            Some(node.span.resolve(self))
        } else {
            None
        }
    }
}

pub trait StrSpanExt {
    fn resolve(self, file: &File) -> &str;
}

impl StrSpanExt for StrSpan {
    fn resolve(self, file: &File) -> &str {
        self.as_str(&file.contents)
    }
}

pub struct Ctx {
    config: Config,
    connection: Connection,
    files: HashMap<FileUrl, File>,
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

        self.files.insert(file, File::new(version, contents));
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
    pub fn get_file(&mut self, file: &FileUrlRef) -> Option<&File> {
        let file = self.files.get_mut(file)?;
        file.update_public();
        Some(file)
    }
    pub fn response(
        &self,
        id: RequestId,
        response: impl serde::Serialize,
    ) -> Result<(), mpsc::SendError<Message>> {
        self.send(Message::Response(Response {
            id,
            result: Some(serde_json::to_value(response).unwrap()),
            error: None,
        }))
    }
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
