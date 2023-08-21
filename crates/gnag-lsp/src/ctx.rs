use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::{Debug, Display},
    ops,
};

use anyhow::{bail, Context};
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

struct File {
    linemap: LineMap,
    contents: String,
    version: i32,
}

pub struct Ctx {
    config: Config,
    files: HashMap<FileUrl, File>,
}

impl Ctx {
    pub fn new(config: Config) -> Ctx {
        Ctx {
            config,
            files: HashMap::new(),
        }
    }
    pub fn file_opened(&mut self, file: FileUrl, contents: String, version: i32) {
        if self.files.contains_key(&file) {
            log::warn!("File {file:?} opened twice.");
        }

        self.files.insert(
            file,
            File {
                linemap: LineMap::new(&contents),
                contents,
                version,
            },
        );
    }
    pub fn modify_file(
        &mut self,
        file: &FileUrl,
        new_version: i32,
        changes: &[TextDocumentContentChangeEvent],
    ) -> Result<(), ModifyFileError> {
        if let Some(file) = self.files.get_mut(file) {
            let File {
                linemap,
                contents,
                version,
            } = file;

            if *version > new_version {
                return Err(ModifyFileError::VersionLower);
            }

            for change in changes {
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
                    linemap.replace_utf16_range(contents, start..end, &change.text);
                } else {
                    linemap.replace_whole(contents, &change.text);
                }
            }

            Ok(())
        } else {
            Err(ModifyFileError::FileNotOpened)
        }
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
