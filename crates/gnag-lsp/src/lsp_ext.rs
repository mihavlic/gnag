use lsp_types::{request::Request, Range, TextDocumentIdentifier};
use serde::{Deserialize, Serialize};

pub enum ShowAst {}

impl Request for ShowAst {
    type Params = TextDocumentParams;
    type Result = String;
    const METHOD: &'static str = "gnag-lsp/showAst";
}

#[derive(Deserialize, Serialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentParams {
    pub text_document: TextDocumentIdentifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
}

pub enum ShowIr {}

impl Request for ShowIr {
    type Params = TextDocumentParams;
    type Result = String;
    const METHOD: &'static str = "gnag-lsp/showIr";
}
