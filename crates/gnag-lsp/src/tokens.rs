use lsp_types::{SemanticTokenModifier, SemanticTokenType};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    Type,
    Parameter,
    Function,
    Comment,
    Decorator,
    String,
    Keyword,
    Number,
    Operator,
}

impl TokenType {
    pub fn types() -> &'static [SemanticTokenType] {
        const DATA: &'static [SemanticTokenType] = &[
            SemanticTokenType::new("type"),
            SemanticTokenType::new("parameter"),
            SemanticTokenType::new("function"),
            SemanticTokenType::new("comment"),
            SemanticTokenType::new("decorator"),
            SemanticTokenType::new("string"),
            SemanticTokenType::new("keyword"),
            SemanticTokenType::new("number"),
            SemanticTokenType::new("operator"),
        ];
        DATA
    }
}

pub enum TokenModifier {
    Declaration,
}

impl TokenModifier {
    pub fn types() -> &'static [SemanticTokenModifier] {
        const DATA: &'static [SemanticTokenModifier] = &[SemanticTokenModifier::new("declaration")];
        DATA
    }
}
