//! stolen from https://github.com/nvarner/typst-lsp/blob/10c15fdad2d80fbb675f983f223876d8a5d1a0b9/src/ext.rs#L17

use lsp_types::{InitializeParams, PositionEncodingKind, SemanticTokensClientCapabilities};

pub trait InitializeParamsExt {
    fn position_encodings(&self) -> &[PositionEncodingKind];
    fn supports_config_change_registration(&self) -> bool;
    fn semantic_tokens_capabilities(&self) -> Option<&SemanticTokensClientCapabilities>;
    fn supports_semantic_tokens_dynamic_registration(&self) -> bool;
}

const DEFAULT_ENCODING: &[PositionEncodingKind; 1] = &[PositionEncodingKind::UTF16];

impl InitializeParamsExt for InitializeParams {
    fn position_encodings(&self) -> &[PositionEncodingKind] {
        self.capabilities
            .general
            .as_ref()
            .and_then(|general| general.position_encodings.as_ref())
            .map(|encodings| encodings.as_slice())
            .unwrap_or(DEFAULT_ENCODING)
    }

    fn supports_config_change_registration(&self) -> bool {
        self.capabilities
            .workspace
            .as_ref()
            .and_then(|workspace| workspace.configuration)
            .unwrap_or(false)
    }

    fn semantic_tokens_capabilities(&self) -> Option<&SemanticTokensClientCapabilities> {
        self.capabilities
            .text_document
            .as_ref()?
            .semantic_tokens
            .as_ref()
    }

    fn supports_semantic_tokens_dynamic_registration(&self) -> bool {
        self.semantic_tokens_capabilities()
            .and_then(|semantic_tokens| semantic_tokens.dynamic_registration)
            .unwrap_or(false)
    }
}
