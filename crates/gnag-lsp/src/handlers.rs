use std::hash::Hasher;

use anyhow::Context;
use gnag::{
    file::{AstItem, RuleExpr},
    NodeKind, StrSpan,
};
use lsp_types::{CompletionItemKind, GotoDefinitionResponse, SymbolKind};

use crate::ctx::{Ctx, StrSpanExt};

pub fn definition(
    cx: &mut Ctx,
    params: &lsp_types::GotoDefinitionParams,
) -> anyhow::Result<serde_json::Value> {
    let position = &params.text_document_position_params;
    let file = cx.get_file(position.text_document.uri.as_ref()).unwrap();

    let node = file
        .find_leaf_cst_node_lsp(position.position)
        .context("Text position is invalid")?;

    if let Some(identifier) = file.node_identifier_text(&node) {
        if let Some(found) = file
            .ast_ir
            .ast_items
            .iter()
            .find(|item| item.name().resolve(file) == identifier)
        {
            return GotoDefinitionResponse::Scalar(lsp_types::Location {
                uri: position.text_document.uri.clone(),
                range: file.span_to_lsp(found.name()),
            })
            .serialize();
        }
    }

    GotoDefinitionResponse::Array(Vec::new()).serialize()
}

#[allow(deprecated)]
pub fn document_symbol(
    cx: &mut Ctx,
    params: &lsp_types::DocumentSymbolParams,
) -> anyhow::Result<serde_json::Value> {
    let file = cx.get_file(params.text_document.uri.as_ref()).unwrap();
    let symbols = file
        .ast_ir
        .ast_items
        .iter()
        .map(|item| lsp_types::SymbolInformation {
            name: item.name().resolve(file).to_owned(),
            kind: match item {
                gnag::file::AstItem::Token(_, _) => SymbolKind::ENUM_MEMBER,
                gnag::file::AstItem::Rule(_, _) => SymbolKind::FUNCTION,
            },
            tags: None,
            location: lsp_types::Location {
                uri: params.text_document.uri.clone(),
                range: file.span_to_lsp(item.name()),
            },
            deprecated: None,
            container_name: None,
        })
        .collect();

    lsp_types::DocumentSymbolResponse::Flat(symbols).serialize()
}

#[derive(Debug)]
enum CompletionFilter {
    Symbols,
    // inline rules + builtin functions
    Callable,
    Invalid,
}

pub fn completion(
    cx: &mut Ctx,
    params: &lsp_types::CompletionParams,
) -> anyhow::Result<serde_json::Value> {
    let file = cx
        .get_file(params.text_document_position.text_document.uri.as_ref())
        .unwrap();

    let cursor = file.lsp_to_offset(params.text_document_position.position);
    let mut trace = file.root.find_with_trace(cursor, &file.arena);

    let mut filter = CompletionFilter::Invalid;
    for node in trace.ancestor_iter() {
        if cursor == node.span.start {
            continue;
        }

        match node.kind {
            NodeKind::Tree(gnag::TreeKind::CallExpr) => {
                let ident = node
                    .children(&file.arena)
                    .iter()
                    .find(|c| c.kind == NodeKind::Token(gnag::TokenKind::Ident));

                if let Some(ident) = ident {
                    if cursor <= ident.span.end {
                        // we use <= for the following situation
                        //  < ident_name<cursor> ... >
                        //              |
                        // the cursor is recognized as within the next token (whitespace) but
                        // we still want to provide completions for the first ident
                        filter = CompletionFilter::Callable;
                    } else {
                        filter = CompletionFilter::Symbols;
                    };
                } else {
                    filter = CompletionFilter::Callable
                }
                break;
            }
            NodeKind::Tree(gnag::TreeKind::SynRule) => {
                filter = CompletionFilter::Symbols;
                break;
            }
            NodeKind::Token(_) => unreachable!(),
            _ => {}
        }
    }

    let mut partial_text = "";
    if let Some(current) = trace.current() {
        // aaaaaaa<whitespace>
        //        | cursor
        if cursor == current.span.start {
            trace.enter_sibling_before(&file.arena);
            trace.enter_rightmost_leaf(&file.arena);
        }

        let current = trace.current().unwrap();
        if current.kind == NodeKind::Token(gnag::TokenKind::Ident) {
            let span = StrSpan {
                start: current.span.start,
                end: cursor,
            };
            partial_text = span.resolve(&file);
        }
    };

    log::trace!("  filter: {filter:?}, partial_text: '{partial_text}'");

    let list = match filter {
        CompletionFilter::Symbols => collect_completion_list(
            file.ast_ir
                .ast_items
                .iter()
                .map(|item| (item.name().resolve(&file), item_to_completion_kind(item))),
        ),
        CompletionFilter::Callable => collect_completion_list(
            file.ast_ir
                .ast_items
                .iter()
                .filter_map(|item| match item {
                    AstItem::Rule(rule, _) => rule.inline.then_some(item.name().resolve(&file)),
                    AstItem::Token(_, _) => None,
                })
                .chain(RuleExpr::BUILTIN_RULES.iter().copied())
                .map(|name| (name, lsp_types::CompletionItemKind::FUNCTION)),
        ),
        CompletionFilter::Invalid => lsp_types::CompletionList {
            is_incomplete: false,
            items: Vec::new(),
        },
    };

    lsp_types::CompletionResponse::List(list).serialize()
}

fn item_to_completion_kind(item: &gnag::file::AstItem) -> CompletionItemKind {
    match item {
        gnag::file::AstItem::Token(_, _) => lsp_types::CompletionItemKind::ENUM_MEMBER,
        gnag::file::AstItem::Rule(_, _) => lsp_types::CompletionItemKind::FUNCTION,
    }
}

fn collect_completion_list<'a>(
    iter: impl IntoIterator<Item = (&'a str, lsp_types::CompletionItemKind)>,
) -> lsp_types::CompletionList {
    let items: Vec<_> = iter
        .into_iter()
        .map(|(name, kind)| lsp_types::CompletionItem {
            label: name.to_owned(),
            kind: Some(kind),
            ..Default::default()
        })
        .collect();

    lsp_types::CompletionList {
        is_incomplete: true,
        items,
    }
}

pub fn formatting(
    cx: &mut Ctx,
    params: &lsp_types::DocumentFormattingParams,
) -> anyhow::Result<serde_json::Value> {
    anyhow::bail!("TODO")
}

pub fn diagnostic(
    cx: &mut Ctx,
    params: &lsp_types::DocumentDiagnosticParams,
) -> anyhow::Result<serde_json::Value> {
    let file = cx.get_file(params.text_document.uri.as_ref()).unwrap();
    let hash = {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&file.errors, &mut hasher);
        hasher.finish()
    };
    let hash = format!("{hash:x}");

    if params.previous_result_id.as_ref() == Some(&hash) {
        lsp_types::DocumentDiagnosticReport::Unchanged(
            lsp_types::RelatedUnchangedDocumentDiagnosticReport {
                related_documents: None,
                unchanged_document_diagnostic_report:
                    lsp_types::UnchangedDocumentDiagnosticReport { result_id: hash },
            },
        )
    } else {
        let items = file
            .errors
            .iter()
            .map(|e| lsp_types::Diagnostic {
                range: file.span_to_lsp(e.span),
                severity: Some(lsp_types::DiagnosticSeverity::ERROR),
                message: e.err.clone(),
                ..Default::default()
            })
            .collect();

        lsp_types::DocumentDiagnosticReport::Full(lsp_types::RelatedFullDocumentDiagnosticReport {
            related_documents: None,
            full_document_diagnostic_report: lsp_types::FullDocumentDiagnosticReport {
                result_id: Some(hash),
                items,
            },
        })
    }
    .serialize()
}

trait JsonAnyhowSerialize {
    fn serialize(&self) -> anyhow::Result<serde_json::Value>;
}

impl<T: serde::Serialize> JsonAnyhowSerialize for T {
    fn serialize(&self) -> anyhow::Result<serde_json::Value> {
        Ok(serde_json::to_value(self)?)
    }
}
