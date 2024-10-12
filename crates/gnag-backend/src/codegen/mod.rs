#![allow(dead_code)]

pub mod render;
pub mod structure;

use code_render::{render, CollectFragments, Fragments, RenderCx};
use render::render_expression;
use structure::{lower_pattern, Flow, StructureBuilder};

use crate::backend::{grammar::Grammar, LexerKind, ParserKind, Rule, RuleKind};

pub fn render_file(grammar: &Grammar, rcx: &RenderCx) -> Fragments {
    let functions = render_functions(grammar, rcx);

    render!(rcx,
        use gnag_runtime::lexer::*;
        use gnag_runtime::parser::*;
        use gnag_runtime::*;

        #{functions}*
    )
}

pub fn render_functions(grammar: &Grammar, rcx: &RenderCx) -> Fragments {
    grammar
        .iter()
        .filter(|(_, rule, _)| match rule.kind {
            RuleKind::Lexer(LexerKind::Lexer) => true,
            RuleKind::Parser(ParserKind::Pratt | ParserKind::Rule) => true,
            _ => false,
        })
        .map(|(_, rule, _)| render_rule(rule, grammar, rcx))
        .collect_fragments(rcx)
}

fn render_rule(rule: &Rule, grammar: &Grammar, rcx: &RenderCx) -> Fragments {
    // TODO amortize builder
    let mut builder = StructureBuilder::new();

    lower_pattern(
        &rule.pattern,
        Flow::Unreachable,
        Flow::Unreachable,
        grammar,
        &mut builder,
    );

    let body = render_expression(&builder, rcx, grammar);

    render!(rcx,
        pub fn #{rule.name}(p: &mut Parser) -> bool {
            #body
        }
    )
}
