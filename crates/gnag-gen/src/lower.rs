use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
};

use crate::{
    convert::{
        CallExpr, ConvertedFile, InlineHandle, RuleExpr, RuleHandle, TokenDef, TokenHandle,
        TokenPattern,
    },
    graph::Transition,
};
use gnag::{
    ctx::{ErrorAccumulator, SpanExt},
    handle::{HandleVec, SecondaryVec},
    StrSpan,
};

#[derive(Debug)]
pub enum LoweredTokenPattern {
    Regex(regex_syntax::hir::Hir),
    RustCode(String),
    Literal(Vec<u8>),
    Error,
}

impl Display for LoweredTokenPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regex(a) => write!(f, "Regex({a})"),
            Self::RustCode(a) => write!(f, "Regex({a:?})"),
            Self::Literal(a) => write!(f, "Regex({:?})", String::from_utf8_lossy(a)),
            Self::Error => write!(f, "Error"),
        }
    }
}

struct LoweringCx<'a, 'b, 'c> {
    src: &'a str,
    err: &'b ErrorAccumulator,
    file: &'c ConvertedFile,
    stack: Vec<InlineHandle>,
}

impl<'a, 'b, 'c> Borrow<str> for LoweringCx<'a, 'b, 'c> {
    fn borrow(&self) -> &str {
        self.src
    }
}

impl<'a, 'b, 'c> LoweringCx<'a, 'b, 'c> {
    fn new(src: &'a str, err: &'b ErrorAccumulator, file: &'c ConvertedFile) -> Self {
        Self {
            src,
            err,
            file,
            stack: Vec::new(),
        }
    }
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.err.error(span, err)
    }
}

pub struct LoweredFile {
    pub tokens: HandleVec<TokenHandle, LoweredTokenPattern>,
    pub rules: HandleVec<RuleHandle, RuleExpr>,
}

impl LoweredFile {
    pub fn new(src: &str, err: &ErrorAccumulator, file: &ConvertedFile) -> LoweredFile {
        let mut cx = LoweringCx::new(src, err, file);

        let mut inlines = SecondaryVec::new();
        for inline in file.inlines.iter_keys() {
            get_inline(inline, &mut inlines, &mut cx);
        }

        let tokens = file.tokens.map_ref(|token| lower_token(token, &mut cx));
        let rules = file.rules.map_ref(|rule| {
            let mut expr = rule.expr.clone();
            inline_calls(&mut expr, &mut inlines, &mut cx);
            expr
        });

        LoweredFile { tokens, rules }
    }
}

fn convert_regex_syntax_span(
    span: &regex_syntax::ast::Span,
    ast_span: StrSpan,
    cx: &impl Borrow<str>,
) -> StrSpan {
    let ast_str = ast_span.resolve(cx);
    let describe = gnag::ast::DescribedString::new(ast_str).unwrap();

    let start = u32::try_from(describe.find_offset(span.start.offset).unwrap()).unwrap();
    let mut end = u32::try_from(describe.find_offset(span.end.offset).unwrap()).unwrap();

    // regex_syntax likes to make spans where start==end
    // which vscode visualizes as start-1..end
    // which looks bad
    if start == end {
        end += 1;
    }

    StrSpan {
        start: ast_span.start + start,
        end: ast_span.start + end,
    }
}

fn lower_token(token: &TokenDef, cx: &LoweringCx) -> LoweredTokenPattern {
    match &token.pattern {
        TokenPattern::Regex(pattern) => match regex_syntax::parse(pattern) {
            Ok(hir) => match hir.kind() {
                regex_syntax::hir::HirKind::Literal(lit) => {
                    LoweredTokenPattern::Literal(lit.0.to_vec())
                }
                _ => LoweredTokenPattern::Regex(hir),
            },
            Err(err) => {
                match err {
                    regex_syntax::Error::Parse(err) => {
                        let span = convert_regex_syntax_span(err.span(), token.pattern_span, cx);
                        cx.error(span, err.kind());
                    }
                    regex_syntax::Error::Translate(err) => {
                        let span = convert_regex_syntax_span(err.span(), token.pattern_span, cx);
                        cx.error(span, err.kind());
                    }
                    _ => todo!(),
                }

                LoweredTokenPattern::Error
            }
        },
        TokenPattern::RustCode(s) => LoweredTokenPattern::RustCode(s.clone()),
        TokenPattern::SimpleString(s) => LoweredTokenPattern::Literal(s.as_bytes().to_vec()),
        // already repored
        TokenPattern::Invalid => LoweredTokenPattern::Error,
    }
}

fn get_inline<'a>(
    handle: InlineHandle,
    inlines: &'a mut SecondaryVec<InlineHandle, RuleExpr>,
    cx: &mut LoweringCx,
) -> &'a RuleExpr {
    // NLL issue workaround https://github.com/rust-lang/rust/issues/54663#issuecomment-973936708
    if inlines.get(handle).is_some() {
        return inlines.get(handle).unwrap();
    }

    let ir = &cx.file.inlines[handle];

    if cx.stack.contains(&handle) {
        let prev = *cx.stack.last().unwrap();
        let prev_name = cx.file.get_inline_name(prev);
        let prev_span = cx.file.inlines[prev].body.span;

        cx.error(
            prev_span,
            format_args!(
                "Rule {} recursively includes itself through {}",
                prev_name, ir.body.name
            ),
        );
    }

    let mut expr = ir.body.expr.clone();

    cx.stack.push(handle);
    inline_calls(&mut expr, inlines, cx);
    cx.stack.pop();

    inlines.entry(handle).insert(expr)
}

fn inline_calls(
    expr: &mut RuleExpr,
    inlines: &mut SecondaryVec<InlineHandle, RuleExpr>,
    cx: &mut LoweringCx,
) {
    expr.visit_nodes_bottom_up_mut(|node| {
        if let RuleExpr::InlineCall(_) = node {
            let RuleExpr::InlineCall(call) = std::mem::replace(node, RuleExpr::error()) else {
                unreachable!()
            };
            let CallExpr {
                template: handle,
                parameters,
                span,
            } = *call;

            // try to get the expanded body first because doing so can generate errors
            let expanded = get_inline(handle, inlines, cx);

            let rule_ir = &cx.file.inlines[handle];

            let expected_len = rule_ir.parameters.len();
            let provided_len = parameters.len();
            if expected_len != provided_len {
                cx.error(
                    span,
                    format_args!("Expected {expected_len} arguments, got {provided_len}"),
                );
                *node = RuleExpr::error();
            } else {
                *node = expanded.clone();
                if !parameters.is_empty() {
                    node.visit_nodes_top_down_mut(|node| {
                        if let &mut RuleExpr::InlineParameter(pos) = node {
                            *node = parameters
                                .get(pos)
                                .expect("InlineParameter out of bounds??")
                                .clone();
                        }
                    })
                }
            }
        };
        if let RuleExpr::Not(expr) = node {
            if let RuleExpr::Transition(Transition::Token(token)) = **expr {
                *node = RuleExpr::Transition(Transition::Not(token));
            } else {
                cx.error(
                    StrSpan::empty(),
                    "(TODO span) RuleExpr::Not only works with tokens",
                );
                *node = RuleExpr::error();
            }
        }
    });
}
