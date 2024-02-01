use std::borrow::Borrow;

use crate::convert::{
    AstItem, CallExpr, ConvertedFile, InlineHandle, RuleExpr, RuleHandle, TokenDef, TokenHandle,
    TokenPattern,
};
use gnag::{
    ctx::{ConvertCtx, SpanExt},
    handle::{HandleVec, SecondaryVec},
    SpannedError, StrSpan,
};

#[derive(Debug)]
pub enum LoweredTokenPattern {
    Regex(regex_syntax::hir::Hir),
    RustCode(String),
    Literal(Vec<u8>),
    Error,
}

pub struct LoweringCtx<'a, 'b> {
    inner: ConvertCtx<'a>,
    file: &'b ConvertedFile,
    stack: Vec<InlineHandle>,
}

impl<'a, 'b> LoweringCtx<'a, 'b> {
    pub fn new(src: &'a str, file: &'b ConvertedFile) -> LoweringCtx<'a, 'b> {
        Self {
            inner: ConvertCtx::new(src),
            file,
            stack: Vec::new(),
        }
    }
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.inner.error(span, err)
    }
    pub fn finish(self) -> Vec<SpannedError> {
        self.inner.finish()
    }
}

impl Borrow<str> for LoweringCtx<'_, '_> {
    fn borrow(&self) -> &str {
        self.inner.borrow()
    }
}

pub struct LoweredFile {
    pub tokens: HandleVec<TokenHandle, LoweredTokenPattern>,
    pub rules: HandleVec<RuleHandle, RuleExpr>,
    pub errors: Vec<SpannedError>,
}

impl LoweredFile {
    pub fn new(src: &str, file: &ConvertedFile) -> LoweredFile {
        let mut cx = LoweringCtx::new(src, file);

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

        LoweredFile {
            tokens,
            rules,
            errors: cx.finish(),
        }
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

fn lower_token(token: &TokenDef, cx: &LoweringCtx) -> LoweredTokenPattern {
    match &token.pattern {
        TokenPattern::Regex(pattern) => match regex_syntax::parse(pattern) {
            Ok(hir) => match hir.kind() {
                regex_syntax::hir::HirKind::Literal(lit) => {
                    LoweredTokenPattern::Literal(lit.0.to_vec())
                }
                _ => LoweredTokenPattern::Regex(hir),
            },
            Err(err) => {
                let AstItem::Token(ast, _) = &cx.file.ast_items[token.ast] else {
                    unreachable!()
                };
                let span = match ast.pattern {
                    gnag::ast::TokenValue::String(s) => s,
                    gnag::ast::TokenValue::RustCode(s) => s,
                };

                match err {
                    regex_syntax::Error::Parse(err) => {
                        let span = convert_regex_syntax_span(err.span(), span, cx);
                        cx.error(span, err.kind());
                    }
                    regex_syntax::Error::Translate(err) => {
                        let span = convert_regex_syntax_span(err.span(), span, cx);
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
    cx: &mut LoweringCtx,
) -> &'a RuleExpr {
    // NLL issue workaround https://github.com/rust-lang/rust/issues/54663#issuecomment-973936708
    if inlines.get(handle).is_some() {
        return inlines.get(handle).unwrap();
    }

    let ir = &cx.file.inlines[handle];

    if cx.stack.contains(&handle) {
        let prev = *cx.stack.last().unwrap();
        let prev_name = cx.file.get_inline_name(prev);
        let prev_ast = cx.file.get_inline_ast(prev);

        cx.error(
            prev_ast.span,
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
    cx: &mut LoweringCtx<'_, '_>,
) {
    expr.visit_nodes_bottom_up_mut(|node| {
        if let RuleExpr::InlineCall(call) = node {
            let CallExpr {
                template: handle,
                parameters,
                span,
            } = call.as_ref();

            // try to get the expanded body first because doing so can generate errors
            let expanded = get_inline(*handle, inlines, cx);

            let rule_ir = &cx.file.inlines[*handle];

            let expected_len = rule_ir.parameters.len();
            let provided_len = parameters.len();
            if expected_len != provided_len {
                cx.error(
                    *span,
                    format_args!("Expected {expected_len} arguments, got {provided_len}"),
                );
                *node = RuleExpr::Error;
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
    });
}
