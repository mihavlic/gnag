use std::{borrow::Borrow, ops::ControlFlow};

use gnag::{
    ctx::{ConvertCtx, SpanExt},
    file::{AstItem, CallExpr, RuleExpr, RuleHandle, TokenHandle, TokenPattern},
    handle::{HandleVec, SecondaryVec},
    SpannedError, StrSpan,
};

#[derive(Debug)]
pub enum LoweredTokenPattern {
    Regex(regex_syntax::hir::Hir),
    RustCode(String),
    Error,
}

pub struct LoweringCtx<'a, 'b> {
    inner: ConvertCtx<'a>,
    file: &'b gnag::file::ConvertedFile,
    stack: Vec<RuleHandle>,
}

impl<'a, 'b> LoweringCtx<'a, 'b> {
    pub fn new(src: &'a str, file: &'b gnag::file::ConvertedFile) -> LoweringCtx<'a, 'b> {
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
    pub lowered_tokens: HandleVec<TokenHandle, LoweredTokenPattern>,
    pub lowered_rules: SecondaryVec<RuleHandle, RuleExpr>,
    pub errors: Vec<SpannedError>,
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

    // regex_syntax likes to make spand where start==end
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

fn lower_token(token: &gnag::file::TokenDef, cx: &LoweringCtx) -> LoweredTokenPattern {
    match &token.pattern {
        TokenPattern::Regex(pattern) => match regex_syntax::parse(pattern) {
            Ok(hir) => LoweredTokenPattern::Regex(hir),
            Err(err) => {
                let AstItem::Token(ast, _) = &cx.file.ast_items[token.ast] else {
                    unreachable!()
                };
                let span = match ast.pattern {
                    gnag::ast::TokenValue::Regex(span) => span,
                    gnag::ast::TokenValue::Arbitrary(span) => span,
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
        TokenPattern::RustCode(code) => LoweredTokenPattern::RustCode(code.clone()),
    }
}

impl LoweredFile {
    pub fn new(src: &str, file: &gnag::file::ConvertedFile) -> LoweredFile {
        let mut cx = LoweringCtx::new(src, file);
        let mut lowered = LoweredFile {
            lowered_tokens: file.tokens.map_ref(|token| lower_token(token, &mut cx)),
            lowered_rules: SecondaryVec::new(),
            errors: Vec::new(),
        };

        for handle in file.rules.iter_keys() {
            lowered.get_rule(handle, &mut cx);
        }

        lowered.errors = cx.finish();
        lowered
    }
    fn get_rule(&mut self, handle: RuleHandle, cx: &mut LoweringCtx) -> &RuleExpr {
        // NLL issue workaround https://github.com/rust-lang/rust/issues/54663#issuecomment-973936708
        if self.lowered_rules.get(handle).is_some() {
            return self.lowered_rules.get(handle).unwrap();
        }

        let ir = &cx.file.rules[handle];

        if cx.stack.contains(&handle) {
            let prev = *cx.stack.last().unwrap();
            let prev_ir = &cx.file.rules[prev];

            let AstItem::Rule(ast, _) = &cx.file.ast_items[prev_ir.ast] else {
                unreachable!()
            };

            cx.error(
                ast.span,
                format_args!(
                    "Rule {} recursively includes itself through {}",
                    prev_ir.name, ir.name
                ),
            );

            // let expr = ast.expression.as_ref().expect("Rule must contain some expression to cause a cycle.");
            // expr.visit(&mut |expr| if let Expression::Ident(e) = expr {
            //     if e.resolve(cx) == &ir.name {
            //         cx.error(*e, "Rule ")
            //     }
            // })
        }

        let mut expr = ir.expr.clone();

        cx.stack.push(handle);
        expr.visit_nodes_bottom_up(|node| {
            if let ControlFlow::Break(_) = self.lower_expr_node(node, cx) {
                return;
            }
        });
        cx.stack.pop();

        self.lowered_rules.entry(handle).insert(expr)
    }
    fn lower_expr_node(
        &mut self,
        node: &mut RuleExpr,
        cx: &mut LoweringCtx<'_, '_>,
    ) -> ControlFlow<()> {
        match node {
            RuleExpr::Rule(rule) => {
                let rule_ir = &cx.file.rules[*rule];
                if rule_ir.inline {
                    *node = self.get_rule(*rule, cx).clone();
                }
            }
            RuleExpr::InlineCall(call) => {
                let CallExpr {
                    rule,
                    parameters,
                    span,
                } = call.as_ref();

                let mut arguments = parameters.clone();
                for p in &mut arguments {
                    self.lower_expr_node(p, cx);
                }

                let rule_ir = &cx.file.rules[*rule];

                let expected = rule_ir.parameters.len();
                let provided = arguments.len();
                if !rule_ir.inline {
                    cx.error(*span, format_args!("Rule {} is not inline", rule_ir.name));
                    *node = RuleExpr::Error;
                    return ControlFlow::Break(());
                } else if expected != provided {
                    cx.error(
                        *span,
                        format_args!("Expected {expected} arguments, got {provided}"),
                    );
                    *node = RuleExpr::Error;
                    return ControlFlow::Break(());
                }

                let mut expr = self.get_rule(*rule, cx).clone();
                if !arguments.is_empty() {
                    expr.visit_nodes_top_down(|node| {
                        if let &mut RuleExpr::InlineParameter(pos) = node {
                            *node = arguments
                                .get(pos)
                                .expect("InlineParameter out of bounds??")
                                .clone();
                        }
                    })
                }

                *node = expr;
            }
            RuleExpr::Sequence(a) => {
                // we can do this instead of mutual recursion (as in file::binary_expression)
                // because we've already processed any such nested equivalent expressions
                // and any more are the result of inlining rules
                // which are necessarily only one deep
                if a.iter().any(|a| matches!(a, RuleExpr::Sequence(_))) {
                    let mut vec = Vec::new();
                    for expr in a.drain(..) {
                        if let RuleExpr::Sequence(inner) = expr {
                            vec.extend(inner);
                        } else {
                            vec.push(expr);
                        }
                    }
                    *a = vec;
                }
            }
            RuleExpr::Choice(a) => {
                if a.iter().any(|a| matches!(a, RuleExpr::Choice(_))) {
                    let mut vec = Vec::new();
                    for expr in a.drain(..) {
                        if let RuleExpr::Choice(inner) = expr {
                            vec.extend(inner);
                        } else {
                            vec.push(expr);
                        }
                    }
                    *a = vec;
                }
            }
            _ => {}
        }
        ControlFlow::Continue(())
    }
}
