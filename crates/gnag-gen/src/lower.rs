use std::borrow::Borrow;

use crate::convert::{
    AstItem, CallExpr, ConvertedFile, RuleExpr, RuleHandle, TokenDef, TokenHandle, TokenPattern,
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
    stack: Vec<RuleHandle>,
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

        let tokens = file.tokens.map_ref(|token| lower_token(token, &mut cx));
        let mut rules = SecondaryVec::new();

        for handle in file.rules.iter_keys() {
            get_rule(handle, &mut rules, &mut cx);
        }

        LoweredFile {
            tokens,
            rules: HandleVec::try_from(rules).expect("All rules have been visited?"),
            errors: Vec::new(),
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
        TokenPattern::Invalid => LoweredTokenPattern::Error,
    }
}

fn get_rule<'a>(
    handle: RuleHandle,
    rules: &'a mut SecondaryVec<RuleHandle, RuleExpr>,
    cx: &mut LoweringCtx,
) -> &'a RuleExpr {
    // NLL issue workaround https://github.com/rust-lang/rust/issues/54663#issuecomment-973936708
    if rules.get(handle).is_some() {
        return rules.get(handle).unwrap();
    }

    let ir = &cx.file.rules[handle];

    if cx.stack.contains(&handle) {
        let prev = *cx.stack.last().unwrap();
        let prev_ir = &cx.file.rules[prev];
        let prev_ast = cx.file.get_rule_ast(prev);

        cx.error(
            prev_ast.span,
            format_args!(
                "Rule {} recursively includes itself through {}",
                prev_ir.name, ir.name
            ),
        );
    }

    let mut expr = ir.expr.clone();

    cx.stack.push(handle);
    expr.visit_nodes_bottom_up_mut(|node| {
        lower_expr_node(rules, node, cx);
    });
    cx.stack.pop();

    rules.entry(handle).insert(expr)
}

fn lower_expr_node(
    rules: &mut SecondaryVec<RuleHandle, RuleExpr>,
    node: &mut RuleExpr,
    cx: &mut LoweringCtx<'_, '_>,
) {
    match node {
        _ if node.is_empty_nonrecursive() => {
            *node = RuleExpr::Empty;
        }
        RuleExpr::Rule(rule) => {
            let rule_ir = &cx.file.rules[*rule];
            if rule_ir.inline {
                *node = get_rule(*rule, rules, cx).clone();
            }
        }
        RuleExpr::InlineCall(call) => {
            let CallExpr {
                rule,
                parameters,
                span,
            } = call.as_ref();

            let mut parameters = parameters.clone();
            for p in &mut parameters {
                lower_expr_node(rules, p, cx);
            }

            let rule_ir = &cx.file.rules[*rule];

            let expected = rule_ir.parameters.len();
            let provided = parameters.len();

            if !rule_ir.inline {
                cx.error(*span, format_args!("Rule {} is not inline", rule_ir.name));

                *node = RuleExpr::Error;
            } else if expected != provided {
                cx.error(
                    *span,
                    format_args!("Expected {expected} arguments, got {provided}"),
                );

                *node = RuleExpr::Error;
            } else {
                let mut expr = get_rule(*rule, rules, cx).clone();
                if !parameters.is_empty() {
                    expr.visit_nodes_top_down_mut(|node| {
                        if let &mut RuleExpr::InlineParameter(pos) = node {
                            *node = parameters
                                .get(pos)
                                .expect("InlineParameter out of bounds??")
                                .clone();
                        } else {
                            // we need to rerun this on the nodes because we could have
                            //  parameters A, B = Empty
                            //  Expr = Sequence(A B)
                            //    =>
                            //  Expr = Sequence(Empty Empty)
                            lower_expr_node(rules, node, cx);
                        }
                    })
                }

                *node = expr;
            }
        }
        RuleExpr::Sequence(a) => {
            // we can do this instead of mutual recursion (as in file::binary_expression)
            // because we've already processed any such nested equivalent expressions
            // and any more are the result of inlining rules
            // which are necessarily only one deep
            if a.iter()
                .any(|a| matches!(a, RuleExpr::Sequence(_) | RuleExpr::Empty))
            {
                let mut vec = Vec::new();
                for expr in a.drain(..) {
                    match expr {
                        RuleExpr::Sequence(inner) => vec.extend(inner),
                        RuleExpr::Empty => {}
                        _ => vec.push(expr),
                    }
                }
                *a = vec;
            }

            match a.len() {
                0 => *node = RuleExpr::Empty,
                1 => *node = a.pop().unwrap(),
                _ => {}
            }
        }
        RuleExpr::Choice(a) => {
            if a.iter()
                .any(|a| matches!(a, RuleExpr::Choice(_) | RuleExpr::Empty))
            {
                let mut vec = Vec::new();
                for expr in a.drain(..) {
                    match expr {
                        RuleExpr::Choice(inner) => vec.extend(inner),
                        // RuleExpr::Empty always matches without consuming anything so we can safely remove anything that would go after it
                        RuleExpr::Empty => {
                            vec.push(expr);
                            break;
                        }
                        _ => vec.push(expr),
                    }
                }
                *a = vec;
            }

            match a.len() {
                0 => *node = RuleExpr::Empty,
                1 => *node = a.pop().unwrap(),
                _ => {}
            }
        }
        _ => {}
    }
}
