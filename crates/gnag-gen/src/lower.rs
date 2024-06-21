use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
};

use crate::{
    convert::{ConvertedFile, InlineHandle, RuleHandle, TokenDef, TokenHandle, TokenPattern},
    expr::{CallExpr, RuleExpr, Transition},
    pratt::{Associativity, PrattExprKind},
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
        let rules = file.rules.map_ref_with_key(|handle, rule| {
            let mut expr = rule.expr.clone();
            lower_expr(handle, &mut expr, &mut inlines, &mut cx);
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
    expr.visit_nodes_bottom_up_mut(|node| {
        if let RuleExpr::InlineCall(call) = node {
            *node = inline_call(call, inlines, cx);
        }
    });
    cx.stack.pop();

    inlines.entry(handle).insert(expr)
}

fn inline_call(
    call: &CallExpr,
    inlines: &mut SecondaryVec<InlineHandle, RuleExpr>,
    cx: &mut LoweringCx,
) -> RuleExpr {
    let CallExpr {
        template: handle,
        ref parameters,
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
        RuleExpr::error()
    } else {
        let mut expanded = expanded.clone();
        if !parameters.is_empty() {
            expanded.visit_nodes_bottom_up_mut(|node| {
                if let &mut RuleExpr::InlineParameter(pos) = node {
                    *node = parameters
                        .get(pos)
                        .expect("InlineParameter out of bounds??")
                        .clone();
                }
            });
        }
        expanded
    }
}

pub fn visit_affix_leaves(
    expr: &mut RuleExpr,
    prefix: bool,
    on_leaf: &mut dyn FnMut(&mut RuleExpr) -> bool,
) -> Option<bool> {
    match expr {
        RuleExpr::Transition(_) => Some(on_leaf(expr)),
        RuleExpr::Sequence(vec) => {
            let expr = match prefix {
                true => vec.first_mut(),
                false => vec.last_mut(),
            };
            expr.and_then(|e| visit_affix_leaves(e, prefix, on_leaf))
        }
        RuleExpr::Choice(vec) => {
            let mut contains_true = false;
            let mut contains_false = false;

            for expr in vec {
                match visit_affix_leaves(expr, prefix, on_leaf) {
                    Some(true) => contains_true = true,
                    Some(false) => contains_false = true,
                    None => return None,
                }
            }

            // children must all be true or all false, otherwise return None
            match (contains_true, contains_false) {
                (true, false) => Some(true),
                (false, true) => Some(false),
                _ => None,
            }
        }
        RuleExpr::Loop(a) | RuleExpr::Maybe(a) => {
            // these constructs are fine if they do not contain a recursive affix
            match visit_affix_leaves(a, prefix, on_leaf) {
                Some(false) => Some(false),
                _ => None,
            }
        }
        RuleExpr::SeparatedList {
            element,
            separator: _,
        } => {
            if prefix {
                match visit_affix_leaves(element, prefix, on_leaf) {
                    Some(false) => Some(false),
                    _ => None,
                }
            } else {
                None
            }
        }
        RuleExpr::OneOrMore(_)
        | RuleExpr::InlineParameter(_)
        | RuleExpr::InlineCall(_)
        | RuleExpr::Not(_) => {
            unreachable!("These should have been eliminated during lowering")
        }
        RuleExpr::Commit | RuleExpr::Pratt(_) => None,
    }
}

fn lower_pratt(current_rule: RuleHandle, vec: &Vec<crate::convert::RuleDef>) -> RuleExpr {
    let handle_expr = |expr: &mut RuleExpr, prefix: bool| {
        if let RuleExpr::Transition(Transition::Rule(rule)) = expr {
            if *rule == current_rule {
                *expr = match prefix {
                    // binding power will be added later
                    true => RuleExpr::Transition(Transition::CompareBindingPower(0)),
                    false => RuleExpr::Transition(Transition::PrattRule(*rule, 0)),
                };
                return true;
            }
        }
        false
    };

    let mut atoms = Vec::new();
    let mut suffixes = Vec::new();
    let mut bp_offset = 1;
    for rule in vec {
        let mut expr = rule.expr.clone();
        let has_prefix = visit_affix_leaves(&mut expr, true, &mut |expr| handle_expr(expr, true));
        let has_suffix = visit_affix_leaves(&mut expr, false, &mut |expr| handle_expr(expr, false));

        let kind = match has_prefix {
            Some(true) => {
                if has_suffix == Some(true) {
                    let assoc = match rule.attributes.right_assoc {
                        true => Associativity::Right,
                        false => Associativity::Left,
                    };
                    PrattExprKind::Binary(assoc)
                } else {
                    PrattExprKind::Suffix
                }
            }
            Some(false) => {
                if has_suffix != Some(true) || rule.attributes.atom {
                    PrattExprKind::Atom
                } else {
                    PrattExprKind::Prefix
                }
            }
            None => {
                // TODO report error
                expr = RuleExpr::error();
                PrattExprKind::Atom
            }
        };

        let (l_bp, r_bp) = kind.get_binding_power(&mut bp_offset);

        if let Some(bp) = l_bp {
            visit_affix_leaves(&mut expr, true, &mut |expr| {
                if let RuleExpr::Transition(Transition::CompareBindingPower(power)) = expr {
                    *power = bp
                }
                true
            });
        }

        if let Some(bp) = r_bp {
            visit_affix_leaves(&mut expr, false, &mut |expr| {
                if let RuleExpr::Transition(Transition::PrattRule(_, power)) = expr {
                    *power = bp
                }
                true
            });
        }

        // expr.to_sequence().push(RuleExpr::Transition(Transition::CloseSpan(todo!())));

        let dest = match kind {
            PrattExprKind::Atom | PrattExprKind::Prefix => &mut atoms,
            PrattExprKind::Suffix | PrattExprKind::Binary(_) => &mut suffixes,
        };
        dest.push(expr);
    }
    let mangled = RuleExpr::Sequence(vec![
        RuleExpr::Choice(atoms),
        RuleExpr::Loop(Box::new(RuleExpr::Choice(suffixes))),
    ]);

    mangled
}

fn lower_expr(
    rule: RuleHandle,
    expr: &mut RuleExpr,
    inlines: &mut SecondaryVec<InlineHandle, RuleExpr>,
    cx: &mut LoweringCx,
) {
    expr.visit_nodes_bottom_up_mut(|node| match node {
        RuleExpr::Pratt(vec) => *node = lower_pratt(rule, vec),
        RuleExpr::InlineCall(call) => *node = inline_call(call, inlines, cx),
        RuleExpr::Not(expr) => {
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
        RuleExpr::OneOrMore(expr) => {
            let expr = expr.take();
            *node = RuleExpr::Sequence(vec![expr.clone(), RuleExpr::Loop(Box::new(expr))]);
        }
        _ => (),
    });
}
