use std::{
    borrow::Cow,
    cell::{self, RefCell},
    collections::{hash_map::Entry, HashMap},
};

use crate::{
    ast as a,
    file::{
        self as f, AstItem, AstItemHandle, RuleDef, RuleExpr, RuleHandle, TokenDef, TokenHandle,
    },
    handle::HandleVec,
    ParseError, StrSpan,
};

pub struct ConvertCtx<'a> {
    pub src: &'a str,
    errors: RefCell<Vec<ParseError>>,
}

impl<'a> ConvertCtx<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            errors: RefCell::new(Vec::new()),
        }
    }
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.errors.borrow_mut().push(ParseError {
            span,
            err: err.to_string(),
        })
    }
    pub fn get_errors(&self) -> cell::Ref<'_, Vec<ParseError>> {
        self.errors.borrow()
    }
}

pub trait SpanExt {
    fn resolve<'a>(self, cx: &'a ConvertCtx) -> &'a str;
    fn resolve_owned(self, cx: &ConvertCtx) -> String;
}

impl SpanExt for StrSpan {
    fn resolve<'a>(self, cx: &'a ConvertCtx) -> &'a str {
        self.as_str(cx.src)
    }

    fn resolve_owned(self, cx: &ConvertCtx) -> String {
        self.as_str(cx.src).to_owned()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ItemKind {
    Token(TokenHandle),
    Rule(RuleHandle),
}

pub fn file(cx: &ConvertCtx, file: a::File) -> f::File {
    let mut name_to_item = HashMap::new();

    let mut ast_items = HandleVec::new();
    let mut ast_tokens = HandleVec::new();
    let mut ast_rules = HandleVec::new();

    for item in file.items {
        match item {
            a::Item::Tokenizer(a) => {
                for r in a.rules {
                    let name_span = r.name;
                    let name = name_span.resolve_owned(cx);
                    let handle: AstItemHandle = ast_items.push(AstItem::Token(r, None));
                    match name_to_item.entry(name) {
                        Entry::Occupied(_) => cx.error(name_span, "Duplicate item definition"),
                        Entry::Vacant(o) => {
                            let ir_handle = ast_tokens.push(handle);
                            o.insert(ItemKind::Token(ir_handle));
                            match &mut ast_items[handle] {
                                AstItem::Token(_, ir) => *ir = Some(ir_handle),
                                _ => unreachable!(),
                            };
                        }
                    }
                }
            }
            a::Item::SynRule(r) => {
                let name_span = r.name;
                let name = name_span.resolve_owned(cx);
                let handle: AstItemHandle = ast_items.push(AstItem::Rule(r, None));
                match name_to_item.entry(name) {
                    Entry::Occupied(_) => cx.error(name_span, "Duplicate item definition"),
                    Entry::Vacant(o) => {
                        let ir_handle = ast_rules.push(handle);
                        o.insert(ItemKind::Rule(ir_handle));
                        match &mut ast_items[handle] {
                            AstItem::Rule(_, ir) => *ir = Some(ir_handle),
                            _ => unreachable!(),
                        };
                    }
                }
            }
        };
    }

    let ir_tokens = ast_tokens.map_ref(|r| {
        let AstItem::Token(r, _) = &ast_items[*r] else {
            unreachable!()
        };

        let pattern = a::unescape_str_literal(r.value.resolve(cx));
        if pattern.is_none() {
            cx.error(r.value, "Invalid string");
        }

        TokenDef {
            attrs: attributes(cx, &r.attributes),
            name: r.name.resolve_owned(cx),
            pattern: pattern.map(Cow::into_owned).unwrap_or(String::new()),
        }
    });

    let ir_rules = ast_rules.map_ref(|r| {
        let AstItem::Rule(r, _) = &ast_items[*r] else {
            unreachable!()
        };

        let rule = RuleDef {
            attrs: attributes(cx, &r.attributes),
            name: r.name.resolve_owned(cx),
            inline: r.inline,
            arguments: r
                .paramaters
                .as_ref()
                .map_or(Vec::new(), |p| params(cx, &p.params)),
            expr: expression(cx, &r.expression, &ir_tokens, &name_to_item),
        };
        if !rule.arguments.is_empty() && !rule.inline {
            cx.error(r.span, "Templated rules must be inline");
        }
        rule
    });

    f::File {
        ast_items,
        ast_tokens,
        ast_rules,
        ir_tokens,
        ir_rules,
    }
}

pub fn attributes(cx: &ConvertCtx, attrs: &[a::Attribute]) -> Vec<f::Attribute> {
    attrs
        .iter()
        .map(|a| f::Attribute {
            name: a.name.resolve_owned(cx),
        })
        .collect()
}

pub fn params(cx: &ConvertCtx, attrs: &[StrSpan]) -> Vec<String> {
    attrs.iter().map(|a| a.resolve_owned(cx)).collect()
}

fn expression(
    cx: &ConvertCtx,
    expr: &a::Expression,
    tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
) -> f::RuleExpr {
    match expr {
        a::Expression::Ident(a) => {
            let name = a.resolve(cx);
            match name_to_item.get(name) {
                Some(ItemKind::Token(t)) => f::RuleExpr::Token(*t),
                Some(ItemKind::Rule(r)) => f::RuleExpr::Rule(*r),
                None => {
                    cx.error(*a, "Unknown item");
                    f::RuleExpr::Error
                }
            }
        }
        a::Expression::Literal(a) => {
            let value = a::unescape_str_literal(a.resolve(cx));
            if let Some(value) = value {
                let token = tokens.iter_kv().find(|(_, v)| v.pattern == value);
                if let Some((handle, _)) = token {
                    f::RuleExpr::Token(handle)
                } else {
                    cx.error(*a, "No matching token");
                    f::RuleExpr::Error
                }
            } else {
                cx.error(*a, "Invalid string");
                f::RuleExpr::Error
            }
        }
        a::Expression::Paren(a) => return expression(cx, &a.expr, tokens, name_to_item),
        a::Expression::PreExpr(a) => {
            _ = expression(cx, &a.expr, tokens, name_to_item);
            cx.error(a.span, "TODO Expression attributes");
            f::RuleExpr::Error
        }
        a::Expression::CallExpr(a) => {
            let name = a.name.resolve(cx);
            let expression = a
                .args
                .as_ref()
                .map(|e| expression(cx, e, tokens, name_to_item));
            let mut args = match expression {
                Some(f::RuleExpr::Sequence(seq)) => seq,
                Some(a) => vec![a],
                _ => vec![],
            };

            let mut expect_count = |c: usize, ok: fn(&mut Vec<RuleExpr>) -> f::RuleExpr| {
                if args.len() != c {
                    cx.error(a.span, format_args!("expected {c} arguments"));
                    f::RuleExpr::Error
                } else {
                    ok(&mut args)
                }
            };

            match name {
                "any" => expect_count(0, |_| f::RuleExpr::Any),
                "not" => expect_count(1, |args| f::RuleExpr::Not(Box::new(args.pop().unwrap()))),
                "separated_list" => expect_count(2, |args| f::RuleExpr::SeparatedList {
                    separator: Box::new(args.pop().unwrap()),
                    element: Box::new(args.pop().unwrap()),
                }),
                "zero_space" => expect_count(0, |_| f::RuleExpr::ZeroSpace),
                _ => match name_to_item.get(name) {
                    Some(ItemKind::Token(_)) => {
                        cx.error(a.span, "Found token name");
                        f::RuleExpr::Error
                    }
                    Some(ItemKind::Rule(_)) => {
                        cx.error(a.span, "TODO Arbitrary rule calls");
                        f::RuleExpr::Error
                    }
                    None => {
                        cx.error(a.span, "Unknown item");
                        f::RuleExpr::Error
                    }
                },
            }
        }
        a::Expression::PostName(a) => {
            cx.error(a.span, "TODO postfix name");
            f::RuleExpr::Error
        }
        a::Expression::PostExpr(a) => {
            let inner = Box::new(expression(cx, &a.expr, tokens, name_to_item));
            match a.kind {
                a::PostExprKind::Question => f::RuleExpr::Maybe(inner),
                a::PostExprKind::Star => f::RuleExpr::ZeroOrMore(inner),
                a::PostExprKind::Plus => f::RuleExpr::OneOrMore(inner),
            }
        }
        a::Expression::BinExpr(a) => {
            let left = expression(cx, &a.left, tokens, name_to_item);
            let right = expression(cx, &a.right, tokens, name_to_item);
            f::RuleExpr::Choice(vec![left, right])
        }
        a::Expression::SeqExpr(a) => {
            let exprs = a
                .exprs
                .iter()
                .map(|e| expression(cx, e, tokens, name_to_item))
                .collect();
            f::RuleExpr::Sequence(exprs)
        }
    }
    // attrs.iter().map(|a| a::read_maybe_escaped_string(src, *a).into_owned()).collect()
}
