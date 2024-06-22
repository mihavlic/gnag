use std::{
    borrow::{Borrow, Cow},
    collections::{hash_map::Entry, HashMap},
};

use gnag::{
    ast::{self, ParsedFile, SynRule, TokenRule},
    ctx::{ErrorAccumulator, SpanExt},
    handle::HandleVec,
    StrSpan,
};

use crate::expr::{CallExpr, RuleExpr, Transition};

gnag::simple_handle! {
    pub TokenHandle,
    pub RuleHandle,
    pub InlineHandle,
    pub AstItemHandle
}

impl TokenHandle {
    pub fn name(self, file: &ConvertedFile) -> &str {
        file.tokens[self].name.as_str()
    }
}

impl RuleHandle {
    pub fn name(self, file: &ConvertedFile) -> &str {
        file.rules[self].name.as_str()
    }
}

impl InlineHandle {
    pub fn name(self, file: &ConvertedFile) -> &str {
        file.inlines[self].body.name.as_str()
    }
}

pub enum AstItem {
    Token(ast::TokenRule, Option<TokenHandle>),
    Rule(ast::SynRule, Option<RuleHandle>),
    Inline(ast::SynRule, Option<InlineHandle>),
}

impl AstItem {
    pub fn name(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.name,
            AstItem::Rule(a, _) => a.name,
            AstItem::Inline(a, _) => a.name,
        }
    }
    pub fn span(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.span,
            AstItem::Rule(a, _) => a.span,
            AstItem::Inline(a, _) => a.span,
        }
    }
}

#[derive(Debug)]
pub enum TokenPattern {
    Regex(String),
    SimpleString(String),
    RustCode(String),
    Invalid,
}

#[derive(Debug)]
pub enum TokenAttribute {
    Skip(StrSpan),
    ErrorToken(StrSpan),
}

#[derive(Debug)]
pub struct TokenDef {
    pub span: StrSpan,
    pub attribute: Option<TokenAttribute>,
    pub name: String,
    pub pattern_span: StrSpan,
    pub pattern: TokenPattern,
}

#[derive(Debug, Default, Clone)]
pub struct RuleAttributes {
    pub root: bool,
    pub atom: bool,
    pub left_assoc: bool,
    pub right_assoc: bool,
}

#[derive(Debug, Clone)]
pub struct RuleDef {
    pub span: StrSpan,
    pub attributes: RuleAttributes,
    pub name: String,
    pub expr: RuleExpr,
}

#[derive(Debug)]
pub struct InlineDef {
    pub parameters: Vec<String>,
    pub body: RuleDef,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Token(TokenHandle),
    Rule(RuleHandle),
    Inline(InlineHandle),
}

#[derive(Default)]
pub struct ConvertedFile {
    pub name_to_item: HashMap<String, ItemKind>,

    pub tokens: HandleVec<TokenHandle, TokenDef>,
    pub rules: HandleVec<RuleHandle, RuleDef>,
    pub inlines: HandleVec<InlineHandle, InlineDef>,
}

impl ConvertedFile {
    pub fn new(src: &str, err: &ErrorAccumulator, file: &ParsedFile) -> ConvertedFile {
        let file_ast = ast::file(&file.root, &file.arena).unwrap();

        let mut cx = ConvertCx::new(src, err);
        // find all visible rules and tokens for name resolution during true conversion
        cx.scan_ast(&file_ast);

        let tokens = cx.ast_tokens.map_ref(|handle| convert_token(&cx, handle));

        let mut rules = cx.ast_rules.map_fill(RuleDef {
            span: StrSpan::empty(),
            attributes: Default::default(),
            name: Default::default(),
            expr: RuleExpr::empty(),
        });

        for (handle, ast) in cx.ast_rules.iter_kv() {
            rules[handle] = convert_rule(&cx, ast, &[], &tokens, &mut rules);
        }

        let inlines = cx
            .ast_inlines
            .map_ref(|handle| convert_inline_rule(&cx, handle, &tokens, &mut rules));

        ConvertedFile {
            name_to_item: std::mem::take(&mut cx.name_to_item),
            tokens,
            rules,
            inlines,
        }
    }
    pub fn get_token_name(&self, handle: TokenHandle) -> &str {
        &self.tokens[handle].name
    }
    pub fn get_rule_name(&self, handle: RuleHandle) -> &str {
        &self.rules[handle].name
    }
    pub fn get_inline_name(&self, handle: InlineHandle) -> &str {
        &self.inlines[handle].body.name
    }
}

struct ConvertCx<'a, 'b, 'c> {
    src: &'a str,
    err: &'b ErrorAccumulator,
    name_to_item: HashMap<String, ItemKind>,
    ast_tokens: HandleVec<TokenHandle, &'c TokenRule>,
    ast_rules: HandleVec<RuleHandle, &'c SynRule>,
    ast_inlines: HandleVec<InlineHandle, &'c SynRule>,
}

impl<'a, 'b, 'c> Borrow<str> for ConvertCx<'a, 'b, 'c> {
    fn borrow(&self) -> &str {
        self.src
    }
}

impl<'a, 'b, 'c> ConvertCx<'a, 'b, 'c> {
    fn new(src: &'a str, err: &'b ErrorAccumulator) -> Self {
        Self {
            src,
            err,
            name_to_item: Default::default(),
            ast_tokens: Default::default(),
            ast_rules: Default::default(),
            ast_inlines: Default::default(),
        }
    }
    fn insert_ast(&mut self, name: StrSpan, handle: ItemKind) {
        let owned_name = name.resolve_owned(self);
        match self.name_to_item.entry(owned_name) {
            Entry::Occupied(_) => self.error(name, "Duplicate item definition"),
            Entry::Vacant(v) => _ = v.insert(handle),
        }
    }
    fn scan_ast(&mut self, ast: &'c ast::File) {
        for item in &ast.items {
            match item {
                ast::Item::Tokens(a) => {
                    for r in &a.rules {
                        let handle = ItemKind::Token(self.ast_tokens.push(r));
                        self.insert_ast(r.name, handle);
                    }
                }
                ast::Item::Rules(a) => {
                    for r in &a.rules {
                        let handle = match r.inline {
                            true => ItemKind::Inline(self.ast_inlines.push(r)),
                            false => ItemKind::Rule(self.ast_rules.push(r)),
                        };
                        self.insert_ast(r.name, handle);
                    }
                }
            };
        }
    }

    fn error(&self, span: StrSpan, error: impl ToString) {
        self.err.error(span, error.to_string());
    }
}

fn convert_inline_rule(
    cx: &ConvertCx,
    ast: &ast::SynRule,
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    rules: &mut HandleVec<RuleHandle, RuleDef>,
) -> InlineDef {
    let parameters = ast
        .paramaters
        .as_ref()
        .map(|p| p.params.as_slice())
        .unwrap_or_default()
        .iter()
        .map(|parameter| {
            let name = parameter.resolve_owned(cx);
            if cx.name_to_item.contains_key(&name) {
                cx.error(*parameter, "Parameter shadows symbol");
            }
            name
        })
        .collect::<Vec<_>>();

    let body = convert_rule(cx, ast, &parameters, ir_tokens, rules);

    InlineDef { parameters, body }
}

fn convert_rule(
    cx: &ConvertCx,
    ast: &ast::SynRule,
    parameters: &[String],
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    rules: &mut HandleVec<RuleHandle, RuleDef>,
) -> RuleDef {
    let mut attributes = RuleAttributes::default();
    for attr in &ast.attributes {
        match attr.name.resolve(cx) {
            "root" => attributes.root = true,
            "left" => attributes.left_assoc = true,
            "right" => attributes.right_assoc = true,
            "atom" => attributes.atom = true,
            _ => cx.error(attr.name, "Unknown attribute"),
        }
    }

    let rule = RuleDef {
        span: ast.span,
        attributes,
        name: ast.name.resolve_owned(cx),
        expr: ast.expression.as_ref().map_or(RuleExpr::empty(), |e| {
            convert_expression(cx, e, &parameters, ir_tokens, rules)
        }),
    };

    rule
}

fn convert_token(cx: &ConvertCx, ast: &ast::TokenRule) -> TokenDef {
    let extracted = ast::extract_str_literal(ast.pattern.resolve(cx));

    let pattern = if let Some((str, is_regex)) = extracted {
        let string = Cow::into_owned(str);
        match is_regex {
            true => TokenPattern::Regex(string),
            false => TokenPattern::SimpleString(string),
        }
    } else {
        cx.error(ast.pattern, "Invalid token pattern");
        TokenPattern::Invalid
    };

    let mut attribute = None;
    for attr in &ast.attributes {
        let name = attr.name;
        match name.resolve(cx) {
            "skip" => attribute = Some(TokenAttribute::Skip(name)),
            "error" => attribute = Some(TokenAttribute::ErrorToken(name)),
            _ => cx.error(name, "Unknown attribute"),
        }
    }

    TokenDef {
        span: ast.span,
        attribute,
        name: ast.name.resolve_owned(cx),
        pattern_span: ast.pattern,
        pattern,
    }
}

fn convert_expression(
    cx: &ConvertCx,
    expr: &ast::Expression,
    parameters: &[String],
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    rules: &mut HandleVec<RuleHandle, RuleDef>,
) -> RuleExpr {
    match expr {
        ast::Expression::Ident(a) => {
            let name = (*a).resolve(cx);
            if let Some(pos) = parameters.iter().position(|a| a == name) {
                RuleExpr::InlineParameter(pos)
            } else {
                match cx.name_to_item.get(name) {
                    Some(ItemKind::Token(t)) => RuleExpr::token(*t),
                    Some(ItemKind::Rule(r)) => RuleExpr::rule(*r),
                    Some(ItemKind::Inline(_)) => {
                        cx.error(*a, "Use <> syntax for inlines");
                        RuleExpr::error()
                    }
                    None => {
                        cx.error(*a, "Unknown item");
                        RuleExpr::error()
                    }
                }
            }
        }
        ast::Expression::Literal(a) => {
            let value = ast::extract_str_literal(a.resolve(cx)).map(|(s, _)| s);
            if let Some(value) = value {
                let token = ir_tokens.iter_kv().find(|(_, v)| match &v.pattern {
                    TokenPattern::SimpleString(pattern) => pattern == &value,
                    _ => false,
                });
                if let Some((handle, _)) = token {
                    RuleExpr::token(handle)
                } else {
                    cx.error(*a, "No matching token");
                    RuleExpr::error()
                }
            } else {
                cx.error(*a, "Invalid string");
                RuleExpr::error()
            }
        }
        ast::Expression::PrattExpr(vec) => {
            let handles = vec
                .exprs
                .iter()
                .map(|r| {
                    if r.inline {
                        cx.error(r.span, "Rules inside a pratt expression cannot be inline");
                    }
                    let body = convert_rule(cx, r, &[], ir_tokens, rules);
                    rules.push(body)
                })
                .collect();
            RuleExpr::Pratt(handles)
        }
        ast::Expression::Paren(a) => match &a.expr {
            Some(e) => convert_expression(cx, e, parameters, ir_tokens, rules),
            None => RuleExpr::empty(),
        },
        ast::Expression::CallExpr(a) => {
            let expression = a
                .args
                .as_ref()
                .map(|e| convert_expression(cx, e, parameters, ir_tokens, rules));

            let name = a.name.resolve(cx);

            let mut arguments = match expression {
                Some(RuleExpr::Sequence(seq)) => seq,
                Some(a) => vec![a],
                _ => vec![],
            };

            let mut expect_count = |c: usize, ok: &dyn Fn(&mut Vec<RuleExpr>) -> RuleExpr| {
                if arguments.len() != c {
                    cx.error(a.span, format_args!("expected {c} arguments"));
                    RuleExpr::error()
                } else {
                    ok(&mut arguments)
                }
            };

            match name {
                "any" => expect_count(0, &|_| RuleExpr::Transition(Transition::Any)),
                "commit" => expect_count(0, &|_| RuleExpr::Commit),
                "not" => expect_count(1, &|args| RuleExpr::Not(Box::new(args.pop().unwrap()))),
                "separated_list" => expect_count(2, &|args| RuleExpr::SeparatedList {
                    separator: Box::new(args.pop().unwrap()),
                    element: Box::new(args.pop().unwrap()),
                }),
                _ => match cx.name_to_item.get(name) {
                    Some(ItemKind::Inline(rule)) => RuleExpr::InlineCall(Box::new(CallExpr {
                        template: *rule,
                        parameters: arguments,
                        span: a.span,
                    })),
                    Some(_) => {
                        cx.error(a.name, "Expected inline");
                        RuleExpr::error()
                    }
                    None => {
                        cx.error(a.name, "Unknown item");
                        RuleExpr::error()
                    }
                },
            }
        }
        ast::Expression::PostExpr(a) => {
            let inner = Box::new(convert_expression(
                cx, &a.expr, parameters, ir_tokens, rules,
            ));
            match a.kind {
                ast::PostExprKind::Question => RuleExpr::Maybe(inner),
                ast::PostExprKind::Star => RuleExpr::Loop(inner),
                ast::PostExprKind::Plus => RuleExpr::OneOrMore(inner),
            }
        }
        ast::Expression::BinExpr(_) => {
            let mut vec = Vec::new();
            binary_expression(cx, expr, parameters, ir_tokens, &mut vec, rules);
            RuleExpr::Choice(vec)
        }
        ast::Expression::SeqExpr(seq) => {
            let vec = seq
                .exprs
                .iter()
                .map(|e| convert_expression(cx, e, parameters, ir_tokens, rules))
                .collect();
            RuleExpr::Sequence(vec)
        }
    }
}

fn binary_expression(
    cx: &ConvertCx,
    expr: &ast::Expression,
    parameters: &[String],
    tokens: &HandleVec<TokenHandle, TokenDef>,
    vec: &mut Vec<RuleExpr>,
    rules: &mut HandleVec<RuleHandle, RuleDef>,
) {
    match expr {
        ast::Expression::BinExpr(a) => {
            binary_expression(cx, &a.left, parameters, tokens, vec, rules);
            binary_expression(cx, &a.right, parameters, tokens, vec, rules);
        }
        _ => {
            vec.push(convert_expression(cx, expr, parameters, tokens, rules));
        }
    }
}
