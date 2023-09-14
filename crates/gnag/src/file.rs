use std::{
    borrow::{Borrow, Cow},
    cell::RefCell,
    collections::{hash_map::Entry, HashMap, HashSet},
};

use crate::{ast, handle::HandleVec, lex, Lexer, Node, ParseError, StrSpan};

crate::simple_handle! {
    pub TokenHandle,
    pub RuleHandle,
    pub AstItemHandle
}

pub enum AstItem {
    Token(ast::TokenRule, Option<TokenHandle>),
    Rule(ast::SynRule, Option<RuleHandle>),
}

impl AstItem {
    pub fn name(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.name,
            AstItem::Rule(a, _) => a.name,
        }
    }
    pub fn span(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.span,
            AstItem::Rule(a, _) => a.span,
        }
    }
}

#[derive(Debug)]
pub struct Attribute {
    pub name: String,
}

pub enum TokenPattern {
    Regex(String),
    RustCode(String),
}

pub struct TokenDef {
    pub ast: AstItemHandle,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub pattern: TokenPattern,
}

#[derive(Debug)]
pub struct RuleDef {
    pub ast: AstItemHandle,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub inline: bool,
    pub parameters: Vec<String>,
    pub expr: RuleExpr,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Token(TokenHandle),
    Rule(RuleHandle),
}

pub struct ConvertCtx<'a> {
    pub src: &'a str,
    pub errors: RefCell<Vec<ParseError>>,
}

impl<'a> ConvertCtx<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            errors: Default::default(),
        }
    }
}

pub trait SpanExt {
    fn resolve<'a, S: Borrow<str> + 'a>(self, cx: &'a S) -> &'a str;
    fn resolve_owned<S: Borrow<str>>(self, cx: &S) -> String;
}

impl SpanExt for StrSpan {
    fn resolve<'a, S: Borrow<str> + 'a>(self, cx: &'a S) -> &'a str {
        self.as_str(cx.borrow())
    }

    fn resolve_owned<S: Borrow<str>>(self, cx: &S) -> String {
        self.as_str(cx.borrow()).to_owned()
    }
}

impl ConvertCtx<'_> {
    fn error(&self, span: StrSpan, message: impl ToString) {
        self.errors.borrow_mut().push(ParseError {
            span,
            err: message.to_string(),
        })
    }
}

impl Borrow<str> for ConvertCtx<'_> {
    fn borrow(&self) -> &str {
        self.src
    }
}

#[derive(Default)]
pub struct File {
    pub name_to_item: HashMap<String, ItemKind>,
    pub ast_items: HandleVec<AstItemHandle, AstItem>,

    pub ir_tokens: HandleVec<TokenHandle, TokenDef>,
    pub ir_rules: HandleVec<RuleHandle, RuleDef>,
}

impl File {
    pub fn new_from_string(src: &str) -> (Self, Vec<ParseError>, Vec<Node>, Node) {
        let mut lexer = Lexer::new(src.as_bytes());

        let (tokens, trivia) = lex(&mut lexer);
        let mut parser = crate::Parser::new(src, tokens, trivia);
        _ = crate::file(&mut parser);

        let mut arena = Vec::new();
        let root = parser.build_tree(&mut arena);

        let cx = ConvertCtx::new(src);
        let file = File::from_ast(&cx, &root, &arena);
        (file, RefCell::into_inner(cx.errors), arena, root)
    }
    pub fn from_ast(cx: &ConvertCtx, cst: &Node, arena: &[Node]) -> File {
        let file_ast = ast::file(&cst, &arena).unwrap();

        let mut name_to_item = HashMap::new();
        let mut ast_items = HandleVec::new();
        let mut ast_tokens = HandleVec::new();
        let mut ast_rules = HandleVec::new();

        for item in file_ast.items {
            match item {
                ast::Item::Tokenizer(a) => {
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
                ast::Item::SynRule(r) => {
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

        let ir_tokens = ast_tokens.map(|handle| {
            let AstItem::Token(ast, _) = &ast_items[handle] else {
                unreachable!()
            };
            token_ast_to_ir(cx, handle, ast)
        });

        let ir_rules = ast_rules.map(|handle| {
            let AstItem::Rule(ast, _) = &ast_items[handle] else {
                unreachable!()
            };
            ast_token_to_ir(cx, handle, ast, &ir_tokens, &name_to_item)
        });

        File {
            name_to_item,
            ast_items,
            ir_tokens,
            ir_rules,
        }
    }
    // fn process_inlines(&mut self) {
    //     let mut partial_rules = Vec::new();
    //     let mut finished_rules = HashSet::new();
    //     for r in self.ir_rules.iter_keys() {
    //         self.rule_apply_inlines(r, &mut partial_rules, &mut finished_rules);
    //     }
    // }
    // fn rule_process_body(
    //     &mut self,
    //     rule_handle: RuleHandle,
    //     partial_rules: &mut Vec<RuleHandle>,
    //     finished_rules: &mut HashSet<RuleHandle>,
    // ) {
    //     let rule = &self.ir_rules[rule_handle];
    //     if finished_rules.contains(&rule_handle) {
    //         return &rule;
    //     }

    //     if rule.inline {
    //         let conflict = partial_rules.contains(&rule_handle);
    //         partial_rules.push(rule_handle);

    //         if conflict {
    //             let names = partial_rules
    //                 .iter()
    //                 .flat_map(|handle| {
    //                     let name = &self.ir_rules[*handle].name;
    //                     [name, " "]
    //                 })
    //                 .collect::<String>();

    //             panic!("{} rule is recursively inlined:\n{}", rule.name, names);
    //         }

    //         let mut take = std::mem::replace(&mut self.ir_rules[rule_handle].expr, RuleExpr::Error);
    //         take.visit_nodes_top_down(&mut |node| {
    //             if let RuleExpr::Rule(handle) = node {
    //                 if self.ir_rules[*handle].inline {
    //                     self.rule_apply_inlines(*handle, partial_rules, finished_rules);
    //                     *node = self.ir_rules[*handle].expr.clone();
    //                 }
    //             }
    //         });
    //         take.finalize();
    //         _ = std::mem::replace(&mut self.ir_rules[rule_handle].expr, take);

    //         assert_eq!(partial_rules.pop(), Some(rule_handle));
    //     }

    //     finished_rules.insert(rule_handle);
    // }
}

fn ast_token_to_ir(
    cx: &ConvertCtx<'_>,
    handle: AstItemHandle,
    ast: &ast::SynRule,
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
) -> RuleDef {
    let parameters = ast
        .paramaters
        .as_ref()
        .map(|p| {
            p.params
                .iter()
                .map(|parameter| {
                    let name = parameter.resolve_owned(cx);
                    if name_to_item.contains_key(&name) {
                        cx.error(*parameter, "Parameter shadows symbol");
                    }
                    name
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();

    let rule = RuleDef {
        ast: handle,
        attrs: attributes(cx, &ast.attributes),
        name: ast.name.resolve_owned(cx),
        inline: ast.inline,
        expr: ast.expression.as_ref().map_or(RuleExpr::Empty, |e| {
            expression(cx, e, &parameters, ir_tokens, name_to_item)
        }),
        parameters,
    };

    if !rule.parameters.is_empty() && !rule.inline {
        cx.error(
            ast.paramaters.as_ref().unwrap().span,
            "Templated rules must be inline",
        );
    }

    rule
}

fn token_ast_to_ir(cx: &ConvertCtx<'_>, handle: AstItemHandle, ast: &ast::TokenRule) -> TokenDef {
    let pattern = match ast.value {
        ast::TokenValue::Regex(s) => ast::unescape_str_literal(s.resolve(cx))
            .map(Cow::into_owned)
            .map(TokenPattern::Regex),
        ast::TokenValue::Arbitrary(s) => Some(TokenPattern::RustCode(s.resolve(cx).to_owned())),
    };

    if pattern.is_none() {
        let span = match ast.value {
            ast::TokenValue::Regex(s) => s,
            ast::TokenValue::Arbitrary(s) => s,
        };
        cx.error(span, "Invalid token pattern");
    }

    TokenDef {
        ast: handle,
        attrs: attributes(cx, &ast.attributes),
        name: ast.name.resolve_owned(cx),
        pattern: pattern.unwrap_or(TokenPattern::Regex(String::new())),
    }
}

#[derive(Clone, Debug)]
pub struct CallExpr {
    rule: RuleHandle,
    arguments: Vec<RuleExpr>,
}

#[derive(Clone, Debug)]
pub enum RuleExpr {
    // base nodes
    Token(TokenHandle),
    Rule(RuleHandle),
    // structuring nodes
    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    // repetition
    ZeroOrMore(Box<RuleExpr>),
    OneOrMore(Box<RuleExpr>),
    Maybe(Box<RuleExpr>),
    // inline rules
    InlineParameter(usize),
    InlineCall(Box<CallExpr>),
    // builtins
    Any,
    Not(Box<RuleExpr>),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },
    ZeroSpace,
    Empty,
    Error,
}

impl RuleExpr {
    pub const BUILTIN_RULES: &[&'static str] = &["any", "not", "separated_list", "zero_space"];
    pub fn is_sequence(&self) -> bool {
        matches!(self, Self::Sequence(_))
    }
    pub fn is_choice(&self) -> bool {
        matches!(self, Self::Choice(_))
    }
    pub fn visit_nodes_top_down(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        fun(self);
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_top_down(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_top_down(fun);
                separator.visit_nodes_top_down(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_top_down(fun);
            }
            _ => {}
        }
    }
    pub fn visit_nodes_bottom_up(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_bottom_up(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_bottom_up(fun);
                separator.visit_nodes_bottom_up(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_bottom_up(fun);
            }
            _ => {}
        }
        fun(self);
    }
    pub fn finalize(&mut self) {
        self.visit_nodes_bottom_up(&mut |node| match node {
            RuleExpr::Sequence(seq) => {
                let mut i = 0;
                while i < seq.len() {
                    match &mut seq[i] {
                        RuleExpr::Sequence(a) => {
                            let drain = std::mem::take(a);
                            seq.splice(i..=i, drain);
                        }
                        RuleExpr::Empty => {
                            seq.remove(i);
                        }
                        _ => i += 1,
                    }
                }
                if seq.is_empty() {
                    *node = RuleExpr::Empty;
                }
            }
            RuleExpr::Choice(seq) => {
                let mut i = 0;
                while i < seq.len() {
                    match &mut seq[i] {
                        RuleExpr::Choice(a) => {
                            let drain = std::mem::take(a);
                            seq.splice(i..=i, drain);
                        }
                        RuleExpr::Empty => {
                            seq.remove(i);
                        }
                        _ => i += 1,
                    }
                }
                if seq.is_empty() {
                    *node = RuleExpr::Empty;
                }
            }
            _ => {}
        });
    }
}

pub fn attributes(cx: &ConvertCtx, attrs: &[ast::Attribute]) -> Vec<Attribute> {
    attrs
        .iter()
        .map(|a| Attribute {
            name: a.name.resolve_owned(cx),
        })
        .collect()
}

fn expression(
    cx: &ConvertCtx,
    expr: &ast::Expression,
    parameters: &[String],
    tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
) -> RuleExpr {
    match expr {
        ast::Expression::Ident(a) => {
            let name = (*a).resolve(cx);
            if let Some(pos) = parameters.iter().position(|a| a == name) {
                RuleExpr::InlineParameter(pos)
            } else {
                match name_to_item.get(name) {
                    Some(ItemKind::Token(t)) => RuleExpr::Token(*t),
                    Some(ItemKind::Rule(r)) => RuleExpr::Rule(*r),
                    None => {
                        cx.error(*a, "Unknown item");
                        RuleExpr::Error
                    }
                }
            }
        }
        ast::Expression::Literal(a) => {
            let value = ast::unescape_str_literal(a.resolve(cx));
            if let Some(value) = value {
                let token = tokens.iter_kv().find(|(_, v)| match &v.pattern {
                    TokenPattern::Regex(pattern) => pattern == &*value,
                    TokenPattern::RustCode(_) => false,
                });
                if let Some((handle, _)) = token {
                    RuleExpr::Token(handle)
                } else {
                    cx.error(*a, "No matching token");
                    RuleExpr::Error
                }
            } else {
                cx.error(*a, "Invalid string");
                RuleExpr::Error
            }
        }
        ast::Expression::Paren(a) => {
            return expression(cx, &a.expr, parameters, tokens, name_to_item)
        }
        ast::Expression::PreExpr(a) => {
            _ = expression(cx, &a.expr, parameters, tokens, name_to_item);
            cx.error(a.span, "TODO Expression attributes");
            RuleExpr::Error
        }
        ast::Expression::CallExpr(a) => {
            let name = a.name.resolve(cx);
            let expression = a
                .args
                .as_ref()
                .map(|e| expression(cx, e, parameters, tokens, name_to_item));
            let mut arguments = match expression {
                Some(RuleExpr::Sequence(seq)) => seq,
                Some(a) => vec![a],
                _ => vec![],
            };

            let mut expect_count = |c: usize, ok: fn(&mut Vec<RuleExpr>) -> RuleExpr| {
                if arguments.len() != c {
                    cx.error(a.span, format_args!("expected {c} arguments"));
                    RuleExpr::Error
                } else {
                    ok(&mut arguments)
                }
            };

            match name {
                "any" => expect_count(0, |_| RuleExpr::Any),
                "not" => expect_count(1, |args| RuleExpr::Not(Box::new(args.pop().unwrap()))),
                "separated_list" => expect_count(2, |args| RuleExpr::SeparatedList {
                    separator: Box::new(args.pop().unwrap()),
                    element: Box::new(args.pop().unwrap()),
                }),
                "zero_space" => expect_count(0, |_| RuleExpr::ZeroSpace),
                _ => match name_to_item.get(name) {
                    Some(ItemKind::Token(_)) => {
                        cx.error(a.name, "Expected rule");
                        RuleExpr::Error
                    }
                    Some(ItemKind::Rule(rule)) => RuleExpr::InlineCall(Box::new(CallExpr {
                        rule: *rule,
                        arguments,
                    })),
                    None => {
                        cx.error(a.name, "Unknown item");
                        RuleExpr::Error
                    }
                },
            }
        }
        ast::Expression::PostName(a) => {
            cx.error(a.span, "TODO postfix name");
            RuleExpr::Error
        }
        ast::Expression::PostExpr(a) => {
            let inner = Box::new(expression(cx, &a.expr, parameters, tokens, name_to_item));
            match a.kind {
                ast::PostExprKind::Question => RuleExpr::Maybe(inner),
                ast::PostExprKind::Star => RuleExpr::ZeroOrMore(inner),
                ast::PostExprKind::Plus => RuleExpr::OneOrMore(inner),
            }
        }
        ast::Expression::BinExpr(_) => {
            let mut vec = Vec::new();
            binary_expression(cx, expr, parameters, tokens, name_to_item, &mut vec);
            RuleExpr::Choice(vec)
        }
        ast::Expression::SeqExpr(_) => {
            let mut vec = Vec::new();
            seq_expression(cx, expr, parameters, tokens, name_to_item, &mut vec);
            RuleExpr::Sequence(vec)
        }
    }
}

fn binary_expression(
    cx: &ConvertCtx,
    expr: &ast::Expression,
    parameters: &[String],
    tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
    vec: &mut Vec<RuleExpr>,
) {
    match expr {
        ast::Expression::Paren(a) => {
            binary_expression(cx, &a.expr, parameters, tokens, name_to_item, vec);
        }
        ast::Expression::BinExpr(a) => {
            binary_expression(cx, &a.left, parameters, tokens, name_to_item, vec);
            binary_expression(cx, &a.right, parameters, tokens, name_to_item, vec);
        }
        _ => {
            vec.push(expression(cx, expr, parameters, tokens, name_to_item));
        }
    }
}

fn seq_expression(
    cx: &ConvertCtx,
    expr: &ast::Expression,
    parameters: &[String],
    tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
    vec: &mut Vec<RuleExpr>,
) {
    match expr {
        ast::Expression::Paren(a) => {
            seq_expression(cx, &a.expr, parameters, tokens, name_to_item, vec);
        }
        ast::Expression::SeqExpr(a) => {
            for expr in &a.exprs {
                seq_expression(cx, expr, parameters, tokens, name_to_item, vec);
            }
        }
        _ => {
            vec.push(expression(cx, expr, parameters, tokens, name_to_item));
        }
    }
}
