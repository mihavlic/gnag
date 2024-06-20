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

use crate::graph::Transition;

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
    // fn convert(&mut self, src: &str, err: &ErrorAccumulator, file: &ParsedFile) {}
    pub fn new(src: &str, err: &ErrorAccumulator, file: &ParsedFile) -> ConvertedFile {
        let file_ast = ast::file(&file.root, &file.arena).unwrap();

        let mut cx = ConvertCx::new(src, err);
        cx.scan_ast(&file_ast);

        let ir_tokens = cx.ast_tokens.map_ref(|handle| convert_token(&cx, handle));
        let ir_rules = cx
            .ast_rules
            .map_ref(|handle| convert_rule(&cx, handle, &[], &ir_tokens));
        let ir_inlines = cx
            .ast_inlines
            .map_ref(|handle| convert_inline_rule(&cx, handle, &ir_tokens));

        ConvertedFile {
            name_to_item: std::mem::take(&mut cx.name_to_item),
            tokens: ir_tokens,
            rules: ir_rules,
            inlines: ir_inlines,
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

    let body = convert_rule(cx, ast, &parameters, ir_tokens);

    InlineDef { parameters, body }
}

fn convert_rule(
    cx: &ConvertCx,
    ast: &ast::SynRule,
    parameters: &[String],
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
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
            convert_expression(cx, e, &parameters, ir_tokens)
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

#[derive(Clone, Debug)]
pub struct CallExpr {
    pub template: InlineHandle,
    pub parameters: Vec<RuleExpr>,
    // TODO use a more consistent solution
    pub span: StrSpan,
}

#[derive(Clone, Debug)]
pub enum RuleExpr {
    Transition(Transition),

    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    Loop(Box<RuleExpr>),
    OneOrMore(Box<RuleExpr>),
    Maybe(Box<RuleExpr>),

    Commit,

    // inline rules (eliminated during lowering)
    InlineParameter(usize),
    InlineCall(Box<CallExpr>),

    // `Not` only supports tokens, but at this point it may also contain an InlineParameter, we will check this later
    Not(Box<RuleExpr>),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },

    // pratt
    Pratt(Vec<RuleDef>),
}

impl RuleExpr {
    pub const BUILTIN_RULES: &'static [&'static str] = &["any", "not", "separated_list"];
    // pub fn is_sequence(&self) -> bool {
    //     matches!(self, Self::Sequence(_))
    // }
    // pub fn is_choice(&self) -> bool {
    //     matches!(self, Self::Choice(_))
    // }
    // /// A helper function for [`Self::is_empty_nonrecursive()`] which only considers the current
    // /// node without traversing into its childern.
    // fn is_empty_leaf(&self) -> bool {
    //     match self {
    //         RuleExpr::empty() => true,
    //         RuleExpr::Sequence(a) | RuleExpr::Choice(a) => a.is_empty(),
    //         _ => false,
    //     }
    // }
    // /// A version of [`Self::is_empty()`] which only considers its direct children, useful when
    // /// doing a [`Self::visit_nodes_bottom_up()`] to avoid quadratic complexity.
    // pub fn is_empty_nonrecursive(&self) -> bool {
    //     self.is_empty_impl(Self::is_empty_leaf)
    // }
    // pub fn is_empty(&self) -> bool {
    //     self.is_empty_impl(Self::is_empty)
    // }
    // fn is_empty_impl<F: Fn(&Self) -> bool>(&self, fun: F) -> bool {
    //     match self {
    //         RuleExpr::empty() => true,
    //         RuleExpr::Sequence(a) | RuleExpr::Choice(a) => a.iter().all(fun),
    //         RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Maybe(a) => fun(a),
    //         RuleExpr::Not(a) => !fun(a),
    //         RuleExpr::SeparatedList { element, separator } => fun(element) && fun(separator),
    //         RuleExpr::token(_)
    //         | RuleExpr::rule(_)
    //         | RuleExpr::InlineParameter(_)
    //         | RuleExpr::InlineCall(_)
    //         | RuleExpr::Any
    //         | RuleExpr::ZeroSpace
    //         | RuleExpr::error()
    //         | RuleExpr::PrattRecursion { .. } => false,
    //     }
    // }
    pub fn empty() -> RuleExpr {
        RuleExpr::Sequence(vec![])
    }
    pub fn error() -> RuleExpr {
        RuleExpr::Transition(Transition::Error)
    }
    pub fn token(handle: TokenHandle) -> RuleExpr {
        RuleExpr::Transition(Transition::Token(handle))
    }
    pub fn rule(handle: RuleHandle) -> RuleExpr {
        RuleExpr::Transition(Transition::Rule(handle))
    }
    pub fn visit_nodes_top_down(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_(true, &mut fun)
    }
    pub fn visit_nodes_bottom_up(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_(false, &mut fun)
    }
    pub fn visit_nodes_top_down_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_mut_(true, &mut fun)
    }
    pub fn visit_nodes_bottom_up_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_mut_(false, &mut fun)
    }

    fn visit_nodes_(&self, top_down: bool, fun: &mut dyn FnMut(&RuleExpr)) {
        if top_down {
            fun(self);
        }
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_(top_down, fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_(top_down, fun);
                separator.visit_nodes_(top_down, fun);
            }
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_(top_down, fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &call.parameters {
                    a.visit_nodes_(top_down, fun);
                }
            }
            RuleExpr::Pratt(rules) => {
                for a in rules {
                    a.expr.visit_nodes_(top_down, fun);
                }
            }
            RuleExpr::Transition(_) | RuleExpr::InlineParameter(_) | RuleExpr::Commit => {}
        }
        if !top_down {
            fun(self);
        }
    }
    fn visit_nodes_mut_(&mut self, top_down: bool, fun: &mut dyn FnMut(&mut RuleExpr)) {
        if top_down {
            fun(self);
        }
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_mut_(top_down, fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_mut_(top_down, fun);
                separator.visit_nodes_mut_(top_down, fun);
            }
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_mut_(top_down, fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &mut call.parameters {
                    a.visit_nodes_mut_(top_down, fun);
                }
            }
            RuleExpr::Pratt(rules) => {
                for a in rules {
                    a.expr.visit_nodes_mut_(top_down, fun);
                }
            }
            RuleExpr::Transition(_) | RuleExpr::InlineParameter(_) | RuleExpr::Commit => {}
        }
        if !top_down {
            fun(self);
        }
    }
    pub fn display(&self, buf: &mut dyn std::fmt::Write, file: &ConvertedFile) {
        self.display_with_indent(buf, 0, file);
    }
    #[allow(unused_must_use)]
    pub fn display_with_indent(
        &self,
        buf: &mut dyn std::fmt::Write,
        indent: u32,
        file: &ConvertedFile,
    ) {
        let print_indent = |buf: &mut dyn std::fmt::Write| {
            for _ in 0..indent {
                write!(buf, "  ");
            }
        };

        let display_slice = |buf: &mut dyn std::fmt::Write, name: &str, exprs: &[RuleExpr]| {
            writeln!(buf, "{name}");
            for expr in exprs {
                expr.display_with_indent(buf, indent + 1, file);
            }
            Ok(())
        };
        let display_nested = |buf: &mut dyn std::fmt::Write, name: &str, expr: &RuleExpr| {
            writeln!(buf, "{name}");
            expr.display_with_indent(buf, indent + 1, file);
            Ok(())
        };

        print_indent(buf);
        match self {
            RuleExpr::Transition(transition) => transition.display(buf, file),
            RuleExpr::Commit => write!(buf, "Commit"),
            RuleExpr::Sequence(a) => display_slice(buf, "Sequence", a),
            RuleExpr::Choice(a) => display_slice(buf, "Choice", a),
            RuleExpr::Loop(a) => display_nested(buf, "Loop", a),
            RuleExpr::OneOrMore(a) => display_nested(buf, "OneOrMore", a),
            RuleExpr::Maybe(a) => display_nested(buf, "Maybe", a),
            RuleExpr::InlineParameter(a) => writeln!(buf, "InlineParameter({a})"),
            RuleExpr::InlineCall(a) => {
                write!(buf, "InlineCall {}", a.template.name(file));
                display_slice(buf, "", &a.parameters)
            }
            RuleExpr::Not(a) => display_nested(buf, "Not", a),
            RuleExpr::SeparatedList { element, separator } => {
                writeln!(buf, "SeparatedList");
                element.display_with_indent(buf, indent + 1, file);
                for _ in 0..=indent {
                    write!(buf, "  ");
                }
                writeln!(buf, "---");
                separator.display_with_indent(buf, indent + 1, file);
                Ok(())
            }
            RuleExpr::Pratt(rules) => {
                writeln!(buf, "pratt");

                for rule in rules {
                    print_indent(buf);
                    display_nested(buf, &rule.name, &rule.expr);
                }

                Ok(())
            }
        };
    }
}

fn convert_expression(
    cx: &ConvertCx,
    expr: &ast::Expression,
    parameters: &[String],
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
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
        ast::Expression::PrattExpr(rules) => {
            let rules = rules
                .exprs
                .iter()
                .map(|r| {
                    if r.inline {
                        cx.error(r.span, "Rules inside a pratt expression cannot be inline");
                    }
                    convert_rule(cx, r, &[], ir_tokens)
                })
                .collect();
            RuleExpr::Pratt(rules)
        }
        ast::Expression::Paren(a) => match &a.expr {
            Some(e) => convert_expression(cx, e, parameters, ir_tokens),
            None => RuleExpr::empty(),
        },
        ast::Expression::CallExpr(a) => {
            let expression = a
                .args
                .as_ref()
                .map(|e| convert_expression(cx, e, parameters, ir_tokens));

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
            let inner = Box::new(convert_expression(cx, &a.expr, parameters, ir_tokens));
            match a.kind {
                ast::PostExprKind::Question => RuleExpr::Maybe(inner),
                ast::PostExprKind::Star => RuleExpr::Loop(inner),
                ast::PostExprKind::Plus => RuleExpr::OneOrMore(inner),
            }
        }
        ast::Expression::BinExpr(_) => {
            let mut vec = Vec::new();
            binary_expression(cx, expr, parameters, ir_tokens, &mut vec);
            RuleExpr::Choice(vec)
        }
        ast::Expression::SeqExpr(seq) => {
            let vec = seq
                .exprs
                .iter()
                .map(|e| convert_expression(cx, e, parameters, ir_tokens))
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
) {
    match expr {
        ast::Expression::BinExpr(a) => {
            binary_expression(cx, &a.left, parameters, tokens, vec);
            binary_expression(cx, &a.right, parameters, tokens, vec);
        }
        _ => {
            vec.push(convert_expression(cx, expr, parameters, tokens));
        }
    }
}
