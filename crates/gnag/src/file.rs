use std::{
    borrow::Cow,
    collections::{hash_map::Entry, HashMap},
};

use crate::{
    ast::{self, ParsedFile},
    ctx::{ConvertCtx, SpanExt},
    handle::HandleVec,
    SpannedError, StrSpan,
};

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

// #[derive(Debug)]
// pub struct Attribute {
//     pub name: String,
// }

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
    pub ast: AstItemHandle,
    pub attribute: Option<TokenAttribute>,
    pub name: String,
    pub pattern: TokenPattern,
}

#[derive(Debug)]
pub enum LoweredTokenAttribute {
    Skip(StrSpan),
    ErrorToken(StrSpan),
}

#[derive(Debug, Default)]
pub struct RuleAttributes {
    pub root: bool,
    pub pratt: bool,
    pub left_assoc: bool,
    pub right_assoc: bool,
}

#[derive(Debug)]
pub struct RuleDef {
    pub ast: AstItemHandle,
    pub attributes: RuleAttributes,
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

#[derive(Default)]
pub struct ConvertedFile {
    pub name_to_item: HashMap<String, ItemKind>,
    pub ast_items: HandleVec<AstItemHandle, AstItem>,

    pub tokens: HandleVec<TokenHandle, TokenDef>,
    pub rules: HandleVec<RuleHandle, RuleDef>,

    pub errors: Vec<SpannedError>,
}

impl ConvertedFile {
    pub fn new(src: &str, file: &ParsedFile) -> ConvertedFile {
        let file_ast = ast::file(&file.root, &file.arena).unwrap();

        let mut name_to_item = HashMap::new();
        let mut ast_items = HandleVec::new();
        let mut ast_tokens = HandleVec::new();
        let mut ast_rules = HandleVec::new();

        let mut convert_cx = ConvertCtx::new(src);
        let cx = &mut convert_cx;

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

        ConvertedFile {
            name_to_item,
            ast_items,
            tokens: ir_tokens,
            rules: ir_rules,
            errors: convert_cx.finish(),
        }
    }
    pub fn get_token_ast(&self, handle: TokenHandle) -> &ast::TokenRule {
        let token = &self.tokens[handle];
        if let AstItem::Token(ast, _) = &self.ast_items[token.ast] {
            ast
        } else {
            unreachable!()
        }
    }
    pub fn get_rule_ast(&self, handle: RuleHandle) -> &ast::SynRule {
        let rule = &self.rules[handle];
        if let AstItem::Rule(ast, _) = &self.ast_items[rule.ast] {
            ast
        } else {
            unreachable!()
        }
    }
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

    let mut attributes = RuleAttributes::default();
    for attr in &ast.attributes {
        match attr.name.resolve(cx) {
            "root" => attributes.root = true,
            "pratt" => attributes.pratt = true,
            "left" => attributes.left_assoc = true,
            "right" => attributes.right_assoc = true,
            _ => cx.error(attr.name, "Unknown attribute"),
        }
    }

    let rule = RuleDef {
        ast: handle,
        attributes,
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
    let pattern = match ast.pattern {
        ast::TokenValue::String(span) => {
            if let Some((str, is_raw)) = ast::extract_str_literal(span.resolve(cx)) {
                let string = Cow::into_owned(str);
                match is_raw {
                    true => TokenPattern::Regex(string),
                    false => TokenPattern::SimpleString(string),
                }
            } else {
                cx.error(span, "Invalid token pattern");
                TokenPattern::Invalid
            }
        }
        ast::TokenValue::RustCode(span) => TokenPattern::RustCode(span.resolve(cx).to_owned()),
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
        ast: handle,
        attribute,
        name: ast.name.resolve_owned(cx),
        pattern,
    }
}

#[derive(Clone, Debug)]
pub struct CallExpr {
    pub rule: RuleHandle,
    pub parameters: Vec<RuleExpr>,
    // TODO use a more consistent solution
    pub span: StrSpan,
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
    // inline rules (eliminated during lowering)
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
    // compilation annotated pratt recursion (used to differentiate normal recursion from pratt during left recursion checking)
    PrattRecursion {
        pratt: RuleHandle,
        binding_power: u32,
    },
    // compiled pratt rule
    // PrattSequence(Vec<PrattExpr>),
}

impl RuleExpr {
    pub const BUILTIN_RULES: &[&'static str] = &["any", "not", "separated_list", "zero_space"];
    pub fn is_sequence(&self) -> bool {
        matches!(self, Self::Sequence(_))
    }
    pub fn is_choice(&self) -> bool {
        matches!(self, Self::Choice(_))
    }
    /// A helper function for [`Self::is_empty_nonrecursive()`] which only considers the current
    /// node without traversing into its childern.
    fn is_empty_leaf(&self) -> bool {
        match self {
            RuleExpr::Empty => true,
            RuleExpr::Sequence(a) | RuleExpr::Choice(a) => a.is_empty(),
            _ => false,
        }
    }
    /// A version of [`Self::is_empty()`] which only considers its direct children, useful when
    /// doing a [`Self::visit_nodes_bottom_up()`] to avoid quadratic complexity.
    pub fn is_empty_nonrecursive(&self) -> bool {
        self.is_empty_impl(Self::is_empty_leaf)
    }
    pub fn is_empty(&self) -> bool {
        self.is_empty_impl(Self::is_empty)
    }
    fn is_empty_impl<F: Fn(&Self) -> bool>(&self, fun: F) -> bool {
        match self {
            RuleExpr::Empty => true,
            RuleExpr::Sequence(a) | RuleExpr::Choice(a) => a.iter().all(fun),
            RuleExpr::ZeroOrMore(a) | RuleExpr::OneOrMore(a) | RuleExpr::Maybe(a) => fun(a),
            RuleExpr::Not(a) => !fun(a),
            RuleExpr::SeparatedList { element, separator } => fun(element) && fun(separator),
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::ZeroSpace
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => false,
        }
    }
    pub fn visit_nodes_top_down(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_top_down_(&mut fun)
    }
    fn visit_nodes_top_down_(&self, fun: &mut dyn FnMut(&RuleExpr)) {
        fun(self);
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_top_down_(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_top_down_(fun);
                separator.visit_nodes_top_down_(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_top_down_(fun);
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::ZeroSpace
            | RuleExpr::Empty
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => {}
        }
    }
    pub fn visit_nodes_bottom_up(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_bottom_up_(&mut fun)
    }
    fn visit_nodes_bottom_up_(&self, fun: &mut dyn FnMut(&RuleExpr)) {
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_bottom_up_(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_bottom_up_(fun);
                separator.visit_nodes_bottom_up_(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_bottom_up_(fun);
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::ZeroSpace
            | RuleExpr::Empty
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => {}
        }
        fun(self);
    }
    pub fn visit_nodes_top_down_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_top_down_mut_(&mut fun)
    }
    fn visit_nodes_top_down_mut_(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        fun(self);
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_top_down_mut_(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_top_down_mut_(fun);
                separator.visit_nodes_top_down_mut_(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_top_down_mut_(fun);
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::ZeroSpace
            | RuleExpr::Empty
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => {}
        }
    }
    pub fn visit_nodes_bottom_up_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_bottom_up_mut_(&mut fun)
    }
    fn visit_nodes_bottom_up_mut_(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_bottom_up_mut_(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_bottom_up_mut_(fun);
                separator.visit_nodes_bottom_up_mut_(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_bottom_up_mut_(fun);
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::ZeroSpace
            | RuleExpr::Empty
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => {}
        }
        fun(self);
    }
    /// Visits all leaf nodes which may be visited by the grammar while no tokens have been consumed.
    pub fn visit_prefix_leaves(&self, mut fun: impl FnMut(&RuleExpr) -> bool) {
        self.visit_prefix_leaves_(&mut fun);
    }
    pub fn visit_prefix_leaves_(&self, fun: &mut dyn FnMut(&RuleExpr) -> bool) -> bool {
        match self {
            RuleExpr::Sequence(a) => {
                if let Some(first) = a.first() {
                    if first.visit_prefix_leaves_(fun) {
                        return true;
                    }
                }
                false
            }
            RuleExpr::Choice(a) => {
                for e in a {
                    if e.visit_prefix_leaves_(fun) {
                        return true;
                    }
                }
                false
            }
            RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::SeparatedList { element: a, .. } => a.visit_prefix_leaves_(fun),
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::Any
            | RuleExpr::Not(_)
            | RuleExpr::ZeroSpace
            | RuleExpr::Empty
            | RuleExpr::Error
            | RuleExpr::PrattRecursion { .. } => fun(self),
        }
    }
    pub fn get_sequence_slice(&self) -> &[RuleExpr] {
        match self {
            Self::Sequence(a) => a.as_slice(),
            _ => std::array::from_ref(self),
        }
    }
    pub fn get_choice_slice(&self) -> &[RuleExpr] {
        match self {
            Self::Choice(a) => a.as_slice(),
            _ => std::array::from_ref(self),
        }
    }
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
            let value = ast::extract_str_literal(a.resolve(cx)).map(|(s, _)| s);
            if let Some(value) = value {
                let token = tokens.iter_kv().find(|(_, v)| match &v.pattern {
                    TokenPattern::SimpleString(pattern) => pattern == &value,
                    _ => false,
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
            let expression = a
                .args
                .as_ref()
                .map(|e| expression(cx, e, parameters, tokens, name_to_item));

            let name = a.name.resolve(cx);

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
                        parameters: arguments,
                        span: a.span,
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
