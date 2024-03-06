use std::{
    borrow::Cow,
    collections::{hash_map::Entry, HashMap},
};

use gnag::{
    ast::{self, ParsedFile},
    ctx::{ConvertCtx, SpanExt},
    handle::HandleVec,
    SpannedError, StrSpan,
};

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
    pub ast: AstItemHandle,
    pub attribute: Option<TokenAttribute>,
    pub name: String,
    pub pattern: TokenPattern,
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
    pub ast_items: HandleVec<AstItemHandle, AstItem>,

    pub tokens: HandleVec<TokenHandle, TokenDef>,
    pub rules: HandleVec<RuleHandle, RuleDef>,
    pub inlines: HandleVec<InlineHandle, InlineDef>,

    pub errors: Vec<SpannedError>,
}

fn add_ast_item(
    cx: &mut ConvertCtx<'_>,

    name_span: StrSpan,
    ast_handle: AstItemHandle,
    name_to_item: &mut HashMap<String, ItemKind>,
    ast_items: &mut HandleVec<AstItemHandle, AstItem>,

    push_fn: &mut dyn FnMut() -> ItemKind,
) {
    let name = name_span.resolve_owned(cx);
    match name_to_item.entry(name) {
        Entry::Occupied(_) => cx.error(name_span, "Duplicate item definition"),
        Entry::Vacant(e) => {
            let item_handle = push_fn();
            e.insert(item_handle);
            let ast_entry = &mut ast_items[ast_handle];
            match (item_handle, ast_entry) {
                (ItemKind::Token(handle), AstItem::Token(_, a)) => *a = Some(handle),
                (ItemKind::Rule(handle), AstItem::Rule(_, a)) => *a = Some(handle),
                (ItemKind::Inline(handle), AstItem::Inline(_, a)) => *a = Some(handle),
                _ => unreachable!(),
            };
        }
    }
}

impl ConvertedFile {
    pub fn new(src: &str, file: &ParsedFile) -> ConvertedFile {
        let file_ast = ast::file(&file.root, &file.arena).unwrap();

        let mut name_to_item = HashMap::new();
        let mut ast_items = HandleVec::new();

        let mut ast_tokens = HandleVec::new();
        let mut ast_rules = HandleVec::new();
        let mut ast_inlines = HandleVec::new();

        let mut convert_cx = ConvertCtx::new(src);
        let cx = &mut convert_cx;

        for item in file_ast.items {
            match item {
                ast::Item::Tokenizer(a) => {
                    for r in a.rules {
                        let name = r.name;
                        let handle = ast_items.push(AstItem::Token(r, None));
                        add_ast_item(
                            cx,
                            name,
                            handle,
                            &mut name_to_item,
                            &mut ast_items,
                            &mut || ItemKind::Token(ast_tokens.push(handle)),
                        );
                    }
                }
                ast::Item::SynRule(r) => {
                    let name = r.name;
                    if r.inline {
                        let handle = ast_items.push(AstItem::Inline(r, None));
                        add_ast_item(
                            cx,
                            name,
                            handle,
                            &mut name_to_item,
                            &mut ast_items,
                            &mut || ItemKind::Inline(ast_inlines.push(handle)),
                        );
                    } else {
                        let handle = ast_items.push(AstItem::Rule(r, None));
                        add_ast_item(
                            cx,
                            name,
                            handle,
                            &mut name_to_item,
                            &mut ast_items,
                            &mut || ItemKind::Rule(ast_rules.push(handle)),
                        );
                    }
                }
            };
        }

        let ir_tokens = ast_tokens.map(|handle| {
            let AstItem::Token(ast, _) = &ast_items[handle] else {
                unreachable!()
            };
            convert_ast_token(cx, handle, ast)
        });
        let ir_rules = ast_rules.map(|handle| {
            let AstItem::Rule(ast, _) = &ast_items[handle] else {
                unreachable!()
            };
            convert_ast_rule(cx, handle, ast, &[], &ir_tokens, &name_to_item)
        });
        let ir_inlines = ast_inlines.map(|handle| {
            let AstItem::Inline(ast, _) = &ast_items[handle] else {
                unreachable!()
            };
            convert_ast_inline(cx, handle, ast, &ir_tokens, &name_to_item)
        });

        ConvertedFile {
            name_to_item,
            ast_items,
            tokens: ir_tokens,
            rules: ir_rules,
            inlines: ir_inlines,
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
    pub fn get_inline_ast(&self, handle: InlineHandle) -> &ast::SynRule {
        let rule = &self.inlines[handle];
        if let AstItem::Inline(ast, _) = &self.ast_items[rule.body.ast] {
            ast
        } else {
            unreachable!()
        }
    }
    pub fn find_ast_item(&self, pos: u32) -> Option<&AstItem> {
        let items = self.ast_items.as_slice();
        let index = match items.binary_search_by_key(&pos, |a| a.span().start) {
            Ok(ok) => ok,
            Err(a) => a.checked_sub(1)?,
        };
        Some(&items[index])
    }
    pub fn find_rule_token(&self, pos: u32) -> Option<TokenHandle> {
        match self.find_ast_item(pos)? {
            AstItem::Token(_, handle) => *handle,
            AstItem::Rule(_, _) => None,
            AstItem::Inline(_, _) => None,
        }
    }
    pub fn find_rule_handle(&self, pos: u32) -> Option<RuleHandle> {
        match self.find_ast_item(pos)? {
            AstItem::Token(_, _) => None,
            AstItem::Rule(_, handle) => *handle,
            AstItem::Inline(_, _) => None,
        }
    }
    pub fn find_rule_inline(&self, pos: u32) -> Option<InlineHandle> {
        match self.find_ast_item(pos)? {
            AstItem::Token(_, _) => None,
            AstItem::Rule(_, _) => None,
            AstItem::Inline(_, handle) => *handle,
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

fn convert_ast_inline(
    cx: &ConvertCtx<'_>,
    handle: AstItemHandle,
    ast: &ast::SynRule,
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
) -> InlineDef {
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
    let body = convert_ast_rule(cx, handle, ast, &parameters, ir_tokens, name_to_item);

    InlineDef { parameters, body }
}

fn convert_ast_rule(
    cx: &ConvertCtx<'_>,
    handle: AstItemHandle,
    ast: &ast::SynRule,
    parameters: &[String],
    ir_tokens: &HandleVec<TokenHandle, TokenDef>,
    name_to_item: &HashMap<String, ItemKind>,
) -> RuleDef {
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
        expr: ast.expression.as_ref().map_or(RuleExpr::Empty, |e| {
            expression(cx, e, &parameters, ir_tokens, name_to_item)
        }),
    };

    rule
}

fn convert_ast_token(cx: &ConvertCtx<'_>, handle: AstItemHandle, ast: &ast::TokenRule) -> TokenDef {
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
    pub template: InlineHandle,
    pub parameters: Vec<RuleExpr>,
    // TODO use a more consistent solution
    pub span: StrSpan,
}

#[derive(Clone, Debug)]
pub enum RuleExpr {
    Empty,
    Error,
    Token(TokenHandle),
    Rule(RuleHandle),

    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    Loop(Box<RuleExpr>),
    OneOrMore(Box<RuleExpr>),
    Maybe(Box<RuleExpr>),

    // inline rules (eliminated during lowering)
    InlineParameter(usize),
    InlineCall(Box<CallExpr>),

    // builtins
    Any,
    Commit,
    // `Not` only supports tokens, but at this point it may also contain an InlineParameter, we will check this later
    Not(Box<RuleExpr>),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },
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
    //         RuleExpr::Empty => true,
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
    //         RuleExpr::Empty => true,
    //         RuleExpr::Sequence(a) | RuleExpr::Choice(a) => a.iter().all(fun),
    //         RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Maybe(a) => fun(a),
    //         RuleExpr::Not(a) => !fun(a),
    //         RuleExpr::SeparatedList { element, separator } => fun(element) && fun(separator),
    //         RuleExpr::Token(_)
    //         | RuleExpr::Rule(_)
    //         | RuleExpr::InlineParameter(_)
    //         | RuleExpr::InlineCall(_)
    //         | RuleExpr::Any
    //         | RuleExpr::ZeroSpace
    //         | RuleExpr::Error
    //         | RuleExpr::PrattRecursion { .. } => false,
    //     }
    // }
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
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_top_down_(fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &call.parameters {
                    a.visit_nodes_top_down_(fun);
                }
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::Any
            | RuleExpr::Commit
            | RuleExpr::Empty
            | RuleExpr::Error => {}
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
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_bottom_up_(fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &call.parameters {
                    a.visit_nodes_bottom_up_(fun);
                }
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::Any
            | RuleExpr::Commit
            | RuleExpr::Empty
            | RuleExpr::Error => {}
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
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_top_down_mut_(fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &mut call.parameters {
                    a.visit_nodes_top_down_mut_(fun);
                }
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::Any
            | RuleExpr::Commit
            | RuleExpr::Empty
            | RuleExpr::Error => {}
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
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) | RuleExpr::Not(a) => {
                a.visit_nodes_bottom_up_mut_(fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &mut call.parameters {
                    a.visit_nodes_bottom_up_mut_(fun);
                }
            }
            RuleExpr::Token(_)
            | RuleExpr::Rule(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::Any
            | RuleExpr::Commit
            | RuleExpr::Empty
            | RuleExpr::Error => {}
        }
        fun(self);
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
        for _ in 0..indent {
            write!(buf, "  ");
        }
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

        match self {
            RuleExpr::Empty => writeln!(buf, "Empty"),
            RuleExpr::Error => writeln!(buf, "Error"),
            RuleExpr::Token(a) => writeln!(buf, "Token({})", a.name(file)),
            RuleExpr::Rule(a) => writeln!(buf, "Rule({})", a.name(file)),
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
            RuleExpr::Any => writeln!(buf, "Any"),
            RuleExpr::Commit => writeln!(buf, "Commit"),
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
        };
    }
    // /// Visits all leaf nodes which may be visited by the grammar while no tokens have been consumed.
    // pub fn visit_prefix_leaves(&self, mut fun: impl FnMut(&RuleExpr) -> bool) {
    //     self.visit_prefix_leaves_(&mut fun);
    // }
    // pub fn visit_prefix_leaves_(&self, fun: &mut dyn FnMut(&RuleExpr) -> bool) -> bool {
    //     match self {
    //         RuleExpr::Sequence(a) => {
    //             if let Some(first) = a.first() {
    //                 if first.visit_prefix_leaves_(fun) {
    //                     return true;
    //                 }
    //             }
    //             false
    //         }
    //         RuleExpr::Choice(a) => {
    //             for e in a {
    //                 if e.visit_prefix_leaves_(fun) {
    //                     return true;
    //                 }
    //             }
    //             false
    //         }
    //         RuleExpr::Loop(a)
    //         | RuleExpr::OneOrMore(a)
    //         | RuleExpr::Maybe(a)
    //         | RuleExpr::SeparatedList { element: a, .. } => a.visit_prefix_leaves_(fun),
    //         RuleExpr::Token(_)
    //         | RuleExpr::Rule(_)
    //         | RuleExpr::InlineParameter(_)
    //         | RuleExpr::InlineCall(_)
    //         | RuleExpr::Any
    //         | RuleExpr::Not(_)
    //         | RuleExpr::ZeroSpace
    //         | RuleExpr::Empty
    //         | RuleExpr::Error
    //         | RuleExpr::PrattRecursion { .. } => fun(self),
    //     }
    // }
    // pub fn get_sequence_slice(&self) -> &[RuleExpr] {
    //     match self {
    //         Self::Sequence(a) => a.as_slice(),
    //         _ => std::array::from_ref(self),
    //     }
    // }
    // pub fn get_choice_slice(&self) -> &[RuleExpr] {
    //     match self {
    //         Self::Choice(a) => a.as_slice(),
    //         _ => std::array::from_ref(self),
    //     }
    // }
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
                    Some(ItemKind::Inline(_)) => {
                        cx.error(*a, "Use <> syntax for inlines");
                        RuleExpr::Error
                    }
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
        ast::Expression::Paren(a) => match &a.expr {
            Some(e) => expression(cx, e, parameters, tokens, name_to_item),
            None => RuleExpr::Empty,
        },
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

            let mut expect_count = |c: usize, ok: &dyn Fn(&mut Vec<RuleExpr>) -> RuleExpr| {
                if arguments.len() != c {
                    cx.error(a.span, format_args!("expected {c} arguments"));
                    RuleExpr::Error
                } else {
                    ok(&mut arguments)
                }
            };

            match name {
                "any" => expect_count(0, &|_| RuleExpr::Any),
                "commit" => expect_count(0, &|_| RuleExpr::Commit),
                "not" => expect_count(1, &|args| RuleExpr::Not(Box::new(args.pop().unwrap()))),
                "separated_list" => expect_count(2, &|args| RuleExpr::SeparatedList {
                    separator: Box::new(args.pop().unwrap()),
                    element: Box::new(args.pop().unwrap()),
                }),
                _ => match name_to_item.get(name) {
                    Some(ItemKind::Inline(rule)) => RuleExpr::InlineCall(Box::new(CallExpr {
                        template: *rule,
                        parameters: arguments,
                        span: a.span,
                    })),
                    Some(_) => {
                        cx.error(a.name, "Expected inline");
                        RuleExpr::Error
                    }
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
                ast::PostExprKind::Star => RuleExpr::Loop(inner),
                ast::PostExprKind::Plus => RuleExpr::OneOrMore(inner),
            }
        }
        ast::Expression::BinExpr(_) => {
            let mut vec = Vec::new();
            binary_expression(cx, expr, parameters, tokens, name_to_item, &mut vec);
            RuleExpr::Choice(vec)
        }
        ast::Expression::SeqExpr(seq) => {
            let vec = seq
                .exprs
                .iter()
                .map(|e| expression(cx, e, parameters, tokens, name_to_item))
                .collect();
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
        ast::Expression::BinExpr(a) => {
            binary_expression(cx, &a.left, parameters, tokens, name_to_item, vec);
            binary_expression(cx, &a.right, parameters, tokens, name_to_item, vec);
        }
        _ => {
            vec.push(expression(cx, expr, parameters, tokens, name_to_item));
        }
    }
}
