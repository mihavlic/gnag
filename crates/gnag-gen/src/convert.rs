use std::borrow::Borrow;

use gnag::{
    ast::{self, ParsedFile, RuleKind, SynRule},
    ctx::{ErrorAccumulator, SpanExt},
    handle::HandleVec,
    StrSpan,
};

use crate::expr::{CallExpr, RuleExpr, Transition};

gnag::simple_handle! {
    pub RuleHandle,
    pub InlineHandle
}

impl RuleHandle {
    pub fn name(self, file: &ConvertedFile) -> &str {
        file.rules[self].body.name.as_str()
    }
    pub fn span(self, file: &ConvertedFile) -> StrSpan {
        file.rules[self].body.name_span
    }
}

impl InlineHandle {
    pub fn name(self, file: &ConvertedFile) -> &str {
        file.inlines[self].body.name.as_str()
    }
    pub fn span(self, file: &ConvertedFile) -> StrSpan {
        file.inlines[self].body.name_span
    }
}

#[derive(Debug, Default, Clone)]
pub struct RuleAttributes {
    pub root: bool,
    pub atom: bool,
    pub left_assoc: bool,
    pub right_assoc: bool,
    pub skip: bool,
    pub word: bool,
    pub keyword: bool,
}

#[derive(Debug, Clone)]
pub struct RuleBody {
    pub span: StrSpan,
    pub attributes: RuleAttributes,
    pub name: String,
    pub name_span: StrSpan,
    pub expr: RuleExpr,
}

#[derive(Debug)]
pub struct RuleDef {
    pub kind: RuleKind,
    pub body: RuleBody,
}

#[derive(Debug)]
pub struct InlineDef {
    pub parameters: Vec<String>,
    pub body: RuleBody,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Rule(RuleHandle),
    Inline(InlineHandle),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HandleKind {
    Token,
    Rule,
    Inline,
}

impl HandleKind {
    pub fn name(self) -> &'static str {
        match self {
            HandleKind::Token => "token",
            HandleKind::Rule => "rule",
            HandleKind::Inline => "inline",
        }
    }
}

#[derive(Default)]
pub struct ConvertedFile {
    pub rules: HandleVec<RuleHandle, RuleDef>,
    pub inlines: HandleVec<InlineHandle, InlineDef>,
    pub lexer: Option<RuleHandle>,
}

impl ConvertedFile {
    pub fn new(src: &str, err: &ErrorAccumulator, file: &ParsedFile) -> ConvertedFile {
        let mut this = ConvertedFile::default();

        let Some(ast) = ast::file(&file.root, &file.arena) else {
            return this;
        };

        let cx = ConvertCx::new(src, err);

        this.convert_file(&cx, &ast);
        if let Some(lexer) = this.create_lexer_expr(&cx) {
            let def = RuleDef {
                kind: RuleKind::Tokens,
                body: RuleBody {
                    span: StrSpan::empty(),
                    attributes: RuleAttributes::default(),
                    name: "Lexer".into(),
                    name_span: StrSpan::empty(),
                    expr: lexer,
                },
            };
            let handle = this.rules.push(def);
            this.lexer = Some(handle);
        }

        this
    }

    fn convert_file(&mut self, cx: &ConvertCx, ast: &ast::File) {
        for block in &ast.items {
            match block.kind {
                ast::RuleKind::Tokens => {
                    for rule in &block.rules {
                        self.add_rule(cx, rule, RuleKind::Tokens);
                    }
                }
                ast::RuleKind::Rules => {
                    for rule in &block.rules {
                        if rule.inline {
                            self.add_inline(cx, rule);
                        } else {
                            self.add_rule(cx, rule, RuleKind::Rules);
                        }
                    }
                }
            }
        }
    }

    fn check_no_parameters(&self, cx: &ConvertCx, ast: &ast::SynRule) {
        if ast.paramaters.is_some() {
            cx.error(ast.name, "Non-inline rules cannot have parameters");
        }
    }

    fn add_rule(&mut self, cx: &ConvertCx, rule: &SynRule, kind: RuleKind) -> RuleHandle {
        self.check_no_parameters(cx, rule);
        let body = self.convert_rule(cx, rule, &[]);
        self.rules.push(RuleDef { kind, body })
    }

    fn add_inline(&mut self, cx: &ConvertCx, rule: &SynRule) -> InlineHandle {
        let body = self.convert_inline_rule_body(cx, rule);
        self.inlines.push(body)
    }

    fn convert_inline_rule_body(&mut self, cx: &ConvertCx, ast: &ast::SynRule) -> InlineDef {
        let parameters = ast
            .paramaters
            .as_ref()
            .map(|p| p.params.as_slice())
            .unwrap_or_default()
            .iter()
            .map(|parameter| parameter.resolve_owned(cx))
            .collect::<Vec<_>>();

        let body = self.convert_rule(cx, ast, &parameters);

        InlineDef { parameters, body }
    }

    fn convert_rule(
        &mut self,
        cx: &ConvertCx,
        ast: &ast::SynRule,
        parameters: &[String],
    ) -> RuleBody {
        let mut attributes = RuleAttributes::default();
        for attr in &ast.attributes {
            match attr.name.resolve(cx) {
                "root" => attributes.root = true,
                "left" => attributes.left_assoc = true,
                "right" => attributes.right_assoc = true,
                "atom" => attributes.atom = true,
                "skip" => attributes.skip = true,
                "word" => attributes.word = true,
                "keyword" => attributes.keyword = true,
                _ => cx.error(attr.name, "Unknown attribute"),
            }
        }

        let expr = ast.expression.as_ref().map_or(RuleExpr::empty(), |e| {
            self.convert_expression(cx, e, parameters)
        });

        RuleBody {
            span: ast.span,
            attributes,
            name: ast.name.resolve_owned(cx),
            name_span: ast.name,
            expr,
        }
    }

    fn convert_expression(
        &mut self,
        cx: &ConvertCx,
        expr: &ast::Expression,
        parameters: &[String],
    ) -> RuleExpr {
        match expr {
            ast::Expression::Ident(a) => {
                let name = a.resolve(cx);
                if let Some(index) = parameters.iter().position(|p| p == name) {
                    RuleExpr::InlineParameter(index)
                } else {
                    RuleExpr::UnresolvedIdentifier {
                        name: name.into(),
                        name_span: *a,
                    }
                }
            }
            ast::Expression::Literal(a) => {
                let value = ast::extract_str_literal(a.resolve(cx)).map(|(s, _)| s);
                if let Some(value) = value {
                    RuleExpr::bytes(value.as_bytes())
                } else {
                    cx.error(*a, "Invalid string");
                    RuleExpr::error()
                }
            }
            ast::Expression::PrattExpr(vec) => {
                let handles = vec
                    .exprs
                    .iter()
                    .map(|rule| self.add_rule(cx, rule, RuleKind::Rules))
                    .collect();
                RuleExpr::Pratt(handles)
            }
            ast::Expression::Paren(a) => match &a.expr {
                Some(e) => self.convert_expression(cx, e, parameters),
                None => RuleExpr::empty(),
            },
            ast::Expression::CallExpr(a) => {
                let expression = a
                    .args
                    .as_ref()
                    .map(|e| self.convert_expression(cx, e, parameters));

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
                    _ => RuleExpr::InlineCall(Box::new(CallExpr {
                        name: name.to_owned(),
                        name_span: a.name,
                        parameters: arguments,
                        span: a.span,
                    })),
                }
            }
            ast::Expression::PostExpr(a) => {
                let inner = Box::new(self.convert_expression(cx, &a.expr, parameters));
                match a.kind {
                    ast::PostExprKind::Question => RuleExpr::Maybe(inner),
                    ast::PostExprKind::Star => RuleExpr::Loop(inner),
                    ast::PostExprKind::Plus => RuleExpr::OneOrMore(inner),
                }
            }
            ast::Expression::BinExpr(_) => {
                let mut vec = Vec::new();
                self.binary_expression(cx, expr, parameters, &mut vec);
                RuleExpr::Choice(vec)
            }
            ast::Expression::SeqExpr(seq) => {
                let vec = seq
                    .exprs
                    .iter()
                    .map(|e| self.convert_expression(cx, e, parameters))
                    .collect();
                RuleExpr::Sequence(vec)
            }
        }
    }

    fn create_lexer_expr(&self, cx: &ConvertCx) -> Option<RuleExpr> {
        let mut has_word_token = false;
        let mut keyword_tokens = Vec::new();
        for (handle, rule) in self.rules.iter_kv() {
            let span = handle.span(self);
            let is_word = rule.body.attributes.word;
            let is_keyword = rule.body.attributes.keyword;

            if is_word {
                if is_keyword {
                    cx.error(span, "Token cannot be both @word and @keyword");
                }
                if has_word_token {
                    cx.error(span, "Only one @word token may exist");
                }
                has_word_token = true;
            }

            if is_keyword {
                let body = &self.rules[handle].body.expr;
                let bytes = match body {
                    RuleExpr::Transition(Transition::Bytes(b)) => Some(b.clone()),
                    _ => None,
                };

                if bytes.is_none() {
                    cx.error(
                        span,
                        "(TODO span) @keyword tokens must only be a string literal",
                    );
                }

                keyword_tokens.push((handle, bytes));
            }
        }

        let mut token_exprs = Vec::new();
        for (handle, rule) in self.rules.iter_kv() {
            let span = handle.span(self);
            let is_word = rule.body.attributes.word;
            let is_keyword = rule.body.attributes.keyword;

            if rule.kind == RuleKind::Tokens {
                if is_keyword && !has_word_token {
                    cx.error(span, "Missing @keyword token");
                }

                if is_keyword && has_word_token {
                    // keyword token gets parsed as a subset of the word token
                }
                if is_word {
                    let mut close_spans = Vec::with_capacity(keyword_tokens.len() + 1);
                    for (handle, bytes) in &keyword_tokens {
                        if let Some(bytes) = bytes {
                            close_spans.push(RuleExpr::Sequence(vec![
                                RuleExpr::keyword(bytes.clone()),
                                RuleExpr::close_span(*handle),
                            ]));
                        }
                    }
                    close_spans.push(RuleExpr::close_span(handle));

                    token_exprs.push(RuleExpr::Sequence(vec![
                        RuleExpr::rule(handle),
                        RuleExpr::Choice(close_spans),
                    ]));
                } else {
                    token_exprs.push(RuleExpr::Sequence(vec![
                        RuleExpr::rule(handle),
                        RuleExpr::close_span(handle),
                    ]));
                }
            } else {
                if is_keyword {
                    cx.error(span, "@keyword must be a token");
                }
                if is_word {
                    cx.error(span, "@word must be a token");
                }
            }
        }

        if token_exprs.is_empty() {
            return None;
        }

        Some(RuleExpr::Choice(token_exprs))
    }

    fn binary_expression(
        &mut self,
        cx: &ConvertCx,
        expr: &ast::Expression,
        parameters: &[String],
        vec: &mut Vec<RuleExpr>,
    ) {
        match expr {
            ast::Expression::BinExpr(a) => {
                self.binary_expression(cx, &a.left, parameters, vec);
                self.binary_expression(cx, &a.right, parameters, vec);
            }
            _ => {
                vec.push(self.convert_expression(cx, expr, parameters));
            }
        }
    }
}

struct ConvertCx<'a, 'b> {
    src: &'a str,
    err: &'b ErrorAccumulator,
}

impl<'a, 'b> Borrow<str> for ConvertCx<'a, 'b> {
    fn borrow(&self) -> &str {
        self.src
    }
}

impl<'a, 'b> ConvertCx<'a, 'b> {
    fn new(src: &'a str, err: &'b ErrorAccumulator) -> Self {
        Self { src, err }
    }

    fn error(&self, span: StrSpan, error: impl ToString) {
        self.err.error(span, error.to_string());
    }
}
