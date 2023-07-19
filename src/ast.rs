#![allow(unused)]

use crate::{handle::HandleVec, simple_handle, Child, StrSpan, TokenKind, Tree, TreeKind};

simple_handle! {
    pub TokenHandle,
    pub RuleHandle,
    pub TokenizerHandle,
    pub TokenRuleHandle,
    pub SynRuleHandle
}

enum RuleExpr {
    // base nodes
    Terminal(TokenHandle),
    Rule(RuleHandle),
    // structuring nodes
    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    // repetition
    ZeroOrMore(Vec<RuleExpr>),
    OneOrMore(Vec<RuleExpr>),
    Maybe(Vec<RuleExpr>),
    // builtins
    Any,
    Not(TokenHandle),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },
    ZeroSpace,
}

#[derive(Debug)]
pub enum Item {
    Tokenizer(Tokenizer),
    SynRule(SynRule),
}

#[derive(Debug)]
pub struct File {
    span: StrSpan,
    items: Vec<Item>,
}

pub fn file(tree: &Tree) -> Option<File> {
    assert_eq!(tree.kind, TreeKind::File);

    let mut items = Vec::new();

    for c in &tree.children {
        match c {
            Child::Tree(
                tree @ Tree {
                    kind,
                    span,
                    children,
                },
            ) => match kind {
                TreeKind::Tokenizer => items.extend(tokenizer(tree).map(Item::Tokenizer)),
                TreeKind::SynRule => items.extend(syn_rule(tree).map(Item::SynRule)),
                _ => {}
            },
            _ => {}
        }
    }

    Some(File {
        span: tree.span,
        items,
    })
}

#[derive(Debug)]
pub struct Tokenizer {
    span: StrSpan,
    rules: HandleVec<TokenRuleHandle, TokenRule>,
}

fn tokenizer(tree: &Tree) -> Option<Tokenizer> {
    assert_eq!(tree.kind, TreeKind::Tokenizer);

    let mut rules = HandleVec::new();

    for c in &tree.children {
        match c {
            Child::Tree(tree) => match tree.kind {
                TreeKind::TokenRule => rules.extend(token_rule(tree)),
                _ => {}
            },
            _ => {}
        }
    }

    Some(Tokenizer {
        span: tree.span,
        rules,
    })
}

#[derive(Debug)]
pub struct Attribute {
    span: StrSpan,
    name: StrSpan,
}

fn attribute(tree: &Tree) -> Option<Attribute> {
    assert_eq!(tree.kind, TreeKind::Attribute);

    let mut name = None;

    for c in &tree.children {
        match c {
            Child::Token(token) => match token.kind {
                TokenKind::Ident => name = Some(token.span),
                _ => {}
            },
            _ => {}
        }
    }

    Some(Attribute {
        span: tree.span,
        name: name?,
    })
}

#[derive(Debug)]
pub struct TokenRule {
    span: StrSpan,
    name: StrSpan,
    value: StrSpan,
}

fn token_rule(tree: &Tree) -> Option<TokenRule> {
    assert_eq!(tree.kind, TreeKind::TokenRule);

    let mut name = None;
    let mut value = None;

    for c in &tree.children {
        match c {
            Child::Token(token) => match token.kind {
                TokenKind::Ident => name = Some(token.span),
                TokenKind::Literal => value = Some(token.span),
                _ => {}
            },
            _ => {}
        }
    }

    Some(TokenRule {
        span: tree.span,
        name: name?,
        value: value?,
    })
}

#[derive(Debug)]
pub struct Parameters {
    params: Vec<StrSpan>,
}

fn parameters(tree: &Tree) -> Option<Parameters> {
    assert_eq!(tree.kind, TreeKind::Parameters);

    let mut params = Vec::new();

    for c in &tree.children {
        match c {
            Child::Token(token) => match token.kind {
                TokenKind::Ident => params.push(token.span),
                _ => {}
            },
            _ => {}
        }
    }

    Some(Parameters { params })
}

#[derive(Debug)]
pub struct SynRule {
    span: StrSpan,
    name: StrSpan,
    parameters: Option<Parameters>,
    attributes: Vec<Attribute>,
    expression: Expression,
}

fn syn_rule(tree: &Tree) -> Option<SynRule> {
    assert_eq!(tree.kind, TreeKind::SynRule);

    let mut attributes = Vec::new();
    let mut name = None;
    let mut expr = None;
    let mut params = None;

    for c in &tree.children {
        match c {
            Child::Tree(tree) => match tree.kind {
                TreeKind::PreExpr
                | TreeKind::AtomExpr
                | TreeKind::ParenExpr
                | TreeKind::CallExpr
                | TreeKind::BinExpr
                | TreeKind::SeqExpr
                | TreeKind::PostExpr
                | TreeKind::PostName => {
                    if let Some(e) = expression(tree) {
                        expr = Some(e);
                    }
                }
                TreeKind::Attribute => attributes.extend(attribute(tree)),
                TreeKind::Parameters => params = parameters(tree),
                _ => {}
            },
            Child::Token(token) => match token.kind {
                TokenKind::Ident => name = Some(token.span),
                _ => {}
            },
        }
    }

    Some(SynRule {
        span: tree.span,
        name: name?,
        parameters: params,
        attributes,
        expression: expr?,
    })
}

#[derive(Debug)]
pub struct PreExpr {
    span: StrSpan,
    attributes: Vec<Attribute>,
    expr: Box<Expression>,
}
#[derive(Debug)]
pub struct ParenExpr {
    span: StrSpan,
    expr: Box<Expression>,
}
#[derive(Debug)]
pub struct CallExpr {
    span: StrSpan,
    name: StrSpan,
    args: Box<Expression>,
}
#[derive(Debug)]
pub struct PostName {
    span: StrSpan,
    expr: Box<Expression>,
    name: StrSpan,
}
#[derive(Debug)]
pub enum PostExprKind {
    Question,
    Star,
    Plus,
}
#[derive(Debug)]
pub struct PostExpr {
    span: StrSpan,
    expr: Box<Expression>,
    kind: PostExprKind,
}
#[derive(Debug)]
pub struct BinExpr {
    span: StrSpan,
    left: Box<Expression>,
    right: Box<Expression>,
}
#[derive(Debug)]
pub struct SeqExpr {
    span: StrSpan,
    exprs: Vec<Expression>,
}

#[derive(Debug)]
pub enum Expression {
    Ident(StrSpan),
    Literal(StrSpan),
    Paren(ParenExpr),
    PreExpr(PreExpr),
    CallExpr(CallExpr),
    PostName(PostName),
    PostExpr(PostExpr),
    BinExpr(BinExpr),
    SeqExpr(SeqExpr),
}

fn expression(tree: &Tree) -> Option<Expression> {
    let span = tree.span;
    match tree.kind {
        TreeKind::AtomExpr => {
            for c in &tree.children {
                match c {
                    Child::Token(crate::Token {
                        kind: TokenKind::Ident,
                        span,
                    }) => return Some(Expression::Ident(*span)),
                    Child::Token(crate::Token {
                        kind: TokenKind::Literal,
                        span,
                    }) => return Some(Expression::Literal(*span)),
                    _ => {}
                }
            }
        }
        TreeKind::PreExpr => {
            let mut attributes = Vec::new();
            let mut expr = None;
            for c in &tree.children {
                match c {
                    Child::Tree(
                        tree @ crate::Tree {
                            kind: TreeKind::Attribute,
                            span,
                            children,
                        },
                    ) => attributes.extend(attribute(tree)),
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            expr = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::PreExpr(PreExpr {
                span,
                attributes,
                expr: Box::new(expr?),
            }));
        }
        TreeKind::ParenExpr => {
            let mut expr = None;
            for c in &tree.children {
                match c {
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            expr = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::Paren(ParenExpr {
                span,
                expr: Box::new(expr?),
            }));
        }
        TreeKind::CallExpr => {
            let mut name = None;
            let mut args = None;
            for c in &tree.children {
                match c {
                    Child::Token(crate::Token {
                        kind: TokenKind::Ident,
                        span,
                    }) => name = Some(*span),
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            args = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::CallExpr(CallExpr {
                span,
                name: name?,
                args: Box::new(args?),
            }));
        }
        TreeKind::PostName => {
            let mut name = None;
            let mut expr = None;
            for c in &tree.children {
                match c {
                    Child::Token(crate::Token {
                        kind: TokenKind::Ident,
                        span,
                    }) => name = Some(*span),
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            expr = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::PostName(PostName {
                span,
                name: name?,
                expr: Box::new(expr?),
            }));
        }
        TreeKind::PostExpr => {
            let mut kind = None;
            let mut expr = None;
            for c in &tree.children {
                match c {
                    Child::Token(crate::Token {
                        kind: TokenKind::Question,
                        span,
                    }) => kind = Some(PostExprKind::Question),
                    Child::Token(crate::Token {
                        kind: TokenKind::Star,
                        span,
                    }) => kind = Some(PostExprKind::Star),
                    Child::Token(crate::Token {
                        kind: TokenKind::Plus,
                        span,
                    }) => kind = Some(PostExprKind::Plus),
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            expr = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::PostExpr(PostExpr {
                span,
                kind: kind?,
                expr: Box::new(expr?),
            }));
        }
        TreeKind::BinExpr => {
            let mut expr1 = None;
            let mut expr2 = None;
            for c in &tree.children {
                match c {
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            if expr1.is_none() {
                                expr1 = Some(e);
                            } else {
                                expr2 = Some(e);
                            }
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::BinExpr(BinExpr {
                span,
                left: Box::new(expr1?),
                right: Box::new(expr2?),
            }));
        }
        TreeKind::SeqExpr => {
            let mut exprs = Vec::new();
            for c in &tree.children {
                match c {
                    Child::Tree(tree) => {
                        if let Some(e) = expression(tree) {
                            exprs.push(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::SeqExpr(SeqExpr { span, exprs }));
        }
        _ => {}
    }

    None
}
