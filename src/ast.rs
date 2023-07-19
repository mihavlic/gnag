#![allow(unused)]

use crate::{handle::HandleVec, simple_handle, Node, NodeKind, StrSpan, TokenKind, TreeKind};

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

#[profiling::function]
pub fn file(tree: &Node) -> Option<File> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::File));

    let mut items = Vec::new();

    for c in tree.children {
        match c.kind {
            NodeKind::Tree(TreeKind::Tokenizer) => items.extend(tokenizer(c).map(Item::Tokenizer)),
            NodeKind::Tree(TreeKind::SynRule) => items.extend(syn_rule(c).map(Item::SynRule)),
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

#[profiling::function]
fn tokenizer(tree: &Node) -> Option<Tokenizer> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Tokenizer));

    let mut rules = HandleVec::new();

    for c in tree.children {
        match c.kind {
            NodeKind::Tree(TreeKind::TokenRule) => rules.extend(token_rule(tree)),
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

#[profiling::function]
fn attribute(tree: &Node) -> Option<Attribute> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Attribute));

    let mut name = None;

    for c in tree.children {
        match c.kind {
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
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

#[profiling::function]
fn token_rule(tree: &Node) -> Option<TokenRule> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::TokenRule));

    let mut name = None;
    let mut value = None;

    for c in tree.children {
        match c.kind {
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
            NodeKind::Token(TokenKind::Literal) => value = Some(c.span),
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

#[profiling::function]
fn parameters(tree: &Node) -> Option<Parameters> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Parameters));

    let mut params = Vec::new();

    for c in tree.children {
        match c.kind {
            NodeKind::Token(TokenKind::Ident) => params.push(c.span),
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

#[profiling::function]
fn syn_rule(tree: &Node) -> Option<SynRule> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::SynRule));

    let mut attributes = Vec::new();
    let mut name = None;
    let mut expr = None;
    let mut params = None;

    for c in tree.children {
        match c.kind {
            NodeKind::Tree(
                TreeKind::PreExpr
                | TreeKind::AtomExpr
                | TreeKind::ParenExpr
                | TreeKind::CallExpr
                | TreeKind::BinExpr
                | TreeKind::SeqExpr
                | TreeKind::PostExpr
                | TreeKind::PostName,
            ) => {
                if let Some(e) = expression(tree) {
                    expr = Some(e);
                }
            }
            NodeKind::Tree(TreeKind::Attribute) => attributes.extend(attribute(tree)),
            NodeKind::Tree(TreeKind::Parameters) => params = parameters(tree),
            _ => {}
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
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

#[profiling::function]
fn expression(tree: &Node) -> Option<Expression> {
    let span = tree.span;
    match tree.kind {
        NodeKind::Tree(TreeKind::AtomExpr) => {
            for c in tree.children {
                match c.kind {
                    NodeKind::Token(TokenKind::Ident) => return Some(Expression::Ident(c.span)),
                    NodeKind::Token(TokenKind::Literal) => {
                        return Some(Expression::Literal(c.span))
                    }
                    _ => {}
                }
            }
        }
        NodeKind::Tree(TreeKind::PreExpr) => {
            let mut attributes = Vec::new();
            let mut expr = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Tree(TreeKind::Attribute) => attributes.extend(attribute(tree)),
                    NodeKind::Tree(_) => {
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
        NodeKind::Tree(TreeKind::ParenExpr) => {
            let mut expr = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Tree(_) => {
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
        NodeKind::Tree(TreeKind::CallExpr) => {
            let mut name = None;
            let mut args = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
                    NodeKind::Tree(_) => {
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
        NodeKind::Tree(TreeKind::PostName) => {
            let mut name = None;
            let mut expr = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
                    NodeKind::Tree(_) => {
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
        NodeKind::Tree(TreeKind::PostExpr) => {
            let mut kind = None;
            let mut expr = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Token(TokenKind::Question) => kind = Some(PostExprKind::Question),
                    NodeKind::Token(TokenKind::Star) => kind = Some(PostExprKind::Star),
                    NodeKind::Token(TokenKind::Plus) => kind = Some(PostExprKind::Plus),
                    NodeKind::Tree(_) => {
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
        NodeKind::Tree(TreeKind::BinExpr) => {
            let mut expr1 = None;
            let mut expr2 = None;
            for c in tree.children {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c) {
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
        NodeKind::Tree(TreeKind::SeqExpr) => {
            let mut exprs = Vec::new();
            for c in tree.children {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c) {
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
