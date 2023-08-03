#![allow(unused)]

use std::borrow::Cow;

use crate::{
    handle::HandleVec, simple_handle, Lexer, Node, NodeKind, StrSpan, TokenKind, TreeKind,
};

#[derive(Debug)]
pub enum Item {
    Tokenizer(Tokenizer),
    SynRule(SynRule),
}

#[derive(Debug)]
pub struct File {
    pub span: StrSpan,
    pub items: Vec<Item>,
}

pub fn file(tree: &Node, arena: &[Node]) -> Option<File> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::File));

    let mut items = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::Tokenizer) => {
                items.extend(tokenizer(c, arena).map(Item::Tokenizer))
            }
            NodeKind::Tree(TreeKind::SynRule) => {
                items.extend(syn_rule(c, arena).map(Item::SynRule))
            }
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
    pub span: StrSpan,
    pub rules: Vec<TokenRule>,
}

fn tokenizer(tree: &Node, arena: &[Node]) -> Option<Tokenizer> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Tokenizer));

    let mut rules = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::TokenRule) => rules.extend(token_rule(c, arena)),
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
    pub span: StrSpan,
    pub name: StrSpan,
}

fn attribute(tree: &Node, arena: &[Node]) -> Option<Attribute> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Attribute));

    let mut name = None;

    for c in tree.children(arena) {
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
    pub span: StrSpan,
    pub name: StrSpan,
    pub attributes: Vec<Attribute>,
    pub value: StrSpan,
}

fn token_rule(tree: &Node, arena: &[Node]) -> Option<TokenRule> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::TokenRule));

    let mut name = None;
    let mut value = None;
    let mut attrs = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::Attribute) => attrs.extend(attribute(c, arena)),
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
            NodeKind::Token(TokenKind::Literal) => value = Some(c.span),
            _ => {}
        }
    }

    Some(TokenRule {
        span: tree.span,
        name: name?,
        attributes: attrs,
        value: value?,
    })
}

#[derive(Debug)]
pub struct Parameters {
    pub params: Vec<StrSpan>,
}

fn parameters(tree: &Node, arena: &[Node]) -> Option<Parameters> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Parameters));

    let mut params = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Token(TokenKind::Ident) => params.push(c.span),
            _ => {}
        }
    }

    Some(Parameters { params })
}

#[derive(Debug)]
pub struct SynRule {
    pub span: StrSpan,
    pub name: StrSpan,
    pub inline: bool,
    pub paramaters: Option<Parameters>,
    pub attributes: Vec<Attribute>,
    pub expression: Expression,
}

fn syn_rule(tree: &Node, arena: &[Node]) -> Option<SynRule> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::SynRule));

    let mut attributes = Vec::new();
    let mut name = None;
    let mut expr = None;
    let mut params = None;
    let mut inline = false;

    for c in tree.children(arena) {
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
                if let Some(e) = expression(c, arena) {
                    expr = Some(e);
                }
            }
            NodeKind::Tree(TreeKind::Attribute) => attributes.extend(attribute(c, arena)),
            NodeKind::Tree(TreeKind::Parameters) => params = parameters(c, arena),
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
            NodeKind::Token(TokenKind::InlineKeyword) => inline = true,
            _ => {}
        }
    }

    Some(SynRule {
        span: tree.span,
        name: name?,
        inline,
        paramaters: params,
        attributes,
        expression: expr?,
    })
}

#[derive(Debug)]
pub struct PreExpr {
    pub span: StrSpan,
    pub attributes: Vec<Attribute>,
    pub expr: Box<Expression>,
}
#[derive(Debug)]
pub struct ParenExpr {
    pub span: StrSpan,
    pub expr: Box<Expression>,
}
#[derive(Debug)]
pub struct CallExpr {
    pub span: StrSpan,
    pub name: StrSpan,
    pub args: Option<Box<Expression>>,
}
#[derive(Debug)]
pub struct PostName {
    pub span: StrSpan,
    pub expr: Box<Expression>,
    pub name: StrSpan,
}
#[derive(Debug)]
pub enum PostExprKind {
    Question,
    Star,
    Plus,
}
#[derive(Debug)]
pub struct PostExpr {
    pub span: StrSpan,
    pub expr: Box<Expression>,
    pub kind: PostExprKind,
}
#[derive(Debug)]
pub struct BinExpr {
    pub span: StrSpan,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}
#[derive(Debug)]
pub struct SeqExpr {
    pub span: StrSpan,
    pub exprs: Vec<Expression>,
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

fn expression(tree: &Node, arena: &[Node]) -> Option<Expression> {
    let span = tree.span;
    match tree.kind {
        NodeKind::Tree(TreeKind::AtomExpr) => {
            for c in tree.children(arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Tree(TreeKind::Attribute) => attributes.extend(attribute(c, arena)),
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
                            args = Some(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::CallExpr(CallExpr {
                span,
                name: name?,
                args: args.map(Box::new),
            }));
        }
        NodeKind::Tree(TreeKind::PostName) => {
            let mut name = None;
            let mut expr = None;
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Token(TokenKind::Question) => kind = Some(PostExprKind::Question),
                    NodeKind::Token(TokenKind::Star) => kind = Some(PostExprKind::Star),
                    NodeKind::Token(TokenKind::Plus) => kind = Some(PostExprKind::Plus),
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = expression(c, arena) {
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

pub fn unescape_str_literal(src: &str) -> Option<Cow<str>> {
    assert!(!src.is_empty());

    let mut l = Lexer::new(src.as_bytes());

    let mut raw = false;
    if l.peek().unwrap() == b'r' {
        raw = true;
        l.next();
    }

    let mut balance = 0;
    loop {
        match l.next() {
            Some(b'#') => balance += 1,
            Some(b'\'') => break,
            _ => return None,
        }
    }

    let mut start = l.pos();
    let mut end = start;
    let mut string = String::new();

    'done: loop {
        match l.next() {
            None => return None,
            Some(b'\\') if !raw => {
                let mut catchup = l.span_since(start);
                // do not push the starting \
                catchup.end -= 1;

                let escaped = match l.next().unwrap() {
                    b'\\' => Some('\\'),
                    b'n' => Some('\n'),
                    b't' => Some('\t'),
                    b'0' => Some('\0'),
                    _ => None,
                };

                if let Some(escaped) = escaped {
                    let str = catchup.as_str(src);
                    string.push_str(str);
                    string.push(escaped);

                    start = l.pos();
                }
            }
            Some(b'\'') => {
                // do not include the ending '
                end = l.pos() - 1;
                let mut balance = balance;
                loop {
                    if balance == 0 {
                        break 'done;
                    }
                    if let Some(b'#') = l.next() {
                        balance -= 1;
                    } else {
                        break;
                    }
                }
            }
            _ => {}
        }
    }

    let span = StrSpan { start, end };
    let str = span.as_str(src);

    if string.is_empty() {
        Some(str.into())
    } else {
        string.push_str(str);
        Some(string.into())
    }
}

#[rustfmt::skip]
#[test]
fn test_read_maybe_escaped_string() {
    let src = r"###'hi\nthis\tis your mother👍'###";
    let out =      "hi\nthis\tis your mother👍";

    let span = StrSpan {
        start: 0,
        end: src.len() as u32,
    };

    let res = unescape_str_literal(src).unwrap();
    assert!(matches!(res, Cow::Owned(_)));
    assert_eq!(&*res, out);
}
