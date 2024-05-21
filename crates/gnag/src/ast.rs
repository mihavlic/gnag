#![allow(unused)]

use std::borrow::Cow;

use crate::{
    ctx::ErrorAccumulator, handle::HandleVec, simple_handle, Lexer, Node, NodeKind, SpannedError,
    StrSpan, TokenKind, TreeKind,
};

pub struct ParsedFile {
    pub root: Node,
    pub arena: Vec<Node>,
}

impl ParsedFile {
    pub fn new(src: &str, err: &ErrorAccumulator) -> ParsedFile {
        let mut lexer = Lexer::new(src.as_bytes());

        let (tokens, trivia) = crate::lex(&mut lexer);
        let mut parser = crate::Parser::new(src, tokens, trivia);
        _ = crate::file(&mut parser);

        let mut arena = Vec::new();
        let root = parser.build_tree(&mut arena);

        Self { root, arena }
    }
}

#[derive(Debug)]
pub struct File {
    pub span: StrSpan,
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub enum Item {
    Tokens(Tokens),
    Rules(Rules),
}

pub fn file(tree: &Node, arena: &[Node]) -> Option<File> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::File));

    let mut items = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::Tokens) => items.extend(tokens(c, arena).map(Item::Tokens)),
            NodeKind::Tree(TreeKind::Rules) => items.extend(rules(c, arena).map(Item::Rules)),
            _ => {}
        }
    }

    Some(File {
        span: tree.span,
        items,
    })
}

#[derive(Debug)]
pub struct Tokens {
    pub span: StrSpan,
    pub rules: Vec<TokenRule>,
}

fn tokens(tree: &Node, arena: &[Node]) -> Option<Tokens> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Tokens));

    let mut rules = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::TokenRule) => rules.extend(token_rule(c, arena)),
            _ => {}
        }
    }

    Some(Tokens {
        span: tree.span,
        rules,
    })
}

#[derive(Debug)]
pub struct Rules {
    pub span: StrSpan,
    pub rules: Vec<SynRule>,
}

fn rules(tree: &Node, arena: &[Node]) -> Option<Rules> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::Rules));

    let mut rules = Vec::new();

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(TreeKind::SynRule) => rules.extend(rule(c, arena)),
            _ => {}
        }
    }

    Some(Rules {
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
pub enum TokenValue {
    String,
    Regex,
}

#[derive(Debug)]
pub struct TokenRule {
    pub span: StrSpan,
    pub name: StrSpan,
    pub attributes: Vec<Attribute>,
    pub pattern: StrSpan,
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
        pattern: value?,
    })
}

#[derive(Debug)]
pub struct Parameters {
    pub span: StrSpan,
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

    Some(Parameters {
        span: tree.span,
        params,
    })
}

#[derive(Debug)]
pub struct SynRule {
    pub span: StrSpan,
    pub name: StrSpan,
    pub inline: bool,
    pub paramaters: Option<Parameters>,
    pub attributes: Vec<Attribute>,
    pub expression: Option<Expression>,
}

fn rule(tree: &Node, arena: &[Node]) -> Option<SynRule> {
    assert_eq!(tree.kind, NodeKind::Tree(TreeKind::SynRule));

    let mut attributes = Vec::new();
    let mut name = None;
    let mut expr = None;
    let mut params = None;

    for c in tree.children(arena) {
        match c.kind {
            NodeKind::Tree(
                TreeKind::AtomExpr
                | TreeKind::ParenExpr
                | TreeKind::PrattExpr
                | TreeKind::CallExpr
                | TreeKind::BinExpr
                | TreeKind::SeqExpr
                | TreeKind::PostExpr,
            ) => {
                if let Some(e) = expression(c, arena) {
                    expr = Some(e);
                }
            }
            NodeKind::Tree(TreeKind::Attribute) => attributes.extend(attribute(c, arena)),
            NodeKind::Tree(TreeKind::Parameters) => params = parameters(c, arena),
            NodeKind::Token(TokenKind::Ident) => name = Some(c.span),
            _ => {}
        }
    }

    Some(SynRule {
        span: tree.span,
        name: name?,
        inline: params.is_some(),
        paramaters: params,
        attributes,
        expression: expr,
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
    // FIXME this is ugly
    pub expr: Option<Box<Expression>>,
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
pub struct PrattExpr {
    pub span: StrSpan,
    pub exprs: Vec<SynRule>,
}

// Atom = Ident | String | RegexString
// CallExpr = '<' Ident Expr? '>'
// ParenExpr = '(' Expr ')'
// PostExpr = Expr ('?' | '*' | '+')
// SeqExpr = Expr Expr+
// BinExpr = Expr '|' Expr
// PrattExpr = 'pratt' '{' (Newline | Rule)* '}'

#[derive(Debug)]
pub enum Expression {
    Ident(StrSpan),
    Literal(StrSpan),

    Paren(ParenExpr),
    CallExpr(CallExpr),
    PostExpr(PostExpr),
    BinExpr(BinExpr),
    SeqExpr(SeqExpr),
    PrattExpr(PrattExpr),
}

impl Expression {
    pub fn visit(&self, fun: &mut dyn FnMut(&Expression)) {
        fun(self);
        match self {
            Expression::Paren(a) => _ = a.expr.as_ref().map(|e| e.visit(fun)),
            Expression::CallExpr(a) => {
                if let Some(e) = &a.args {
                    e.visit(fun);
                }
            }
            Expression::PostExpr(a) => a.expr.visit(fun),
            Expression::BinExpr(a) => {
                a.left.visit(fun);
                a.right.visit(fun);
            }
            Expression::SeqExpr(a) => {
                for e in &a.exprs {
                    e.visit(fun);
                }
            }
            Expression::PrattExpr(a) => {
                for rule in &a.exprs {
                    if let Some(e) = &rule.expression {
                        e.visit(fun);
                    }
                }
            }
            Expression::Ident(_) | Expression::Literal(_) => {}
        }
    }
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
                expr: expr.map(Box::new),
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
        NodeKind::Tree(TreeKind::PrattExpr) => {
            let mut exprs = Vec::new();
            for c in tree.children(arena) {
                match c.kind {
                    NodeKind::Tree(_) => {
                        if let Some(e) = rule(c, arena) {
                            exprs.push(e);
                        }
                    }
                    _ => {}
                }
            }
            return Some(Expression::PrattExpr(PrattExpr { span, exprs }));
        }
        _ => {}
    }

    None
}

pub trait ExtractedStringAccumulator<'a> {
    fn begin_content(&mut self, offset: usize) {}
    fn push_str(&mut self, str: &str);
    fn push_escaped_char(&mut self, char: char);
    type Result: 'a;
    fn finish(self, verbatim: &'a str) -> Self::Result;
}

impl<'a> ExtractedStringAccumulator<'a> for String {
    fn push_str(&mut self, str: &str) {
        self.push_str(str);
    }
    fn push_escaped_char(&mut self, char: char) {
        self.push(char);
    }
    type Result = Cow<'a, str>;
    fn finish(mut self, verbatim: &'a str) -> Self::Result {
        if self.is_empty() {
            Cow::Borrowed(verbatim)
        } else {
            self.push_str(verbatim);
            Cow::Owned(self)
        }
    }
}

/// returns a string extracted from the string literal syntax, along with a flag
/// whether the string was "raw" (ignored all escapes)
pub fn extract_str_literal(src: &str) -> Option<(Cow<str>, bool)> {
    extract_str_literal_impl(src, String::new())
}

pub fn extract_str_literal_impl<'a, U: ExtractedStringAccumulator<'a>>(
    src: &'a str,
    mut string: U,
) -> Option<(U::Result, bool)> {
    assert!(!src.is_empty());

    let mut l = Lexer::new(src.as_bytes());

    let raw = l.consume(b'r');

    if !l.consume(b'\'') {
        return None;
    }

    let mut start = l.pos();
    let mut end = start;

    string.begin_content(start as usize);
    loop {
        match l.next() {
            None => return None,
            Some(b'\\') if !raw => {
                let mut catchup = l.span_since(start);
                // do not push the starting \
                catchup.end -= 1;

                let escaped = match l.next() {
                    Some(b'\\') => Some('\\'),
                    Some(b'n') => Some('\n'),
                    Some(b't') => Some('\t'),
                    Some(b'0') => Some('\0'),
                    _ => None,
                };

                if let Some(escaped) = escaped {
                    let str = catchup.as_str(src);
                    string.push_str(str);
                    string.push_escaped_char(escaped);

                    start = l.pos();
                }
            }
            Some(b'\'') => {
                // do not include the ending '
                end = l.pos() - 1;
                break;
            }
            _ => {}
        }
    }

    let span = StrSpan { start, end };
    let str = span.as_str(src);

    Some((string.finish(str), raw))
}

#[derive(Debug)]
enum StringPart {
    Original(usize),
    Escaped,
}

impl StringPart {
    fn src_len(&self) -> usize {
        match self {
            StringPart::Original(len) => *len,
            StringPart::Escaped => 2,
        }
    }
    fn out_len(&self) -> usize {
        match self {
            StringPart::Original(len) => *len,
            StringPart::Escaped => 1,
        }
    }
}

#[derive(Default, Debug)]
pub struct DescribedString {
    start: Option<usize>,
    parts: Vec<StringPart>,
}
impl<'a> ExtractedStringAccumulator<'a> for DescribedString {
    fn begin_content(&mut self, offset: usize) {
        self.start = Some(offset);
    }
    fn push_str(&mut self, str: &str) {
        if !str.is_empty() {
            self.parts.push(StringPart::Original(str.len()));
        }
    }
    fn push_escaped_char(&mut self, char: char) {
        self.parts.push(StringPart::Escaped);
    }
    type Result = Self;
    fn finish(mut self, verbatim: &'a str) -> Self::Result {
        self.push_str(verbatim);
        self
    }
}

impl DescribedString {
    pub fn new(str: &str) -> Option<DescribedString> {
        extract_str_literal_impl(str, DescribedString::default()).map(|str| str.0)
    }
    /// Map an "index into the extracted string" to a "index into the source unextracted"
    pub fn find_offset(&self, out_offset: usize) -> Option<usize> {
        // since we're iterating the parts of an extracted string,
        // out_offset may end up inside a part

        //  current_out_offset = 0, current_src_offset = 1
        //  |  next_out_offset = 3
        //  |  |
        // "AAA.escaped.BBB"
        //   |
        //   out_offset = 1
        //
        // (we want to return Some(2))

        let mut current_src_offset = self.start?;
        let mut current_out_offset = 0;

        let mut parts = self.parts.iter();
        loop {
            if out_offset == current_out_offset {
                return Some(current_src_offset);
            }

            let Some(part) = parts.next() else {
                break;
            };

            let part_end_out_offfset = current_out_offset + part.out_len();
            if out_offset < part_end_out_offfset {
                // we're *inside* a StringPart
                //  - it cannot be StringPart::Escaped because its out_len() == 1
                //    and so gets caught by early return in this loop
                //  - so it must be StringPart::Original, where the original (src) length
                //    is the same as out length
                //
                //          part_end_out_offfset = 8
                //          |
                // "AAAAAAAA"
                //  |   |
                //  |   out_offset = 4
                //  current_out_offset = 0
                //  current_src_offset = 1
                //
                // (we want to return Some(5))
                return Some((current_src_offset + out_offset) - current_out_offset);
            }

            current_src_offset += part.src_len();
            current_out_offset = part_end_out_offfset;
        }

        None
    }
}

#[test]
fn test_describe_simple() {
    // src indices   0123456789
    let str: &str = "##'heyahey'##";
    // out indices      0123456

    let describe = DescribedString::new(str).unwrap();

    assert_eq!(describe.find_offset(0), Some(3));
    assert_eq!(describe.find_offset(1), Some(4));
    assert_eq!(describe.find_offset(2), Some(5));
    assert_eq!(describe.find_offset(3), Some(6));
    assert_eq!(describe.find_offset(4), Some(7));
    assert_eq!(describe.find_offset(5), Some(8));
    assert_eq!(describe.find_offset(6), Some(9));
}

#[test]
fn test_describe_escapes() {
    // src indices    0123456789
    let str: &str = r"##'h\ng\np'##";
    // out indices       01 23 4

    let describe = DescribedString::new(str).unwrap();

    assert_eq!(describe.find_offset(0), Some(3));
    assert_eq!(describe.find_offset(1), Some(4));
    assert_eq!(describe.find_offset(2), Some(6));
    assert_eq!(describe.find_offset(3), Some(7));
    assert_eq!(describe.find_offset(4), Some(9));
}

#[rustfmt::skip]
#[test]
fn test_extract_string() {
    let src = r"###'hi\nthis\tis your mother👍'###";
    let out =      "hi\nthis\tis your mother👍";

    let span = StrSpan {
        start: 0,
        end: src.len() as u32,
    };

    let res = extract_str_literal(src).unwrap();
    assert!(matches!(res.0, Cow::Owned(_)));
    assert_eq!(res.0, out);
}
