mod ast;
// pub mod bump;
pub mod handle;

use std::{cell::Cell, io::Read, ops::Index, time::Duration};

/// ```ignore
/// tokenizer {
///     @skip
///     whitespace r"\s+"
///     @contextual
///     node 'node'
///     eq '='
///     number r"\d+"
///     @verbatim hash_string r#"
///         
///     "#
/// }
///
/// rule function {
///   'fn' ident '(' fn_args ')' '->' type expr
/// }
/// 
/// @pratt
/// rule Expr {
///     PrefixOp | BinaryOp | PostfixOp |
///     Ident | Literal | '(' Expr ')' 
/// }
/// 
/// rule PrefixOp {
///     '!' Expr
/// }
/// 
/// rule PostfixOp {
///     Expr '(' <separated_list Expr ','> ')'
/// }
/// 
/// rule BinaryOp {
///     Expr '*' Expr |
///     Expr '/' Expr |
///     Expr @left ('+' | '-') Expr
/// }
/// ```

/// Starting code from
///  https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
///  - https://github.com/matklad/resilient-ll-parsing/blob/master/src/lib.rs
///  https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
///  - https://github.com/matklad/minipratt/blob/master/src/bin/pratt.rs 

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[rustfmt::skip]
pub enum TokenKind {
    Comment, Whitespace,

    Ident, Literal, Number,
    ErrorToken,
  
    LParen, RParen, LCurly, RCurly, LBracket, RBracket, LAngle, RAngle,
    TokenizerKeyword, RuleKeyword,
    At, Comma, Pipe, Colon, Question, Plus, Star
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[rustfmt::skip]
pub enum TreeKind {
    File,
      ErrorTree,
      Attribute,
        AttributeExpr,
        AttributeValue,
      Tokenizer,
        TokenRule,
      SynRule,
        Parameters,
      SynExpr,
        PreExpr,
        AtomExpr,
        ParenExpr,
        CallExpr,
        BinExpr,
        SeqExpr,
        PostExpr,
        PostName,
}

use bumpalo::Bump;
use tracy_client::ProfiledAllocator;
use TokenKind::*;

#[derive(Clone, Copy, Debug)]
pub struct TokenSpan {
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StrSpan {
    pub start: u32,
    pub end: u32,
}

impl StrSpan {
    #[inline]
    pub fn as_str(self, src: &str) -> &str {
        &src[self.start as usize..self.end as usize]
    }
}

impl Index<StrSpan> for str {
    type Output = str;
    fn index(&self, index: StrSpan) -> &Self::Output {
        &self[index.start as usize..index.end as usize]
    }
}

impl<'a> Index<StrSpan> for Lexer<'a> {
    type Output = str;
    fn index(&self, index: StrSpan) -> &Self::Output {
        &self.str[index.start as usize..index.end as usize]
    }
}

impl StrSpan {
    pub fn is_empty(self) -> bool {
        self.end <= self.start
    }
    pub fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    kind: TokenKind,
    span: StrSpan,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Tree(TreeKind),
    Token(TokenKind),
}

#[derive(Clone, Copy, Debug)]
pub struct Node<'a> {
    kind: NodeKind,
    span: StrSpan,
    children: &'a [Node<'a>],
}

impl<'a> Node<'a> {
    fn print(
        &self,
        buf: &mut dyn std::fmt::Write,
        src: &str,
        errors: &mut std::slice::Iter<'_, ParseError>,
        level: usize,
    ) {
        for _ in 0..level {
            _ = buf.write_str("  ");
        }
        _ = write!(buf, "{:?}", self.kind);
        if self.children.is_empty() {
            _ = write!(buf, " {:?}", self.span.as_str(src));
        }
        if let Some(peek) = errors.clone().next() {
            if self.span == peek.span {
                errors.next();
                _ = write!(buf, " !!{}", peek.err);
            }
        }
        _ = write!(buf, "\n");
        for child in self.children {
            child.print(buf, src, errors, level + 1);
        }
    }
}

pub struct Lexer<'str> {
    str: &'str str,
    pos: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(str: &'a str) -> Self {
        Self { str, pos: 0 }
    }

    pub fn pos(&self) -> u32 {
        self.pos
    }

    pub fn span_since(&self, start: u32) -> StrSpan {
        StrSpan {
            start,
            end: self.pos(),
        }
    }

    pub fn restore_pos(&mut self, pos: u32) {
        debug_assert!(pos as usize <= self.str.len());
        self.pos = pos;
    }

    pub fn is_empty(&self) -> bool {
        self.pos as usize == self.str.len()
    }

    pub fn next(&mut self) -> Option<char> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let c = self.str[pos..].chars().next().unwrap();
            // TODO improve this
            self.pos += c.len_utf8() as u32;
            Some(c)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<char> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let c = self.str[pos..].chars().next().unwrap();
            Some(c)
        } else {
            None
        }
    }

    pub fn previous(&self) -> Option<char> {
        let pos = self.pos as usize;
        let mut rev = self.str[..pos].chars().rev();
        rev.next()
    }

    fn consume_while(&mut self, predicate: impl std::ops::Fn(char) -> bool) -> StrSpan {
        let start = self.pos();
        while let Some(c) = self.peek() {
            if predicate(c) {
                self.next();
            } else {
                break;
            }
        }
        StrSpan {
            start,
            end: self.pos(),
        }
    }

    fn choice<T>(&mut self, funs: &[fn(&mut Lexer) -> Option<T>]) -> Option<T> {
        let pos = self.pos;
        for fun in funs {
            match fun(self) {
                None => self.restore_pos(pos),
                some => return some,
            }
        }
        None
    }

    fn sequence(&mut self, sequence: &str) -> bool {
        if self.str[self.pos as usize..].starts_with(sequence) {
            self.pos += sequence.len() as u32;
            true
        } else {
            false
        }
    }
}

fn lex(l: &mut Lexer) -> (Vec<Token>, Vec<Token>) {
    let mut tokens = Vec::new();
    let mut trivia = Vec::new();
    while !l.is_empty() {
        let start = l.pos();
        let kind = l
            .choice(&[
                |l| {
                    if !l.consume_while(char::is_whitespace).is_empty() {
                        Some(Whitespace)
                    } else {
                        None
                    }
                },
                |l| match l.next().unwrap() {
                    '@' => Some(At),
                    ',' => Some(Comma),
                    '|' => Some(Pipe),
                    ':' => Some(Colon),
                    '?' => Some(Question),
                    '+' => Some(Plus),
                    '*' => Some(Star),
                    '(' => Some(LParen),
                    ')' => Some(RParen),
                    '{' => Some(LCurly),
                    '}' => Some(RCurly),
                    '[' => Some(LBracket),
                    ']' => Some(RBracket),
                    '<' => Some(LAngle),
                    '>' => Some(RAngle),
                    _ => None,
                },
                |l| {
                    if l.sequence("//") {
                        l.consume_while(|c| c != '\n');
                        Some(Comment)
                    } else {
                        None
                    }
                },
                |l| {
                    let mut raw = false;
                    if l.peek().unwrap() == 'r' {
                        raw = true;
                        l.next();
                    }

                    let mut balance = 0;
                    while let Some(c) = l.next() {
                        match c {
                            '#' => balance += 1,
                            '\'' => break,
                            _ => return None,
                        }
                    }

                    while let Some(c) = l.next() {
                        match c {
                            '\\' if raw => {
                                l.next();
                            }
                            '\'' => {
                                let mut balance = balance;
                                loop {
                                    if balance == 0 {
                                        return Some(Literal);
                                    }
                                    if let Some('#') = l.next() {
                                        balance -= 1;
                                    } else {
                                        break;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    None
                },
                |l| {
                    let span =
                        l.consume_while(|c| matches!(c, '_' | 'a'..='z' | 'A'..='Z' | '0'..='9'));
                    if span.is_empty() {
                        return None;
                    }
                    match &l[span] {
                        "rule" => Some(RuleKeyword),
                        "tokenizer" => Some(TokenizerKeyword),
                        _ => Some(Ident),
                    }
                },
                |l| {
                    let span = l.consume_while(|c| !c.is_ascii_whitespace());
                    if span.is_empty() {
                        l.next();
                    }
                    Some(ErrorToken)
                },
            ])
            .unwrap();

        let span = l.span_since(start);
        assert!(!span.is_empty());

        if kind == Whitespace || kind == Comment {
            trivia.push(Token { kind, span })
        } else {
            tokens.push(Token { kind, span })
        }
    }
    return (tokens, trivia);
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SpanStart(u32);

#[derive(Clone, Copy, PartialEq, Eq)]
struct SpanIndex(u32);

#[derive(Clone, Copy)]
struct ParserCheckpoint {
    pos: u32,
    fuel: u32,
    spans_len: u32,
    errors_len: u32,
}

#[derive(Clone, Copy)]
pub struct TreeSpan {
    kind: TreeKind,
    span: StrSpan,
}

#[derive(Clone)]
pub struct ParseError {
    span: StrSpan,
    err: String,
}

pub trait TreeVisitor {
    fn token(&mut self, token: Token);
    fn open_tree(&mut self, tree: TreeSpan);
    fn close_tree(&mut self, tree: TreeSpan);
}

pub struct BumpTreeBuilder<'a> {
    bump: &'a Bump,
    stack: Vec<usize>,
    child_stack: Vec<Node<'a>>,
}

impl<'a> TreeVisitor for BumpTreeBuilder<'a> {
    #[profiling::function]
    fn token(&mut self, token: Token) {
        self.child_stack.push(Node {
            kind: NodeKind::Token(token.kind),
            span: token.span,
            children: &[],
        });
    }

    #[profiling::function]
    fn open_tree(&mut self, _: TreeSpan) {
        self.stack.push(self.child_stack.len());
    }

    #[profiling::function]
    fn close_tree(&mut self, tree: TreeSpan) {
        let children_start = self.stack.pop().unwrap();
        let children = self
            .bump
            .alloc_slice_copy(&self.child_stack[children_start..]);
        children.reverse();

        self.child_stack.truncate(children_start);
        self.child_stack.push(Node {
            kind: NodeKind::Tree(tree.kind),
            span: tree.span,
            children,
        });
    }
}

impl<'a> BumpTreeBuilder<'a> {
    pub fn new(bump: &'a Bump) -> Self {
        Self {
            bump,
            stack: Vec::new(),
            child_stack: Vec::new(),
        }
    }
    pub fn finish(mut self) -> Node<'a> {
        self.child_stack.pop().unwrap()
    }
}

pub struct Parser<'a> {
    tokens: Vec<Token>,
    trivia: Vec<Token>,
    pos: u32,
    fuel: Cell<u32>,
    spans: Vec<TreeSpan>,
    errors: Vec<ParseError>,
    src: &'a str,
}

impl<'a> Parser<'a> {
    fn new(src: &str, tokens: Vec<Token>, trivia: Vec<Token>) -> Parser {
        Parser {
            tokens,
            trivia,
            pos: 0,
            fuel: Cell::new(256),
            spans: Vec::new(),
            errors: Vec::new(),
            src,
        }
    }

    // We push tree spans (and their errors) when we close them, so we end up with a reversed topological order; the root will always be last.
    // Let there be tree:
    //  |-----root----|
    //  |--a---| |--b-|
    //  | |-c| | |    |
    //  0123456789abcdef  -- indices of tokens
    // The spans will be like so:
    //  (label, start..end)
    //  [ (b, 9..f) (c, 2..6) (a, 0..8) (root, 0..f) ]
    fn visit_tree(&self, visitor: &mut impl TreeVisitor) {
        let mut merged_tokens = {
            let mut tokens = self.tokens.iter().rev().copied();
            let mut trivia = self.trivia.iter().rev().copied();
            let mut len = self.tokens.len() + self.trivia.len();

            std::iter::from_fn(move || {
                if len > 0 {
                    len -= 1;

                    let token_start = tokens.clone().next().map_or(-1, |a| a.span.start as i64);
                    let trivia_start = trivia.clone().next().map_or(-1, |a| a.span.start as i64);

                    debug_assert_ne!(token_start, trivia_start);
                    if token_start > trivia_start {
                        Some(tokens.next().unwrap())
                    } else {
                        Some(trivia.next().unwrap())
                    }
                } else {
                    None
                }
            })
        };

        // FIXME do not clone
        // let mut errors = self.errors.iter().cloned().rev().peekable();
        let mut spans = self.spans.iter().rev();

        let root = spans.clone().next().unwrap();

        // check that the root contains all of the tokens
        assert_eq!(root.span.start, 0);
        assert_eq!(root.span.end as usize, self.src.len());

        let mut span_stack = Vec::with_capacity(64);

        let mut current_span = root.span;
        let mut next_span = root.span;
        let mut pos = self.src.len() as u32;

        while pos > 0 {
            while pos == next_span.end {
                let opened = spans.next().unwrap();

                visitor.open_tree(*opened);

                debug_assert!(!opened.span.is_empty());

                span_stack.push(*opened);
                current_span = next_span;

                if let Some(next) = spans.clone().next() {
                    #[cfg(debug_assertions)]
                    {
                        let StrSpan { start, end } = next.span;
                        // check against this situation:
                        //  parent    |-------|
                        //  child   |-----|
                        if start >= start {
                            debug_assert!(end <= end);
                        } else {
                            debug_assert!(end <= start);
                        }
                    }
                    next_span = next.span;
                } else {
                    next_span = StrSpan {
                        start: u32::MAX,
                        end: 0,
                    };
                }
            }

            let limit = u32::max(current_span.start, next_span.end);
            while pos > limit {
                let token = merged_tokens.next().unwrap();
                visitor.token(token);
                pos = token.span.start;
            }

            while pos == current_span.start {
                let closed = span_stack.pop().unwrap();
                visitor.close_tree(closed);

                if let Some(parent) = span_stack.last() {
                    current_span = parent.span
                } else {
                    break;
                }
            }
        }
    }

    fn checkpoint(&self) -> ParserCheckpoint {
        ParserCheckpoint {
            pos: self.pos,
            fuel: self.fuel.get(),
            spans_len: self.spans.len().try_into().unwrap(),
            errors_len: self.errors.len().try_into().unwrap(),
        }
    }

    fn restore(&mut self, checkpoint: ParserCheckpoint) {
        let ParserCheckpoint {
            pos,
            fuel,
            spans_len,
            errors_len,
        } = checkpoint;

        self.pos = pos;
        self.fuel.set(fuel);

        assert!(spans_len as usize <= self.spans.len());
        self.spans.truncate(spans_len as usize);

        assert!(errors_len as usize <= self.errors.len());
        self.errors.truncate(errors_len as usize);
    }

    fn open(&mut self) -> SpanStart {
        let start = self
            .tokens
            .get(self.pos as usize)
            .map_or(0, |s| s.span.start);
        SpanStart(start)
    }

    fn close(&mut self, m: SpanStart, kind: TreeKind) -> StrSpan {
        let end = self
            .tokens
            .get(self.pos.saturating_sub(1) as usize)
            .map_or(0, |s| s.span.end);
        let tree = TreeSpan {
            kind,
            span: StrSpan { start: m.0, end },
        };
        self.spans.push(tree);
        tree.span
    }

    fn close_toplevel(&mut self, _m: SpanStart, kind: TreeKind) -> StrSpan {
        let tree = TreeSpan {
            kind,
            span: StrSpan {
                start: 0,
                end: self.src.len().try_into().unwrap(),
            },
        };
        self.spans.push(tree);
        tree.span
    }

    fn close_with_err(&mut self, m: SpanStart, err: impl ToString) {
        let kind = TreeKind::ErrorTree;
        let err = err.to_string();
        let span = self.close(m, kind);
        self.errors.push(ParseError { span, err });
    }

    fn advance(&mut self) {
        assert!(!self.eof());
        self.fuel.set(256);
        self.pos += 1;
    }

    fn try_advance(&mut self) {
        if !self.eof() {
            self.fuel.set(256);
            self.pos += 1;
        }
    }

    #[inline]
    fn eof(&self) -> bool {
        self.pos as usize == self.tokens.len()
    }

    fn peek(&self) -> Option<TokenKind> {
        self.nth(0)
    }

    fn nth(&self, lookahead: u32) -> Option<TokenKind> {
        self.nth_impl(lookahead).map(|it| it.kind)
    }

    fn nth_impl(&self, lookahead: u32) -> Option<&Token> {
        if self.fuel.get() == 0 {
            panic!("parser is stuck")
        }
        self.fuel.set(self.fuel.get() - 1);
        self.tokens.get((self.pos + lookahead) as usize)
    }

    #[inline]
    fn at(&self, kind: TokenKind) -> bool {
        self.nth(0) == Some(kind)
    }

    #[inline]
    fn at_any(&self, kinds: &[TokenKind]) -> bool {
        if let Some(any) = self.nth(0) {
            kinds.contains(&any)
        } else {
            false
        }
    }

    fn token(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            // zero-size scope
            let m = self.open();
            self.close_with_err(m, format!("Expected '{kind:?}'"));
            false
        }
    }
}

pub trait RecoverMethod {
    fn recover(&self, p: &mut Parser);
}

pub struct RecoverUntil<'a>(&'a [TokenKind]);
impl<'a> RecoverMethod for RecoverUntil<'a> {
    #[cold]
    fn recover(&self, p: &mut Parser) {
        let m = p.open();
        while !(p.eof() || p.at_any(self.0)) {
            p.advance()
        }
        p.close_with_err(m, "Recover until");
    }
}

pub struct StepRecoverUntil<'a>(&'a [TokenKind]);
impl<'a> RecoverMethod for StepRecoverUntil<'a> {
    #[cold]
    fn recover(&self, p: &mut Parser) {
        let m = p.open();
        p.try_advance();
        while !(p.eof() || p.at_any(self.0)) {
            p.advance()
        }
        p.close_with_err(m, "Unexpected input");
    }
}

// @always_valid
// (Tokenizer | GrammarRule)*:files
#[profiling::function]
fn file(p: &mut Parser) -> bool {
    let r = StepRecoverUntil(&[TokenizerKeyword, RuleKeyword]);
    let m = p.open();
    while !p.eof() {
        'choice: {
            let checkpoint = p.checkpoint();
            if tokenizer(p) {
                break 'choice;
            }

            p.restore(checkpoint);
            if syn_rule(p) {
                break 'choice;
            }

            p.restore(checkpoint);
            r.recover(p);
        }
    }
    p.close_toplevel(m, TreeKind::File);
    true
}

// 'tokenizer' '{' TokenRule*:rules '}'
#[profiling::function]
fn tokenizer(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(TokenizerKeyword) {
        return false;
    }

    p.expect(LCurly);
    while token_rule(p) {}
    p.expect(RCurly);

    p.close(m, TreeKind::Tokenizer);
    true
}

// (Number | Ident):value
#[profiling::function]
fn attribute_value(p: &mut Parser) -> bool {
    let m = p.open();

    'choice: {
        if p.token(Number) {
            break 'choice;
        }
        if p.token(Ident) {
            break 'choice;
        }
        return false;
    };

    p.close(m, TreeKind::AttributeValue);
    true
}

// Ident:name ( '(' AttributeValue:value ')' )?
#[profiling::function]
fn attribute_expr(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(Ident) {
        return false;
    }

    'optional: {
        if !p.token(LParen) {
            break 'optional;
        }

        attribute_value(p);

        p.expect(RParen);
    }

    p.close(m, TreeKind::AttributeExpr);
    true
}

// '@' Ident:name ( '(' <separated_list AttributeExpr ','>:values ')' )?
#[profiling::function]
fn attribute(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(At) {
        return false;
    }
    p.expect(Ident);
    'optional: {
        if !p.token(LParen) {
            break 'optional;
        }
        loop {
            if !attribute_expr(p) {
                break;
            }
            if !p.token(Comma) {
                break;
            }
        }
        p.expect(RParen);
    }

    p.close(m, TreeKind::Attribute);
    true
}

// Attribute:attributes* Ident:name <commit> Literal:value
#[profiling::function]
fn token_rule(p: &mut Parser) -> bool {
    let m = p.open();

    while attribute(p) {}
    if !p.token(Ident) {
        return false;
    }
    p.expect(Literal);

    p.close(m, TreeKind::TokenRule);
    true
}

// Attribute* 'rule' Ident Parameters? '{' SynExpr '}'
#[profiling::function]
fn syn_rule(p: &mut Parser) -> bool {
    let m = p.open();

    while attribute(p) {}
    if !p.token(RuleKeyword) {
        return false;
    }
    p.expect(Ident);
    parameters(p);
    p.expect(LCurly);
    expr(p, 0);
    p.expect(RCurly);

    p.close(m, TreeKind::SynRule);
    true
}

// '(' <separated_list Ident ','> ')'
#[profiling::function]
fn parameters(p: &mut Parser) -> bool {
    if !p.token(LParen) {
        return false;
    }
    loop {
        if !attribute_expr(p) {
            break;
        }
        if !p.token(Comma) {
            break;
        }
    }
    p.expect(RParen);
    true
}

/// ```ignore
/// @pratt
/// rule Expr {
///   Ident | Literal | PreExpr | BinExpr | PostExpr
/// }
///
/// rule PreExpr {
///   Attribute+ Expr
/// }
///
/// rule AtomExpr {
///   '<' Ident Expr '>' |
///   '(' Expr ')'
/// }
///
/// rule SeqExpr {
///     // incredible
///     Expr Expr+
/// }
///
/// rule BinExpr {
///   Expr '|' Expr
/// }
///
/// rule PostExpr {
///   Expr '?' |
///   Expr '+' |
///   Expr Expr
/// }
///
/// ```
const _: u32 = 0;

// atom bp
//  '<'  _ _
//  '('  _ _
// prefix bp
//  '@'  _ 4
// postfix bp
//  '?'  5 _
//  '+'  5 _
//  '*'  5 _
//  Expr 3 _
// binary bp
//  '|'  2 1

#[profiling::function]
fn base_expr(p: &mut Parser) -> bool {
    let m = p.open();
    let Some(peek) = p.peek() else {
        return false;
    };
    match peek {
        Ident | Literal => {
            p.advance();
            p.close(m, TreeKind::AtomExpr);
        }
        At => {
            while attribute(p) {}
            // bp table lookup
            expr(p, 4);
            p.close(m, TreeKind::PreExpr);
        }
        LParen => {
            p.advance();
            // bp table lookup
            expr(p, 0);
            p.token(RParen);
            p.close(m, TreeKind::ParenExpr);
        }
        LAngle => {
            p.advance();
            p.token(Ident);
            // bp table lookup
            expr(p, 0);
            p.token(RAngle);
            p.close(m, TreeKind::CallExpr);
        }
        _ => return false,
    }
    true
}

#[profiling::function]
fn expr(p: &mut Parser, min_bp: u8) -> bool {
    let m = p.open();

    if !base_expr(p) {
        return false;
    }
    while let Some(peek) = p.peek() {
        match peek {
            Colon => {
                // bp table lookup
                let bp = (5, ());
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                p.expect(Ident);
                p.close(m, TreeKind::PostName);
                continue;
            }
            Question | Plus | Star => {
                // bp table lookup
                let bp = (5, ());
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                p.close(m, TreeKind::PostExpr);
                continue;
            }
            Pipe => {
                // bp table lookup
                let bp = (2, 1);
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                expr(p, bp.1);
                p.close(m, TreeKind::BinExpr);
                continue;
            }
            Ident | Literal | LAngle | LParen | At => {
                // bp table lookup
                let bp = (3, ());
                if bp.0 <= min_bp {
                    break;
                }

                let mut first = true;
                while expr(p, bp.0) {
                    first = false;
                }

                if !first {
                    p.close(m, TreeKind::SeqExpr);
                    continue;
                }
            }
            _ => {}
        }

        break;
    }

    true
}

pub fn parse<'a>(bump: &'a Bump, text: &str) -> (Node<'a>, Vec<ParseError>) {
    let mut lexer = Lexer::new(text);
    let (tokens, trivia) = lex(&mut lexer);
    let mut parser = Parser::new(text, tokens, trivia);
    _ = file(&mut parser);
    let mut builder = BumpTreeBuilder::new(bump);
    parser.visit_tree(&mut builder);

    (builder.finish(), parser.errors)
}

#[global_allocator]
static GLOBAL: ProfiledAllocator<std::alloc::System> =
    ProfiledAllocator::new(std::alloc::System, 30);

fn main() {
    // tracy_client::Client::start();
    // profiling::register_thread!("Main Thread");

    let input = if let Some(path) = std::env::args().nth(1) {
        std::fs::read_to_string(path).unwrap()
    } else {
        let mut input = String::new();
        let mut stdin = std::io::stdin().lock();
        _ = stdin.read_to_string(&mut input);
        input
    };

    if input.is_empty() {
        println!("No input provided");
        std::process::exit(-1);
    }

    let mut bump = Bump::new();

    if true {
        let input = input.repeat(1000);
        let rep = 10;
        let start = std::time::Instant::now();
        for _ in 0..rep {
            bump.reset();
            std::hint::black_box(parse(&bump, &input));
        }
        let elapsed = start.elapsed().as_secs_f64();
        let size = input.len() * rep;
        println!("{} MiB/s", size as f64 / (1024.0 * 1024.0 * elapsed));
    } else {
        let (cst, errors) = parse(&bump, &input);
        let mut buf = String::new();
        cst.print(&mut buf, &input, &mut errors.iter(), 0);
        println!("{buf}");
    }

    profiling::finish_frame!();
}
