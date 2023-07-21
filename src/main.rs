// mod ast;
// pub mod bump;
pub mod handle;

use std::{
    io::Read,
    ops::{Index, Range},
};

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

#[derive(Clone, Debug)]
pub struct Node {
    kind: NodeKind,
    span: StrSpan,
    children: Range<u32>,
}

impl Node {
    fn print(
        &self,
        buf: &mut dyn std::fmt::Write,
        src: &str,
        nodes: &[Node],
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
        for child in &nodes[self.children.start as usize..self.children.end as usize] {
            child.print(buf, src, nodes, errors, level + 1);
        }
    }
}

pub struct Lexer<'a> {
    str: &'a [u8],
    pos: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(str: &'a [u8]) -> Self {
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

    pub fn next(&mut self) -> Option<u8> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let byte = self.str[pos];
            self.pos += 1;
            Some(byte)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<u8> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let byte = self.str[pos];
            Some(byte)
        } else {
            None
        }
    }

    fn consume_while(&mut self, predicate: impl std::ops::Fn(u8) -> bool) -> StrSpan {
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

    fn sequence(&mut self, sequence: &[u8]) -> bool {
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
        let pos = l.pos();
        let kind = match l.next().unwrap() {
            b'\t' | b'\n' | b'\x0C' | b'\r' | b' ' => {
                l.restore_pos(pos);
                l.consume_while(|c| c.is_ascii_whitespace());
                Whitespace
            }
            b'/' if l.sequence(b"//") => {
                l.restore_pos(pos);
                l.consume_while(|c| c != b'\n');
                Comment
            }
            b'@' => At,
            b',' => Comma,
            b'|' => Pipe,
            b':' => Colon,
            b'?' => Question,
            b'+' => Plus,
            b'*' => Star,
            b'(' => LParen,
            b')' => RParen,
            b'{' => LCurly,
            b'}' => RCurly,
            b'[' => LBracket,
            b']' => RBracket,
            b'<' => LAngle,
            b'>' => RAngle,
            _ => 'choice: {
                l.restore_pos(pos);
                if l.sequence(b"rule") {
                    break 'choice RuleKeyword;
                }
                if l.sequence(b"tokenizer") {
                    break 'choice TokenizerKeyword;
                }
                'skip: {
                    let mut raw = false;
                    if l.peek().unwrap() == b'r' {
                        raw = true;
                        l.next();
                    }

                    let mut balance = 0;
                    while let Some(c) = l.next() {
                        match c {
                            b'#' => balance += 1,
                            b'\'' => break,
                            _ => break 'skip,
                        }
                    }

                    while let Some(c) = l.next() {
                        match c {
                            b'\\' if raw => {
                                l.next();
                            }
                            b'\'' => {
                                let mut balance = balance;
                                loop {
                                    if balance == 0 {
                                        break 'choice Literal;
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
                }
                l.restore_pos(pos);
                if !l
                    .consume_while(|c| matches!(c, b'_' | b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9'))
                    .is_empty()
                {
                    break 'choice Ident;
                }
                l.restore_pos(pos);
                {
                    let span = l.consume_while(|c| !c.is_ascii_whitespace());
                    if span.is_empty() {
                        l.next();
                    }
                    ErrorToken
                }
            }
        };

        let span = l.span_since(pos);
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
    spans_len: u32,
    errors_len: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct TreeSpan {
    kind: TreeKind,
    span: StrSpan,
}

#[derive(Clone, Debug)]
pub struct ParseError {
    span: StrSpan,
    err: String,
}

pub struct Parser<'a> {
    tokens: Vec<Token>,
    trivia: Vec<Token>,
    pos: u32,
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
    fn build_tree(&self, arena: &mut Vec<Node>) -> Node {
        arena.reserve(self.spans.len() + self.tokens.len() + self.trivia.len());

        let mut merged_tokens = {
            let mut tokens = self.tokens.iter().copied();
            let mut trivia = self.trivia.iter().copied();
            let mut len = self.tokens.len() + self.trivia.len();

            std::iter::from_fn(move || {
                if len > 0 {
                    len -= 1;

                    let token_start = tokens.clone().next().map_or(u32::MAX, |a| a.span.start);
                    let trivia_start = trivia.clone().next().map_or(u32::MAX, |a| a.span.start);

                    debug_assert_ne!(token_start, trivia_start);
                    if token_start < trivia_start {
                        Some(tokens.next().unwrap())
                    } else {
                        Some(trivia.next().unwrap())
                    }
                } else {
                    None
                }
            })
        };

        let mut stack: Vec<Node> = Vec::new();

        let mut pos = 0;
        for span in &self.spans {
            debug_assert!(!span.span.is_empty());

            let StrSpan { start, end } = span.span;

            // we split the token pushing into two branches depending on whether the next span
            // is closing over already pushed elements or
            //
            // this specialization actually makes it faster (maybe only on very large files?)
            let start_idx = if pos <= start {
                // the cursor has yet to enter the span
                let mut start_idx = None;
                while pos < end {
                    let token = merged_tokens.next().unwrap();
                    pos = token.span.end;
                    if token.span.start == start {
                        start_idx = Some(stack.len());
                    }
                    stack.push(Node {
                        kind: NodeKind::Token(token.kind),
                        span: token.span,
                        children: 0..0,
                    });
                }

                start_idx.unwrap()
            } else {
                // the cursor is already in the span, need to find the start
                let start_idx = stack
                    .binary_search_by_key(&start, |s| s.span.start)
                    .unwrap();

                while pos < end {
                    let token = merged_tokens.next().unwrap();
                    pos = token.span.end;
                    stack.push(Node {
                        kind: NodeKind::Token(token.kind),
                        span: token.span,
                        children: 0..0,
                    });
                }

                start_idx
            };

            let start = arena.len() as u32;
            arena.extend_from_slice(&stack[start_idx..]);
            let end = arena.len() as u32;

            stack.truncate(start_idx);
            stack.push(Node {
                kind: NodeKind::Tree(span.kind),
                span: span.span,
                children: start..end,
            });
        }

        assert_eq!(stack.len(), 1);
        stack.pop().unwrap()
    }

    fn checkpoint(&self) -> ParserCheckpoint {
        ParserCheckpoint {
            pos: self.pos,
            spans_len: self.spans.len().try_into().unwrap(),
            errors_len: self.errors.len().try_into().unwrap(),
        }
    }

    fn restore(&mut self, checkpoint: ParserCheckpoint) {
        let ParserCheckpoint {
            pos,
            spans_len,
            errors_len,
        } = checkpoint;

        self.pos = pos;

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
        debug_assert!(!tree.span.is_empty(), "Span is empty {tree:?}");
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

    fn error(&mut self, err: impl ToString) {
        let err = err.to_string();
        let end = self.tokens.get(self.pos as usize).map_or(0, |s| s.span.end);
        self.errors.push(ParseError {
            span: StrSpan {
                start: end,
                end: end,
            },
            err,
        });
    }

    fn advance(&mut self) {
        assert!(!self.eof());
        self.pos += 1;
    }

    fn try_advance(&mut self) {
        if !self.eof() {
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
            self.error(format!("Expected '{kind:?}'"));
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

pub fn parse<'a>(arena: &mut Vec<Node>, text: &str) -> (Node, Vec<ParseError>) {
    let mut lexer = Lexer::new(text.as_bytes());
    let (tokens, trivia) = lex(&mut lexer);
    let mut parser = Parser::new(text, tokens, trivia);
    _ = file(&mut parser);
    let root = parser.build_tree(arena);

    (root, parser.errors)
}

// #[global_allocator]
// static GLOBAL: ProfiledAllocator<std::alloc::System> =
//     ProfiledAllocator::new(std::alloc::System, 30);

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

    let mut arena = Vec::new();

    if true {
        let input = input.repeat(10000);

        bench("whole", input.len(), || {
            let mut lexer = Lexer::new(input.as_bytes());
            let (tokens, trivia) = bench("lex", input.len(), || lex(&mut lexer));
            // println!("{tokens:#?}\n{trivia:#?}");
            let mut parser = Parser::new(&input, tokens, trivia);
            bench("parse", input.len(), || file(&mut parser));
            // println!("Spans {:#?}\nErrors {:#?}", &parser.spans, &parser.errors);
            bench("build", input.len(), || parser.build_tree(&mut arena));
        });
    } else {
        let (cst, errors) = parse(&mut arena, &input);
        let mut buf = String::new();
        cst.print(&mut buf, &input, &arena, &mut errors.iter(), 0);
        println!("{buf}");
    }

    // profiling::finish_frame!();
}

fn bench<T>(name: &str, len_bytes: usize, fun: impl FnOnce() -> T) -> T {
    let start = std::time::Instant::now();
    let res = std::hint::black_box(fun());
    let elapsed = start.elapsed().as_secs_f64();

    println!(
        "{name:8} {:.2} ms/MiB",
        (elapsed * 1000.0 * 1024.0 * 1024.0) / len_bytes as f64
    );
    res
}
