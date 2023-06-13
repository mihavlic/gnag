mod ast;
pub mod bump;
pub mod handle;

use std::{cell::Cell, ops::Index};

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
enum TokenKind {
    Ident, Literal, RawLiteral, Number,
    ErrorToken, Eof,
  
    LParen, RParen, LCurly, RCurly, LBracket, RBracket, LAngle, RAngle,
    TokenizerKeyword, RuleKeyword,
    At, Comma, Pipe, Question, Plus, Star
}

#[derive(Clone, Copy, Debug)]
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
        CallExpr,
        BinExpr,
        SeqExpr,
        PostExpr,
}

use TokenKind::*;

#[derive(Clone, Copy, Debug)]
pub struct StrSpan {
    pub start: u32,
    pub end: u32,
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
struct Token {
    kind: TokenKind,
    span: StrSpan,
}

impl Token {
    #[inline]
    pub fn as_str(self, src: &str) -> &str {
        &src[self.span.start as usize..self.span.end as usize]
    }
}

#[derive(Clone, Debug)]
enum Child {
    Token(Token),
    Tree(Tree),
}

#[derive(Clone, Debug)]
pub struct Tree {
    kind: TreeKind,
    children: Vec<Child>,
    err: Option<String>,
}

impl Tree {
    fn print(&self, buf: &mut dyn std::fmt::Write, src: &str, level: usize) {
        let indent = "  ".repeat(level);
        _ = write!(buf, "{indent}{:?}", self.kind);
        if let Some(err) = &self.err {
            _ = write!(buf, " '{err}'");
        }
        _ = write!(buf, "\n");
        for child in &self.children {
            match child {
                Child::Token(token) => {
                    _ = write!(buf, "{indent}  {}\n", token.as_str(src));
                }
                Child::Tree(tree) => tree.print(buf, src, level + 1),
            }
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
        self.pos as usize >= self.str.len()
    }

    pub fn current(&self) -> Option<char> {
        self.str[self.pos as usize..].chars().next()
    }

    pub fn next(&mut self) -> Option<char> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let c = self.str[pos..].chars().next().unwrap();
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
        self.str[..pos].chars().rev().next()
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
        let pos = self.pos();
        for fun in funs {
            match fun(self) {
                None => self.restore_pos(pos),
                some => return some,
            }
        }
        None
    }
}

fn lex(l: &mut Lexer) -> Vec<Token> {
    let mut result = Vec::new();
    while !l.is_empty() {
        if !l.consume_while(char::is_whitespace).is_empty() {
            continue;
        }

        let start = l.pos();
        let kind = l
            .choice(&[
                |l| match l.next().unwrap() {
                    '@' => Some(At),
                    ',' => Some(Comma),
                    '|' => Some(Pipe),
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
                    if l.next().unwrap() == '\'' {
                        let mut escaped = false;
                        while let Some(c) = l.next() {
                            if c == '\\' {
                                escaped = true;
                                continue;
                            }

                            if c == '\'' && !escaped {
                                return Some(Literal);
                            }

                            escaped = false;
                        }
                    }
                    None
                },
                |l| {
                    if l.next().unwrap() == 'r' {
                        let mut balance = 0;
                        while let Some(c) = l.next() {
                            match c {
                                '#' => balance += 1,
                                '"' => break,
                                _ => return None,
                            }
                        }

                        while let Some(c) = l.next() {
                            if c == '"' {
                                let mut balance = balance;
                                loop {
                                    if balance == 0 {
                                        return Some(RawLiteral);
                                    }
                                    if let Some('#') = l.next() {
                                        balance -= 1;
                                    } else {
                                        break;
                                    }
                                }
                            }
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

        result.push(Token { kind, span })
    }
    return result;
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SpanStart(u32);

#[derive(Clone, Copy, PartialEq, Eq)]
struct SpanIndex(u32);

struct ParserCheckpoint {
    pos: u32,
    fuel: u32,
    spans_len: u32,
    errors_len: u32,
}

#[derive(Clone)]
struct TreeSpan {
    kind: TreeKind,
    start: u32,
    end: u32,
}

struct ParseError {
    err: String,
    span: SpanIndex,
}

pub struct Parser {
    tokens: Vec<Token>,
    pos: u32,
    fuel: Cell<u32>,
    spans: Vec<TreeSpan>,
    errors: Vec<ParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Parser {
        Parser {
            tokens,
            pos: 0,
            fuel: Cell::new(256),
            spans: Vec::new(),
            errors: Vec::new(),
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
    fn build_tree(self) -> Tree {
        // we operate on reversed iterators so we can build the tree from the root down
        // note that this will make siblings' order reversed, so we need to reverse them back at the end
        // with a Vec::reverse

        let mut tokens: std::iter::Rev<std::vec::IntoIter<Token>> = self.tokens.into_iter().rev();
        let mut errors: std::iter::Peekable<std::iter::Rev<std::vec::IntoIter<ParseError>>> =
            self.errors.into_iter().rev().peekable();
        let mut spans: std::iter::Rev<
            std::iter::Zip<std::slice::Iter<'_, TreeSpan>, std::ops::Range<u32>>,
        > = self.spans.iter().zip(0u32..self.spans.len() as u32).rev();

        // check that the root contains all of the tokens
        let (root, root_index) = spans.next().unwrap();
        assert_eq!(root.start, 0);
        assert_eq!(root.end, tokens.len() as u32);

        // stack of tree spans, the Tree object that we're creating doesn't contain them so
        // we need a separate stack
        let mut span_stack = vec![root];
        let mut stack: Vec<Tree> = {
            let mut root = Tree {
                kind: root.kind,
                children: Vec::new(),
                err: None,
            };
            // try to attach an error to root
            if let Some(ParseError { err: _, span }) = errors.peek() {
                if span.0 == root_index {
                    let error = errors.next().unwrap();
                    root.err = Some(error.err);
                }
            }
            vec![root]
        };

        let mut token_pos = root.end as i32 - 1;

        loop {
            let cur = stack.last_mut().unwrap();
            let cur_span = span_stack.last().unwrap();
            let next = spans.clone().next();

            // remember: we're iterating from the back

            // see what tokens we can safely push as Child::Token into the current node
            let mut limit = cur_span.start as i32;
            if let Some((next, _)) = next {
                // the next node may either be a child or a sibling
                // |-current-node-|
                //    |-next-|
                if next.start >= cur_span.start {
                    debug_assert!(next.end <= cur_span.end);
                    // decrase the limit until the child starts
                    limit = next.end as i32;
                }
            }

            // consume the tokens
            while token_pos >= limit {
                cur.children.push(Child::Token(tokens.next().unwrap()));
                token_pos -= 1;
            }

            // try to enter a child
            if let Some((next, span_index)) = next {
                // same logic for children as before
                if next.start >= cur_span.start {
                    let mut node = Tree {
                        kind: next.kind,
                        children: Vec::new(),
                        err: None,
                    };

                    // try to attach an error
                    if let Some(ParseError { err: _, span }) = errors.peek() {
                        if span.0 == span_index {
                            let error = errors.next().unwrap();
                            node.err = Some(error.err);
                        }
                    }

                    spans.next();
                    span_stack.push(next);
                    stack.push(node);
                    continue;
                }
            }

            // pop the node from the stack, leaving only root
            if stack.len() > 1 {
                span_stack.pop();
                let mut tree = stack.pop().unwrap();
                tree.children.reverse();
                stack.last_mut().unwrap().children.push(Child::Tree(tree));
            } else {
                break;
            }
        }

        let mut tree = stack.pop().unwrap();
        tree.children.reverse();

        tree
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
        SpanStart(self.pos)
    }

    fn close(&mut self, m: SpanStart, kind: TreeKind) -> SpanIndex {
        let index: u32 = self.spans.len().try_into().unwrap();
        self.spans.push(TreeSpan {
            kind,
            start: m.0,
            end: self.pos,
        });
        SpanIndex(index)
    }

    fn close_with_err(&mut self, m: SpanStart, err: impl ToString) {
        self.close_with_err_impl(m, TreeKind::ErrorTree, err.to_string());
    }

    #[doc(hidden)]
    fn close_with_err_impl(&mut self, m: SpanStart, kind: TreeKind, err: String) {
        let span = self.close(m, kind);
        self.errors.push(ParseError { err, span });
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

    fn peek(&self) -> TokenKind {
        self.nth(0)
    }

    fn nth(&self, lookahead: u32) -> TokenKind {
        if self.fuel.get() == 0 {
            panic!("parser is stuck")
        }
        self.fuel.set(self.fuel.get() - 1);
        self.tokens
            .get((self.pos + lookahead) as usize)
            .map_or(TokenKind::Eof, |it| it.kind)
    }

    #[inline]
    fn at(&self, kind: TokenKind) -> bool {
        self.nth(0) == kind
    }

    #[inline]
    fn at_any(&self, kinds: &[TokenKind]) -> bool {
        kinds.contains(&self.nth(0))
    }

    #[must_use]
    fn terminal(&mut self, kind: TokenKind) -> ParseResult {
        if self.at(kind) {
            self.advance();
            ParseResult::Match
        } else {
            ParseResult::NoMatch
        }
    }

    #[must_use]
    fn nonterminal(
        &mut self,
        (kind, fun): (TreeKind, fn(&mut Parser) -> ParseResult),
    ) -> ParseResult {
        let m = self.open();
        let res = fun(self);
        match res {
            ParseResult::Match => {
                self.close(m, kind);
            }
            ParseResult::NoMatch => {}
            ParseResult::Error => {
                self.close_with_err(m, "Error");
            }
        }
        res
    }

    #[must_use]
    fn nonterminal_repetition_star(
        &mut self,
        rule: (TreeKind, fn(&mut Parser) -> ParseResult),
    ) -> ParseResult {
        while !self.eof() {
            match self.nonterminal(rule) {
                ParseResult::Match => { /* continue */ }
                ParseResult::NoMatch => {
                    return ParseResult::Match;
                }
                ParseResult::Error => {
                    return ParseResult::Error;
                }
            }
        }

        ParseResult::Match
    }

    #[must_use]
    fn nonterminal_repetition_plus(
        &mut self,
        (kind, fun): (TreeKind, fn(&mut Parser) -> ParseResult),
    ) -> ParseResult {
        let mut first = true;
        while !self.eof() {
            match self.nonterminal((kind, fun)) {
                ParseResult::Match => { /* continue */ }
                ParseResult::NoMatch => {
                    if first {
                        // FIXME or ParseResult::NoMatch?
                        // we want optional(repetition_plus) to have the same behaviour as repetition_star
                        return ParseResult::Error;
                    } else {
                        return ParseResult::Match;
                    }
                }
                ParseResult::Error => {
                    return ParseResult::Error;
                }
            }
            first = false;
        }

        ParseResult::Match
    }
}

pub trait RecoverMethod {
    fn recover(&self, p: &mut Parser) -> ParseResult;
}

pub struct RecoverUntil<'a>(&'a [TokenKind]);
impl<'a> RecoverMethod for RecoverUntil<'a> {
    #[cold]
    fn recover(&self, p: &mut Parser) -> ParseResult {
        let m = p.open();
        while !(p.eof() || p.at_any(self.0)) {
            p.advance()
        }
        p.close_with_err(m, "Recover until");
        ParseResult::Match
    }
}

pub struct RecoverStop;
impl RecoverMethod for RecoverStop {
    fn recover(&self, _: &mut Parser) -> ParseResult {
        ParseResult::Match
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseErr {
    NoMatch,
    Error,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ParseResult {
    Match,
    NoMatch,
    Error,
}

impl ParseResult {
    fn optional(self) -> Self {
        match self {
            ParseResult::Match => ParseResult::Match,
            ParseResult::NoMatch => ParseResult::Match,
            ParseResult::Error => ParseResult::Error,
        }
    }
}

macro_rules! probe {
    ($p:expr; err $err:expr; $($rule:expr),+) => {
        let checkpoint = $p.checkpoint();
        $(
            match $rule {
                ParseResult::Match => {},
                ParseResult::NoMatch => {
                    $p.restore(checkpoint);
                    return ParseResult::NoMatch;
                },
                ParseResult::Error => {$err;},
            }
        )+
    };
}

// macro_rules! optional {
//     (err $err:expr; $($rule:expr),+) => {
//         $(
//             match $rule {
//                 ParseResult::Match | ParseResult::NoMatch => {},
//                 ParseResult::Error => {$err;},
//             }
//         )+
//     };
// }

macro_rules! expect {
    (err $err:expr; $($rule:expr),+) => {
        $(
            match $rule {
                ParseResult::Match => {},
                ParseResult::NoMatch | ParseResult::Error => {$err;},
            }
        )+
    };
}

macro_rules! choice {
    (err $err:expr; default $default:expr; $($rule:expr),+) => {
        'choice: {
            $(
                match $rule {
                    ParseResult::Match => break 'choice,
                    ParseResult::NoMatch => {}
                    ParseResult::Error => {
                        $err;
                    },
                }
            )+
            $default;
        }
    };
}

macro_rules! parser_rule {
    ($kind:ident, $function:expr) => {
        #[allow(non_upper_case_globals)]
        pub const $kind: (TreeKind, fn(&mut Parser) -> ParseResult) = (TreeKind::$kind, $function);
    };
}

// (Tokenizer | GrammarRule)*
parser_rule! {File, file}
fn file(p: &mut Parser) -> ParseResult {
    'repeat: while !p.eof() {
        let r = RecoverUntil(&[TokenizerKeyword, RuleKeyword]);
        choice!(
            err {r.recover(p); continue 'repeat};
            default {p.try_advance(); r.recover(p); continue 'repeat};
            p.nonterminal(Tokenizer),
            p.nonterminal(SynRule)
        );
    }
    ParseResult::Match
}

// 'tokenizer' '{' TokenRule* '}'
parser_rule! {Tokenizer, tokenizer}
fn tokenizer(p: &mut Parser) -> ParseResult {
    probe! {
        p;
        err return ParseResult::Error;
        p.terminal(TokenizerKeyword)
    }
    expect! {
        err return ParseResult::Error;
        p.terminal(LCurly),
        p.nonterminal_repetition_star(TokenRule),
        p.terminal(RCurly)
    }
    ParseResult::Match
}

// ( Number | Ident )
parser_rule! {AttributeValue, attribute_value}
fn attribute_value(p: &mut Parser) -> ParseResult {
    choice! {
        err return ParseResult::Error;
        default return ParseResult::NoMatch;
        p.terminal(Ident),
        p.terminal(Number)
    }
    ParseResult::Match
}

// Ident ( '(' AttributeValue ')' )?
parser_rule! {AttributeExpr, attribute_expr}
fn attribute_expr(p: &mut Parser) -> ParseResult {
    probe! {
        p;
        err return ParseResult::Error;
        p.terminal(Ident)
    }
    if p.terminal(LParen) == ParseResult::Match {
        expect! {
            err return ParseResult::Error;
            p.nonterminal(AttributeValue),
            p.terminal(RParen)
        }
    }
    ParseResult::Match
}

// '@' Ident ( '(' <separated_list Attribute ','> ')' )?
parser_rule! {Attribute, attribute}
fn attribute(p: &mut Parser) -> ParseResult {
    probe! {
        p;
        err return ParseResult::Error;
        p.terminal(At)
    }
    expect! {
        err return ParseResult::Error;
        p.terminal(Ident)
    }
    if p.terminal(LParen) == ParseResult::Match {
        while !p.eof() {
            match p.nonterminal(AttributeExpr) {
                ParseResult::Match => {}
                ParseResult::NoMatch => break,
                ParseResult::Error => return ParseResult::Error,
            }
            match p.terminal(Comma) {
                ParseResult::Match => {}
                ParseResult::NoMatch => break,
                ParseResult::Error => return ParseResult::Error,
            }
        }
        expect! {
            err return ParseResult::Error;
            p.terminal(RParen)
        }
    }
    ParseResult::Match
}

// Attribute* Ident (Literal | RawLiteral) Literal?
parser_rule! {TokenRule, token_rule}
fn token_rule(p: &mut Parser) -> ParseResult {
    let r = RecoverUntil(&[At, Ident, RCurly]);
    probe! {
        p;
        err return r.recover(p);
        p.nonterminal_repetition_star(Attribute).optional(),
        p.terminal(Ident)
    }
    choice! {
        err return r.recover(p);
        default return r.recover(p);
        p.terminal(Literal),
        p.terminal(RawLiteral)
    }
    expect! {
        err return r.recover(p);
        p.terminal(Literal).optional()
    }
    ParseResult::Match
}

// Attribute* 'rule' Ident Parameters? '{' SynExpr '}'
parser_rule! {SynRule, syn_rule}
fn syn_rule(p: &mut Parser) -> ParseResult {
    let r = RecoverUntil(&[At, Ident, RCurly]);
    probe! {
        p;
        err return r.recover(p);
        p.nonterminal_repetition_star(Attribute),
        p.terminal(RuleKeyword)
    }
    expect! {
        err r.recover(p);
        p.terminal(Ident),
        p.nonterminal(Parameters).optional(),
        p.terminal(LCurly),
        expr(p, 0),
        p.terminal(RCurly)
    }
    ParseResult::Match
}

// '(' <separated_list Ident ','> ')'
parser_rule! {Parameters, parameters}
fn parameters(p: &mut Parser) -> ParseResult {
    let r = RecoverUntil(&[LCurly]);
    probe! {
        p;
        err return r.recover(p);
        p.terminal(LParen)
    }
    while !p.eof() {
        match p.nonterminal(AttributeExpr) {
            ParseResult::Match => {}
            ParseResult::NoMatch => break,
            ParseResult::Error => return r.recover(p),
        }
        match p.terminal(Comma) {
            ParseResult::Match => {}
            ParseResult::NoMatch => break,
            ParseResult::Error => return r.recover(p),
        }
    }
    expect! {
        err return r.recover(p);
        p.terminal(RParen)
    }
    ParseResult::Match
}

/// ```ignore
/// @pratt
/// rule Expr {
///   Ident | Literal | PreExpr | BinExpr | PostExpr
/// }
///
/// rule PreExpr {
///   Attribute Expr
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

fn base_expr(p: &mut Parser) -> ParseResult {
    let m = p.open();
    match p.peek() {
        Ident | Literal => {
            p.advance();
            p.close(m, TreeKind::AtomExpr);
        }
        At => {
            p.advance();
            expect! {
                err return ParseResult::Error;
                // bp table lookup
                expr(p, 4)
            }
            p.close(m, TreeKind::PreExpr);
        }
        LParen => {
            p.advance();
            expect! {
                err return ParseResult::Error;
                // bp table lookup
                expr(p, 0),
                p.terminal(RParen)
            }
            p.close(m, TreeKind::AtomExpr);
        }
        LAngle => {
            p.advance();
            expect! {
                err return ParseResult::Error;
                p.terminal(Ident),
                // bp table lookup
                expr(p, 0),
                p.terminal(RAngle)
            }
            p.close(m, TreeKind::CallExpr);
        }
        _ => return ParseResult::NoMatch,
    }
    ParseResult::Match
}

fn expr(p: &mut Parser, min_bp: u8) -> ParseResult {
    let m = p.open();
    probe! {
        p;
        err return ParseResult::Error;
        base_expr(p)
    }

    'outer: loop {
        // parse postfix
        match p.peek() {
            Question | Plus | Star => {
                // bp table lookup
                let bp = (5, ());
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                p.close(m, TreeKind::PostExpr);
                continue 'outer;
            }
            Pipe => {
                // bp table lookup
                let bp = (2, 1);
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                expect! {
                    err return ParseResult::Error;
                    expr(p, bp.1)
                }

                p.close(m, TreeKind::BinExpr);
                continue 'outer;
            }
            Ident | Literal | LAngle | LParen | At => {
                // bp table lookup
                let bp = (3, ());
                if bp.0 <= min_bp {
                    break;
                }

                let mut first = true;
                while !p.eof() {
                    match expr(p, bp.0) {
                        ParseResult::Match => first = false,
                        ParseResult::NoMatch => break,
                        ParseResult::Error => return ParseResult::Error,
                    }
                }

                if !first {
                    p.close(m, TreeKind::SeqExpr);
                    continue 'outer;
                }
            }
            _ => {}
        }

        break;
    }

    ParseResult::Match
}

pub struct TreeIter<'a> {
    pos: i32,
    tokens: std::iter::Rev<std::vec::IntoIter<Token>>,
    errors: std::iter::Peekable<std::iter::Rev<std::vec::IntoIter<ParseError>>>,
    spans: std::iter::Rev<std::iter::Zip<std::slice::Iter<'a, TreeSpan>, std::ops::Range<u32>>>,
}

enum IterEvent {
    Token(Token),
    OpenTree(TreeKind),
    CloseTree(TreeKind),
}

impl TreeIter {
    fn visit(&mut self, until_start: u32) {
        let cur = stack.last_mut().unwrap();
        let cur_span = span_stack.last().unwrap();
        let next = spans.clone().next();

        // remember: we're iterating from the back

        // see what tokens we can safely push as Child::Token into the current node
        let mut limit = cur_span.start as i32;
        if let Some((next, _)) = next {
            // the next node may either be a child or a sibling
            // |-current-node-|
            //    |-next-|
            if next.start >= cur_span.start {
                debug_assert!(next.end <= cur_span.end);
                // decrase the limit until the child starts
                limit = next.end as i32;
            }
        }

        // consume the tokens
        while token_pos >= limit {
            cur.children.push(Child::Token(tokens.next().unwrap()));
            token_pos -= 1;
        }

        // try to enter a child
        if let Some((next, span_index)) = next {
            // same logic for children as before
            if next.start >= cur_span.start {
                let mut node = Tree {
                    kind: next.kind,
                    children: Vec::new(),
                    err: None,
                };

                // try to attach an error
                if let Some(ParseError { err: _, span }) = errors.peek() {
                    if span.0 == span_index {
                        let error = errors.next().unwrap();
                        node.err = Some(error.err);
                    }
                }

                spans.next();
                span_stack.push(next);
                stack.push(node);
                continue;
            }
        }

        // pop the node from the stack, leaving only root
        if stack.len() > 1 {
            span_stack.pop();
            let mut tree = stack.pop().unwrap();
            tree.children.reverse();
            stack.last_mut().unwrap().children.push(Child::Tree(tree));
        } else {
            break;
        }
    }
}

pub fn parse(text: &str) -> Tree {
    let mut lexer = Lexer::new(text);
    let tokens = lex(&mut lexer);
    let mut parser = Parser::new(tokens);
    _ = parser.nonterminal(File);
    parser.build_tree()
}

fn main() {
    #[rustfmt::skip]
    let text =
r#####"
tokenizer {
    @skip(a(b), c, d) whitespace r##"\\\\\\\\\\\\\\\\s+"##
}

rule a(a, b) {
    (a b)? | c
}
"#####;

    let cst = parse(text);
    let mut buf = String::new();
    cst.print(&mut buf, text, 0);
    eprintln!("{buf}");
}
