#![allow(unreachable_code)]

use std::{cell::Cell};

/// ```ignore
/// tokenizer {
///     #[skip] whitespace r"\s+"
///     #[contextual] node 'node'
///     eq '='
///     number r"\d+"
///     hash_string r#"r#*""# 'parse_raw_string'
/// }
///
/// rule function {
///   'fn' ident '(' fn_args ')' '->' type expr
/// }
/// ```

/// Starting code from
///  https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
///  https://github.com/matklad/resilient-ll-parsing/blob/master/src/lib.rs

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[rustfmt::skip]
enum TokenKind {
    Ident, Literal, RawLiteral,
    ErrorToken, Eof,
  
    LParen, RParen, LCurly, RCurly, LBracket, RBracket, LAngle, RAngle,
    TokenizerKeyword, RuleKeyword,
    Hash,
}

#[derive(Clone, Copy, Debug)]
#[rustfmt::skip]
pub enum TreeKind {
    File,
      ErrorTree,
      Meta,
      Tokenizer,
        TokenRule,
      Rule,
        Annotation,
}

use TokenKind::*;

#[derive(Clone, Copy, Debug)]
struct Span {
    start: u32,
    end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}

#[derive(Clone, Copy, Debug)]
struct Token {
    kind: TokenKind,
    span: Span,
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

pub fn parse(text: &str) -> Tree {
    let tokens = lex(text);
    let mut p = Parser::new(tokens);
    _ = file(&mut p);
    p.build_tree()
}

#[macro_export]
macro_rules! format_to {
    ($buf:expr) => ();
    ($buf:expr, $lit:literal $($arg:tt)*) => {
        { let _ = ::std::write!($buf, $lit $($arg)*); }
    };
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
        format_to!(buf, "{indent}{:?}", self.kind);
        if let Some(err) = &self.err {
            format_to!(buf, "'{err}'");
        }
        format_to!(buf, "\n");
        for child in &self.children {
            match child {
                Child::Token(token) => {
                    format_to!(buf, "{indent}  {}\n", token.as_str(src))
                }
                Child::Tree(tree) => tree.print(buf, src, level + 1),
            }
        }
    }
}

fn lex(src: &str) -> Vec<Token> {
    let punctuation = (
        "# ( ) { } [ ] < >",
        [
            Hash, LParen, RParen, LCurly, RCurly, LBracket, RBracket, LAngle, RAngle,
        ],
    );

    let keywords = ("rule tokenizer", [RuleKeyword, TokenizerKeyword]);

    let mut text = src;
    let mut result = Vec::new();
    while !text.is_empty() {
        if let Some(rest) = trim(text, |it| it.is_ascii_whitespace()) {
            text = rest;
            continue;
        }

        let text_orig = text;
        let mut kind = 'kind: {
            for (i, symbol) in punctuation.0.split_ascii_whitespace().enumerate() {
                if let Some(rest) = text.strip_prefix(symbol) {
                    text = rest;
                    break 'kind punctuation.1[i];
                }
            }

            // 'string'
            let mut string_chars = text.chars();
            if string_chars.next().unwrap() == '\'' {
                let mut escaped = false;
                while let Some(c) = string_chars.next() {
                    if c == '\\' {
                        escaped = true;
                        continue;
                    }

                    if c == '\'' && !escaped {
                        text = string_chars.as_str();
                        break 'kind Literal;
                    }

                    escaped = false;
                }
            }

            // r#"escaped string"#
            let mut string_chars = text.chars();
            if string_chars.next().unwrap() == 'r' {
                let mut balance = 0;
                'inner: {
                    while let Some(c) = string_chars.next() {
                        match c {
                            '#' => balance += 1,
                            '"' => break,
                            _ => break 'inner,
                        }
                    }

                    while let Some(c) = string_chars.next() {
                        if c == '"' {
                            if balance == 0 {
                                text = string_chars.as_str();
                                break 'kind RawLiteral;
                            }

                            let mut balance = balance;
                            let mut string_chars = string_chars.clone();
                            while let Some('#') = string_chars.next() {
                                balance -= 1;
                                if balance == 0 {
                                    text = string_chars.as_str();
                                    break 'kind RawLiteral;
                                }
                            }
                        }
                    }
                }
            }

            // ident
            if let Some(rest) = trim(text, name_char) {
                text = rest;
                break 'kind Ident;
            }

            let error_index = text
                .find(|it: char| it.is_ascii_whitespace())
                .unwrap_or(text.len());
            text = &text[error_index..];
            ErrorToken
        };

        // assert that we've consumed _something_
        assert!(text.len() < text_orig.len());

        let token_text = &text_orig[..text_orig.len() - text.len()];
        if kind == Ident {
            for (i, symbol) in keywords.0.split_ascii_whitespace().enumerate() {
                if token_text == symbol {
                    kind = keywords.1[i];
                    break;
                }
            }
        }

        let start = unsafe {
            text_orig
                .as_ptr()
                .offset_from(src.as_ptr())
                .try_into()
                .unwrap()
        };
        let end = unsafe { text.as_ptr().offset_from(src.as_ptr()).try_into().unwrap() };

        result.push(Token {
            kind,
            span: Span::new(start, end),
        })
    }
    return result;

    fn name_char(c: char) -> bool {
        matches!(c, '_' | 'a'..='z' | 'A'..='Z' | '0'..='9')
    }

    fn trim(text: &str, predicate: impl std::ops::Fn(char) -> bool) -> Option<&str> {
        let index = text.find(|it: char| !predicate(it)).unwrap_or(text.len());
        if index == 0 {
            None
        } else {
            Some(&text[index..])
        }
    }
}

#[derive(Clone, Copy)]
struct SpanIndex(u32);

#[derive(Clone)]
struct TreeSpan {
    kind: TreeKind,
    start: u32,
    end: u32,
    // TODO pointer to bump allocator?
    err: Option<String>,
}

pub struct Parser {
    tokens: Vec<Token>,
    pos: u32,
    fuel: Cell<u32>,
    tree: Vec<TreeSpan>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Parser {
        Parser {
            tokens,
            pos: 0,
            fuel: Cell::new(256),
            tree: Vec::new(),
        }
    }

    fn build_tree(self) -> Tree {
        let root = self.tree.first().unwrap();
        assert_eq!(root.start, 0);
        assert_eq!(root.end, self.tokens.len() as u32);

        let tokens = self.tokens.into_iter();
        let mut tree_spans = self.tree.iter();

        // println!("{stack:#?}\n\n{:#?}", tokens.clone().collect::<Vec<_>>());

        // |-A------------|  -- root
        // |  |-b-|   |-c-|  -- intermediate tree nodes
        // |tttttttttttttt|  -- tokens
        let mut stack = Vec::new();
        let mut span_end_stack = Vec::new();

        for (token, i) in tokens.zip(0..) {
            while let Some(peek) = tree_spans.clone().next() {
                // debug_assert!(peek.start <= i);
                if i == peek.start {
                    stack.push(Tree {
                        kind: peek.kind,
                        children: Vec::new(),
                        err: peek.err.clone(),
                    });
                    span_end_stack.push(peek.end - 1);
                    tree_spans.next();
                    continue;
                }
                break;
            }

            let node = stack.last_mut().unwrap();
            node.children.push(Child::Token(token));

            while let Some(end) = span_end_stack.last().copied() {
                if i == end {
                    if stack.len() == 1 {
                        break;
                    }

                    span_end_stack.pop();
                    let node = stack.pop().unwrap();
                    stack.last_mut().unwrap().children.push(Child::Tree(node));
                } else {
                    break;
                }
            }
        }

        let tree = stack.pop().unwrap();
        tree
    }

    fn open(&mut self) -> SpanIndex {
        let len = self.tree.len() as u32;

        self.tree.push(TreeSpan {
            kind: TreeKind::ErrorTree,
            start: self.pos,
            end: self.pos,
            err: None,
        });

        SpanIndex(len)
    }

    fn close(&mut self, m: SpanIndex, kind: TreeKind) {
        let span = &mut self.tree[m.0 as usize];
        span.end = self.pos;
        span.kind = kind;
    }

    fn close_with_err(&mut self, m: SpanIndex, err: impl ToString) {
        self.close_with_err_impl(m, TreeKind::ErrorTree, err.to_string());
    }

    fn close_with_err_kind(&mut self, m: SpanIndex, kind: TreeKind, err: impl ToString) {
        self.close_with_err_impl(m, kind, err.to_string());
    }

    #[doc(hidden)]
    fn close_with_err_impl(&mut self, m: SpanIndex, kind: TreeKind, err: String) {
        let span = &mut self.tree[m.0 as usize];
        span.end = self.pos;
        span.kind = kind;
        span.err = Some(err);
    }

    // fn close_last(&mut self, kind: TreeKind) {
    //     let span = self.tree.last_mut().unwrap();
    //     debug_assert!(span.is_empty(), "Attempt to close span twice");
    //     span.end = self.pos;
    //     span.kind = kind;
    // }

    fn remove(&mut self, m: SpanIndex) {
        let span = &self.tree[m.0 as usize];
        self.pos = span.start;
        self.tree.truncate(m.0 as usize);
    }

    // fn remove_last(&mut self) {
    //     let span = self.tree.pop().unwrap();
    //     debug_assert!(span.is_empty(), "Cannot remove closed span");
    //     self.pos = span.start;
    // }

    fn reset(&mut self, m: SpanIndex) {
        self.tree.truncate((m.0 + 1) as usize);
        let span = &mut self.tree[m.0 as usize];
        span.end = span.start;
        self.pos = span.start;
    }

    // fn reset_last(&mut self) {
    //     let span = self.tree.last_mut().unwrap();
    //     span.end = span.start;
    //     self.pos = span.start;
    // }

    fn advance(&mut self) {
        assert!(!self.eof());
        self.fuel.set(256);
        self.pos += 1;
    }

    #[inline]
    fn eof(&self) -> bool {
        self.pos as usize == self.tokens.len()
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
            ParseResult::NoMatch => {
                self.remove(m);
            }
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
                        // FIXME or ParseResult::Error?
                        // we want optional(repetition_plus) to have the same behaviour as repetition_star
                        return ParseResult::NoMatch;
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
    fn recover(&self, p: &mut Parser);
}

pub struct RecoverUntil<'a>(&'a [TokenKind]);
impl<'a> RecoverMethod for RecoverUntil<'a> {
    #[cold]
    fn recover(&self, p: &mut Parser) {
        let eof = p.eof();
        let at_any = p.at_any(self.0);
        while !(eof || at_any) {
            p.advance()
        }
    }
}

pub struct RecoverStop;
impl RecoverMethod for RecoverStop {
    fn recover(&self, _: &mut Parser) {}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseErr {
    NoMatch,
    Error,
}

pub type ParseResult = Result<(), ParseErr>;


macro_rules! probe {
    (err $err:expr, $($rule:expr),+) => {
        $(
            match $rule {
                ParseResult::Match => {},
                ParseResult::NoMatch => return ParseResult::NoMatch,
                ParseResult::Error => $err,
            }
        )+
    };
}

macro_rules! optional {
    (err $err:expr, $($rule:expr),+) => {
        $(
            match $rule {
                ParseResult::Match | ParseResult::NoMatch => {},
                ParseResult::Error => $err,
            }
        )+
    };
}

macro_rules! expect {
    (err $err:expr, $($rule:expr),+) => {
        $(
            match $rule {
                ParseResult::Match => {},
                ParseResult::NoMatch | ParseResult::Error => $err,
            }
        )+
    };
}

macro_rules! choice {
    (err $err:expr, $($rule:expr),+) => {
        'choice: {
            $(
                match $rule {
                    ParseResult::Match => break 'choice ParseResult::Match,
                    ParseResult::NoMatch => {}
                    ParseResult::Error => {
                        $err;
                        break 'choice ParseResult::Error;
                    },
                }
            )+
            $err;
        }
    };
}

#[allow(non_upper_case_globals)]
trait ParseResultTrait: Into<ParseResult> + Copy {
    const Match: ParseResult = ParseResult::Ok(());
    const NoMatch: ParseResult = ParseResult::Err(ParseErr::NoMatch);
    const Error: ParseResult = ParseResult::Err(ParseErr::Error);
}
impl ParseResultTrait for ParseResult {}

macro_rules! parser_rule {
    ($kind:ident, $function:expr) => {
        #[allow(non_upper_case_globals)]
        pub const $kind: (TreeKind, fn(&mut Parser) -> ParseResult) = (TreeKind::$kind, $function);
    };
}

parser_rule! {File, file}
fn file(p: &mut Parser) -> ParseResult {
    let m = p.open();
    'main: while !p.eof() {
        let m = p.open();
        // TODO put this inside the rule itself
        'err: {
            match tokenizer(p) {
                ParseResult::Match => p.close(m, TreeKind::Tokenizer),
                ParseResult::NoMatch => {
                    // no rules matched
                    RecoverUntil(&[TokenizerKeyword, RuleKeyword]).recover(p);
                    p.close_with_err(m, "Unknown rule");
                }
                ParseResult::Error => break 'err,
            }

            continue 'main;
        }
        RecoverUntil(&[TokenizerKeyword, RuleKeyword]).recover(p);
        p.close_with_err_kind(m, TreeKind::Tokenizer, "Tokenizer error");
        continue 'main;
    }
    p.close(m, TreeKind::File);
    ParseResult::Match
}

// 'tokenizer' '{' TokenRule* '}'
parser_rule! {Tokenizer, tokenizer}
fn tokenizer(p: &mut Parser) -> ParseResult {
    probe! {
        err {return ParseResult::Error},
        p.terminal(TokenizerKeyword)
    }
    expect! {
        err {return ParseResult::Error},
        p.terminal(LCurly),
        p.nonterminal_repetition_star(TokenRule),
        p.terminal(RCurly)
    }
    Ok(())
}

// '#' '[' Ident ']'
parser_rule! {Meta, meta}
fn meta(p: &mut Parser) -> ParseResult {
    probe! {
        err {return ParseResult::Error},
        p.terminal(Hash)
    }
    expect! {
        err {return ParseResult::Error},
        p.terminal(LBracket),
        p.terminal(Ident),
        p.terminal(RBracket)
    }
    Ok(())
}

// Meta? Ident (Literal|RawLiteral) Literal?
parser_rule! {TokenRule, token_rule}
fn token_rule(p: &mut Parser) -> ParseResult {
    let r = RecoverUntil(&[Hash, Ident]);
    optional! {
        err {r.recover(p); return Ok(())},
        p.nonterminal(Meta)
    }
    probe! {
        err {r.recover(p); return Ok(())},
        p.terminal(Ident)
    }
    expect! {
        err {r.recover(p); return Ok(())},
        choice!{
            err {r.recover(p); return Ok(())},
            p.terminal(Literal),
            p.terminal(RawLiteral)
        },
        p.terminal(Literal)
    }
    Ok(())
}

// // 'rule' Ident '{' rule_expr '}'
// parser_rule! {Rule, rule}
// fn rule(p: &mut Parser) -> ParseResult {
//     optional! {
//         ;
//         p.nonterminal(Meta);
//     }
//     probe! {
//         ;
//         p.terminal(Ident);
//     }

//     p.terminal(Literal)
//         .or_else(|_| p.terminal(RawLiteral))
//         .commit()?;
//     p.terminal(Literal).optional()?;
//     Ok(())
// }

// const PARAM_LIST_RECOVERY: &[TokenKind] = &[FnKeyword, LCurly];
// fn param_list(p: &mut Parser) {
//     assert!(p.at(LParen));
//     let m = p.open();

//     p.expect(LParen);
//     while !p.at(RParen) && !p.eof() {
//         if p.at(Name) {
//             param(p);
//         } else {
//             if p.at_any(PARAM_LIST_RECOVERY) {
//                 break;
//             }
//             p.advance_with_error("expected parameter");
//         }
//     }
//     p.expect(RParen);

//     p.close(m, ParamList);
// }

// fn param(p: &mut Parser) {
//     assert!(p.at(Name));
//     let m = p.open();

//     p.expect(Name);
//     p.expect(Colon);
//     type_expr(p);
//     if !p.at(RParen) {
//         p.expect(Comma);
//     }

//     p.close(m, Param);
// }

// fn type_expr(p: &mut Parser) {
//     let m = p.open();
//     p.expect(Name);
//     p.close(m, TypeExpr);
// }

// const STMT_RECOVERY: &[TokenKind] = &[FnKeyword];
// const EXPR_FIRST: &[TokenKind] = &[Int, TrueKeyword, FalseKeyword, Name, LParen];
// fn block(p: &mut Parser) {
//     assert!(p.at(LCurly));
//     let m = p.open();

//     p.expect(LCurly);
//     while !p.at(RCurly) && !p.eof() {
//         match p.nth(0) {
//             LetKeyword => stmt_let(p),
//             ReturnKeyword => stmt_return(p),
//             _ => {
//                 if p.at_any(EXPR_FIRST) {
//                     stmt_expr(p)
//                 } else {
//                     if p.at_any(STMT_RECOVERY) {
//                         break;
//                     }
//                     p.advance_with_error("expected statement");
//                 }
//             }
//         }
//     }
//     p.expect(RCurly);

//     p.close(m, Block);
// }

// fn stmt_let(p: &mut Parser) {
//     assert!(p.at(LetKeyword));
//     let m = p.open();

//     p.expect(LetKeyword);
//     p.expect(Name);
//     p.expect(Eq);
//     expr(p);
//     p.expect(Semi);

//     p.close(m, StmtLet);
// }

// fn stmt_return(p: &mut Parser) {
//     assert!(p.at(ReturnKeyword));
//     let m = p.open();

//     p.expect(ReturnKeyword);
//     expr(p);
//     p.expect(Semi);

//     p.close(m, StmtReturn);
// }

// fn stmt_expr(p: &mut Parser) {
//     let m = p.open();

//     expr(p);
//     p.expect(Semi);

//     p.close(m, StmtExpr);
// }

// fn expr(p: &mut Parser) {
//     expr_rec(p, Eof);
// }

// fn expr_rec(p: &mut Parser, left: TokenKind) {
//     let Some(mut lhs) = expr_delimited(p) else {
//     return;
//   };

//     while p.at(LParen) {
//         let m = p.open_before(lhs);
//         arg_list(p);
//         lhs = p.close(m, ExprCall);
//     }

//     loop {
//         let right = p.nth(0);
//         if right_binds_tighter(left, right) {
//             let m = p.open_before(lhs);
//             p.advance();
//             expr_rec(p, right);
//             lhs = p.close(m, ExprBinary);
//         } else {
//             break;
//         }
//     }
// }

// fn right_binds_tighter(left: TokenKind, right: TokenKind) -> bool {
//     fn tightness(kind: TokenKind) -> Option<usize> {
//         [
//             // Precedence table:
//             [Plus, Minus].as_slice(),
//             &[Star, Slash],
//         ]
//         .iter()
//         .position(|level| level.contains(&kind))
//     }
//     let Some(right_tightness) = tightness(right) else {
//     return false
//   };
//     let Some(left_tightness) = tightness(left) else {
//     assert!(left == Eof);
//     return true;
//   };
//     right_tightness > left_tightness
// }

// fn expr_delimited(p: &mut Parser) -> Option<MarkClosed> {
//     let result = match p.nth(0) {
//         TrueKeyword | FalseKeyword | Int => {
//             let m = p.open();
//             p.advance();
//             p.close(m, ExprLiteral)
//         }
//         Name => {
//             let m = p.open();
//             p.advance();
//             p.close(m, ExprName)
//         }
//         LParen => {
//             let m = p.open();
//             p.expect(LParen);
//             expr(p);
//             p.expect(RParen);
//             p.close(m, ExprParen)
//         }
//         _ => return None,
//     };
//     Some(result)
// }

// fn arg_list(p: &mut Parser) {
//     assert!(p.at(LParen));
//     let m = p.open();

//     p.expect(LParen);
//     while !p.at(RParen) && !p.eof() {
//         if p.at_any(EXPR_FIRST) {
//             arg(p);
//         } else {
//             break;
//         }
//     }
//     p.expect(RParen);

//     p.close(m, ArgList);
// }

// fn arg(p: &mut Parser) {
//     let m = p.open();
//     expr(p);
//     if !p.at(RParen) {
//         p.expect(Comma);
//     }
//     p.close(m, Arg);
// }

fn main() {
    #[rustfmt::skip]
    let text = 
r#####"
tokenizer {
    #[skip] whitespace r"\\\\\\\\\\\\\\\\s+"
    #[contextual] node 'node'
    eq '='
    number r"\\\\\\\\\\\\\\\\d+"
    hash_string r#"r#*""# 'parse_raw_string'
}
"#####;

    let cst = parse(text);
    let mut buf = String::new();
    cst.print(&mut buf, text, 0);
    eprintln!("{buf}");
}
