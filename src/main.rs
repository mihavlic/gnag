use std::cell::Cell;

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
enum TreeKind {
    File,
      ErrorTree,
      Meta,
      Tokenizer,
        TokenRule,
      Rule,
        Annotation,
}

use TokenKind::*;
use TreeKind::*;

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

#[derive(Clone, Debug)]
pub struct Tree {
    kind: TreeKind,
    children: Vec<Child>,
}

pub fn parse(text: &str) -> Tree {
    let tokens = lex(text);
    let mut p = Parser::new(tokens);
    file(&mut p);
    p.build_tree()
}

#[macro_export]
macro_rules! format_to {
    ($buf:expr) => ();
    ($buf:expr, $lit:literal $($arg:tt)*) => {
        { let _ = ::std::write!($buf, $lit $($arg)*); }
    };
}

impl Tree {
    fn print(&self, buf: &mut dyn std::fmt::Write, src: &str, level: usize) {
        let indent = "  ".repeat(level);
        format_to!(buf, "{indent}{:?}\n", self.kind);
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

#[derive(Debug)]
enum Event {
    Open { kind: TreeKind },
    Close,
    Advance,
}

#[derive(Clone, Copy)]
struct MarkOpened {
    index: u32,
    pos: u32,
}

#[derive(Clone, Copy)]
struct MarkClosed {
    index: u32,
}

#[derive(Clone, Copy, Debug)]
enum ParseError {
    NoMatch,
    Error,
}

type ParseResult = Result<(), ParseError>;

struct Parser {
    tokens: Vec<Token>,
    pos: u32,
    fuel: Cell<u32>,
    events: Vec<Event>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Parser {
        Parser {
            tokens,
            pos: 0,
            fuel: Cell::new(256),
            events: Vec::new(),
        }
    }

    fn build_tree(self) -> Tree {
        let mut tokens = self.tokens.into_iter();
        let mut events = self.events;

        assert!(matches!(events.pop(), Some(Event::Close)));
        let mut stack = Vec::new();
        for event in events {
            match event {
                Event::Open { kind } => stack.push(Tree {
                    kind,
                    children: Vec::new(),
                }),
                Event::Close => {
                    let tree = stack.pop().unwrap();
                    stack.last_mut().unwrap().children.push(Child::Tree(tree));
                }
                Event::Advance => {
                    let token = tokens.next().unwrap();
                    stack.last_mut().unwrap().children.push(Child::Token(token));
                }
            }
        }

        // println!("{stack:#?}\n\n{:#?}", tokens.clone().collect::<Vec<_>>());

        let tree = stack.pop().unwrap();
        assert!(stack.is_empty());
        assert!(tokens.next().is_none());
        tree
    }

    fn open(&mut self) -> MarkOpened {
        let mark = MarkOpened {
            index: self.events.len() as u32,
            pos: self.pos,
        };
        self.events.push(Event::Open {
            kind: TreeKind::ErrorTree,
        });
        mark
    }

    // fn open_before(&mut self, m: MarkClosed) -> MarkOpened {
    //     let mark = MarkOpened {
    //         // TODO is this correct?
    //         index: m.index + 1,
    //         pos: self.pos,
    //     };
    //     self.events.insert(
    //         m.index as usize,
    //         Event::Open {
    //             kind: TreeKind::ErrorTree,
    //         },
    //     );
    //     mark
    // }

    fn close(&mut self, m: MarkOpened, kind: TreeKind) -> MarkClosed {
        self.events[m.index as usize] = Event::Open { kind };
        self.events.push(Event::Close);
        MarkClosed { index: m.index }
    }

    fn close_advance_with_error(&mut self, m: MarkOpened, error: &str) -> MarkClosed {
        eprintln!("{error}");
        self.advance();
        self.close(m, ErrorTree)
    }

    fn reset(&mut self, m: MarkOpened) {
        self.events.truncate((m.index + 1) as usize);
        self.pos = m.pos;
    }

    fn unopen(&mut self, m: MarkOpened) {
        self.events.truncate((m.index) as usize);
        self.pos = m.pos;
    }

    fn advance(&mut self) {
        assert!(!self.eof());
        self.fuel.set(256);
        self.events.push(Event::Advance);
        self.pos += 1;
    }

    fn advance_with_error(&mut self, error: &str) {
        let m = self.open();
        // TODO: Error reporting.
        // eprintln!("{error}");
        self.advance();
        self.close(m, ErrorTree);
    }

    fn advance_with_error_fmt(&mut self, error: std::fmt::Arguments) {
        let m = self.open();
        // TODO: Error reporting.
        // eprintln!("{error}");
        self.advance();
        self.close(m, ErrorTree);
    }

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

    fn at(&self, kind: TokenKind) -> bool {
        self.nth(0) == kind
    }

    fn at_any(&self, kinds: &[TokenKind]) -> bool {
        kinds.contains(&self.nth(0))
    }

    #[must_use]
    fn eat(&mut self, kind: TokenKind) -> ParseResult {
        if self.at(kind) {
            self.advance();
            ParseResult::Ok(())
        } else {
            ParseResult::Err(ParseError::NoMatch)
        }
    }

    #[must_use]
    fn expect(&mut self, kind: TokenKind) -> ParseResult {
        let cur = self.nth(0);
        if cur == kind {
            self.advance();
            ParseResult::Ok(())
        } else {
            self.advance_with_error_fmt(format_args!("Expected token {kind:?}"));
            ParseResult::Err(ParseError::Error)
        }
    }

    fn match_try(
        &mut self,
        m: MarkOpened,
        kind: TreeKind,
        fun: fn(&mut Parser) -> ParseResult,
    ) -> bool {
        match fun(self) {
            Ok(()) | Err(ParseError::Error) => {
                self.close(m, kind);
                true
            }
            Err(ParseError::NoMatch) => {
                self.reset(m);
                false
            }
        }
    }

    fn match_optional(
        &mut self,
        kind: TreeKind,
        fun: fn(&mut Parser) -> ParseResult,
    ) -> ParseResult {
        let m = self.open();
        let res = fun(self);
        match res {
            Ok(()) | Err(ParseError::Error) => {
                self.close(m, kind);
            }
            Err(ParseError::NoMatch) => {
                self.unopen(m);
                return Ok(());
            }
        }
        res
    }

    fn match_repetition_star(
        &mut self,
        kind: TreeKind,
        fun: fn(&mut Parser) -> ParseResult,
    ) -> ParseResult {
        while !self.eof() {
            let m = self.open();
            let res = fun(self);
            match res {
                Ok(()) | Err(ParseError::Error) => {
                    self.close(m, kind);
                    continue;
                }
                Err(ParseError::NoMatch) => {
                    self.unopen(m);
                    break;
                }
            }
        }
        Ok(())
    }

    fn match_repetition_plus(
        &mut self,
        kind: TreeKind,
        fun: fn(&mut Parser) -> ParseResult,
    ) -> ParseResult {
        let mut first = true;
        while !self.eof() {
            let m = self.open();
            let res = fun(self);
            match res {
                Ok(()) | Err(ParseError::Error) => {
                    first = false;
                    self.close(m, kind);
                    continue;
                }
                Err(ParseError::NoMatch) => {
                    self.unopen(m);
                    break;
                }
            }
        }
        if first {
            // TODO custom recover
            self.advance_with_error_fmt(format_args!("{kind:?} must occur at leats once"));
            return Err(ParseError::Error);
        }
        Ok(())
    }
}

fn file(p: &mut Parser) {
    let m = p.open();
    while !p.eof() {
        let m = p.open();
        if p.match_try(m, Tokenizer, tokenizer) {
            continue;
        }

        p.unopen(m);
        break;
        // p.close_advance_with_error(m, "Unknown patern");
    }
    p.close(m, File);
}

/// ```ignore
/// tokenizer {
///     #[skip] whitespace r"\s+"
///     #[contextual] node 'node'
///     eq '='
///     number r"\d+"
///     hash_string r#"r#*""# 'parse_raw_string'
/// }
/// ```
fn tokenizer(p: &mut Parser) -> ParseResult {
    p.eat(TokenizerKeyword)?;
    p.expect(LCurly)?;

    p.match_repetition_star(TokenRule, token_rule)?;

    p.expect(RCurly)?;
    Ok(())
}

fn meta(p: &mut Parser) -> ParseResult {
    p.eat(Hash)?;
    // commit
    p.expect(LBracket)?;
    p.expect(Ident)?;
    p.expect(RBracket)?;
    Ok(())
}

fn token_rule(p: &mut Parser) -> ParseResult {
    p.match_optional(Meta, meta)?;
    p.eat(Ident)?;
    // commit
    p.eat(Literal).or_else(|_| p.expect(RawLiteral))?;
    let _ = p.eat(Literal);

    Ok(())
}

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
    #[skip] whitespace r"\\\\s+"
    #[contextual] node 'node'
    eq '='
    number r"\\\\d+"
    hash_string r#"r#*""# 'parse_raw_string'
}
"#####;

    let cst = parse(text);
    let mut buf = String::new();
    cst.print(&mut buf, text, 0);
    eprintln!("{buf}");
}
