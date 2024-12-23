pub mod builtin;
pub mod check;
pub mod grammar;
pub mod lexer;
pub mod lower;
pub mod pratt;
pub mod resolve;

use std::fmt::Display;

use crate::{
    ast::{pattern::Pattern, Ident, RcString},
    error::ErrorAccumulator,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LexerKind {
    Rule,
    Lexer,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ParserKind {
    Rule,
    Pratt,
    PrattChild,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RuleKind {
    Lexer(LexerKind),
    Parser(ParserKind),
    Template,
}

impl RuleKind {
    pub fn lexer() -> RuleKind {
        RuleKind::Lexer(LexerKind::Rule)
    }
    pub fn parser() -> RuleKind {
        RuleKind::Parser(ParserKind::Rule)
    }
    pub fn template() -> RuleKind {
        RuleKind::Template
    }
    pub fn is_lexer(self) -> bool {
        matches!(self, RuleKind::Lexer(_))
    }
    pub fn is_parser(self) -> bool {
        matches!(self, RuleKind::Parser(_))
    }
    pub fn is_template(self) -> bool {
        matches!(self, RuleKind::Template)
    }
    pub fn is_same_toplevel(self, other: RuleKind) -> bool {
        match (self, other) {
            (RuleKind::Lexer(_), RuleKind::Lexer(_)) => true,
            (RuleKind::Parser(_), RuleKind::Parser(_)) => true,
            (RuleKind::Template, RuleKind::Template) => true,
            _ => false,
        }
    }
}

impl Display for RuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            RuleKind::Lexer(_) => "Lexer",
            RuleKind::Parser(_) => "Parser",
            RuleKind::Template => "Template",
        };
        f.write_str(name)
    }
}

#[derive(Clone, Default)]
pub struct Attributes {
    pub root: bool,
    pub atom: bool,
    pub left_assoc: bool,
    pub right_assoc: bool,
    pub skip: bool,
    pub word: bool,
    pub keyword: bool,
}

impl Attributes {
    pub fn from_ast(kind: RuleKind, ast: &[Ident], err: &ErrorAccumulator) -> Attributes {
        let mut result = Attributes::default();

        for attribute in ast {
            let span = attribute.span;
            let set = |field: &mut bool| match field {
                true => err.error_static(span, "Duplicate attribute"),
                false => *field = true,
            };
            let expect_kind = |expected: RuleKind| {
                if !kind.is_same_toplevel(expected) {
                    err.error(span, format!("Not supported in {kind} rules"))
                }
            };
            let must_not = |field: &bool, error: &'static str| {
                if *field {
                    err.error_static(span, error);
                }
            };

            match &*attribute.value {
                "root" => {
                    set(&mut result.root);
                    expect_kind(RuleKind::parser());
                }
                "atom" => {
                    set(&mut result.atom);
                    expect_kind(RuleKind::parser());
                }
                "left_assoc" => {
                    set(&mut result.left_assoc);
                    expect_kind(RuleKind::parser());
                }
                "right_assoc" => {
                    set(&mut result.right_assoc);
                    expect_kind(RuleKind::parser());
                }
                "skip" => {
                    set(&mut result.skip);
                    expect_kind(RuleKind::lexer());
                }
                "word" => {
                    set(&mut result.word);
                    expect_kind(RuleKind::lexer());
                    must_not(&result.keyword, "@word and @keyword are mutually exclusive");
                }
                "keyword" => {
                    set(&mut result.keyword);
                    expect_kind(RuleKind::lexer());
                    must_not(&result.word, "@word and @keyword are mutually exclusive");
                }
                _ => err.error_static(span, "Unknown attribute"),
            }
        }

        result
    }
}

pub struct Rule {
    pub name: RcString,
    pub kind: RuleKind,
    pub attributes: Attributes,
}
