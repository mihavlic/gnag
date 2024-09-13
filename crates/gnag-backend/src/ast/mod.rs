pub mod build;
pub mod display;
pub mod literal;
pub mod pattern;

use std::rc::Rc;

use crate::{error::ErrorAccumulator, span::Span};

use build::ConvertCx;
use gnag_runtime::trace::PreorderTrace;
use pattern::Pattern;

#[derive(Clone)]
pub struct File {
    pub span: Span,
    pub groups: Vec<RuleGroup>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ItemGroupKind {
    Lexer,
    Parser,
}

#[derive(Clone)]
pub struct RuleGroup {
    pub span: Span,
    pub kind: ItemGroupKind,
    pub items: Vec<Rc<Rule>>,
}

#[derive(Clone)]
pub struct Rule {
    pub span: Span,
    pub name: Ident,
    pub attributes: Vec<Ident>,
    pub parameters: Option<Vec<Ident>>,
    pub body: RuleBody,
}

pub type RcBytes = Rc<[u8]>;
pub type RcString = Rc<str>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ident {
    pub span: Span,
    pub value: RcString,
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.value)
    }
}

#[derive(Clone)]
pub struct Literal {
    pub span: Span,
    pub value: RcBytes,
}

#[derive(Clone)]
pub enum RuleBody {
    Pattern(Pattern),
    Pratt(Pratt),
}

#[derive(Clone)]
pub struct Pratt {
    pub span: Span,
    pub rules: Vec<Rc<Rule>>,
}

pub struct Ast {
    pub file: Option<File>,
}

impl Ast {
    pub fn new(src: &str, trace: &PreorderTrace, err: &ErrorAccumulator) -> Ast {
        let cx = ConvertCx::new(src, err);
        let file = build::build(trace, &cx);

        Self { file }
    }
}
