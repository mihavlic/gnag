use std::{
    ops::{BitAnd, BitOr},
    rc::Rc,
};

use gnag_runtime::lexer::{ByteSet, CharacterClass};

use crate::{
    handle::{RuleHandle, TokenHandle},
    span::Spanned,
};

#[derive(Clone)]
pub struct Pratt {
    children: Vec<RuleHandle>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NotPattern {
    Byte(u8),
    Unicode(char),
    ByteSet(Rc<ByteSet>),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    Token(TokenHandle),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AnyPattern {
    Byte,
    Unicode,
    Token,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Transition {
    Error,
    // lexer
    ByteSet(Rc<ByteSet>),
    Bytes(Rc<[u8]>),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    Keyword(Rc<[u8]>),
    // parser
    Rule(RuleHandle),
    PrattRule(RuleHandle, u32),
    CompareBindingPower(u32),
    // builtins
    Not(NotPattern),
    Any(AnyPattern),
    StringLike {
        delimiter: u8,
    },
    ConsumeUntilByte {
        byte: u8,
        inclusive: bool,
    },
    ConsumeUntilSequence {
        sequence: Rc<[u8]>,
        inclusive: bool,
    },
    // parse state control
    SaveState,
    RestoreState,
    CloseSpan(RuleHandle),
    Return(bool),
    ReturnToken(Option<TokenHandle>),
}

#[derive(Clone)]
pub enum AstGroup {
    Sequence { explicit: bool },
    Choice,
    Loop,
    OneOrMore,
    Maybe,

    InlineCall,

    // is actually a (Element Separator <commit>)*
    SeparatedList,
    UnresolvedPratt,
}

#[derive(Clone)]
pub enum AstLeaf {
    UnresolvedIdent(Rc<str>),
    UnresolvedLiteral(Rc<[u8]>),
    UnloweredPratt(Box<Pratt>),

    InlineParameter(u32),

    Transition(Transition),
    Commit,
}

#[derive(Clone)]
pub enum AstEvent {
    Leaf(Spanned<AstLeaf>),
    Separator,
    OpenGroup,
    CloseGroup(Spanned<AstGroup>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AstIndex(u32);

#[derive(Clone)]
pub struct Ast {
    tape: Vec<AstEvent>,
}

impl Ast {
    pub fn new() -> Ast {
        Self { tape: Vec::new() }
    }
    pub fn push(&mut self, ast: AstEvent) -> AstIndex {
        let index: u32 = self.tape.len().try_into().unwrap();
        self.tape.push(ast);
        AstIndex(index)
    }
    pub fn get(&self, index: AstIndex) -> Option<&AstEvent> {
        self.tape.get(index.0 as usize)
    }
    // pub fn open_group(&mut self) {
    //     self.tape.push(AstEvent::OpenGroup);
    // }
    // pub fn close_group(&mut self, group: Spanned<AstGroup>) {
    //     self.tape.push(AstEvent::CloseGroup(group));
    // }
    // pub fn push(&mut self, leaf: Spanned<AstLeaf>) {
    //     self.tape.push(AstEvent::Leaf(leaf));
    // }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AstProperties(u8);

impl AstProperties {
    #![allow(non_upper_case_globals)]
    pub const MatchesEmpty: AstProperties = AstProperties(1);
    pub const AdvancesParser: AstProperties = AstProperties(2);
    pub const CanFail: AstProperties = AstProperties(4);
}

impl AstProperties {
    pub fn contains(self, flag: AstProperties) -> bool {
        (self.0 & flag.0) == flag.0
    }
    pub fn insert(&mut self, flag: AstProperties) {
        self.0 |= flag.0;
    }
    pub fn remove(&mut self, flag: AstProperties) {
        self.0 &= !flag.0;
    }
}

impl BitOr for AstProperties {
    type Output = AstProperties;
    fn bitor(self, rhs: Self) -> Self::Output {
        AstProperties(self.0 | rhs.0)
    }
}

impl BitAnd for AstProperties {
    type Output = AstProperties;
    fn bitand(self, rhs: Self) -> Self::Output {
        AstProperties(self.0 | rhs.0)
    }
}
