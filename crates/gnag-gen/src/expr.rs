use std::{
    fmt::{Debug, Display, Write},
    rc::Rc,
};

use gnag::{handle::TypedHandle, simple_handle, StrSpan};

use crate::convert::{ConvertedFile, RuleHandle};

#[derive(Clone, Debug)]
pub struct CallExpr {
    pub name: String,
    pub name_span: StrSpan,
    pub parameters: Vec<RuleExpr>,
    // TODO use a more consistent solution
    pub span: StrSpan,
}

simple_handle! {
    pub VariableHandle
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CharacterClass {
    IdentifierStart,
    IdentifierContinue,
    Alphabetic,
    Lowercase,
    Uppercase,
    Digit,
    Hexdigit,
    Alphanumeric,
    Punctuation,
    Whitespace,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ByteBitset([u64; 4]);

impl ByteBitset {
    pub fn set(&mut self, index: u8) {
        let word = &mut self.0[(index >> 6) as usize];
        *word |= 1 << (index & 0b00111111);
    }
    pub fn get(&self, index: u8) -> bool {
        let word = self.0[(index >> 6) as usize];
        let bit = (word >> (index & 0b00111111)) & 1;
        bit != 0
    }
    pub fn raw(&self) -> &[u64; 4] {
        &self.0
    }
}

impl Display for ByteBitset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"")?;
        for i in 0..=255 {
            if self.get(i) {
                write!(f, "{}", std::ascii::escape_default(i))?;
            }
        }
        write!(f, "\"")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotPattern {
    Byte(u8),
    Unicode(char),
    ByteSet(Rc<ByteBitset>),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    Token(RuleHandle),
}

impl NotPattern {
    pub fn display(
        &self,
        f: &mut dyn Write,
        file: &crate::convert::ConvertedFile,
    ) -> std::fmt::Result {
        match self {
            NotPattern::Byte(a) => write!(f, "Byte({})", std::ascii::escape_default(*a)),
            NotPattern::Unicode(a) => write!(f, "Unicode({a})"),
            NotPattern::ByteSet(a) => write!(f, "ByteSet({a})"),
            NotPattern::CharacterClass { class, unicode } => {
                write!(f, "CharacterClass({class:?} unicode: {unicode})")
            }
            NotPattern::Token(a) => write!(f, "Token({})", a.name(file)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnResult {
    RuleOk,
    RuleFail,
    TokenOk(RuleHandle),
    TokenFail,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transition {
    Error,
    // lexer
    ByteSet(Rc<ByteBitset>),
    Bytes(Rc<[u8]>),
    Keyword(Rc<[u8]>),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    // parser
    Rule(RuleHandle),
    PrattRule(RuleHandle, u32),
    CompareBindingPower(u32),
    // builtins
    AnyByte,
    AnyUtf8,
    AnyToken,
    // any of:
    //   ByteSet
    //   Bytes
    //   Keyword
    //   CharacterClass
    //   Rule
    Not(NotPattern),
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
    SaveState(VariableHandle),
    RestoreState(VariableHandle),
    CloseSpan(RuleHandle),
    Return(ReturnResult),
    // does nothing, used to massage statement order for generated code
    // for true always succeeds, for false always fails
    Dummy(bool),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TransitionEffects {
    Fallible,
    Infallible,
    Noreturn,
}

impl Transition {
    pub fn effects(&self) -> TransitionEffects {
        match self {
            Transition::Error
            | Transition::ByteSet(_)
            | Transition::Bytes(_)
            | Transition::Keyword(_)
            | Transition::Rule(_)
            | Transition::PrattRule(_, _)
            | Transition::CompareBindingPower(_)
            | Transition::AnyByte
            | Transition::AnyUtf8
            | Transition::AnyToken
            | Transition::Not(_)
            | Transition::Dummy(_)
            | Transition::CharacterClass { .. }
            | Transition::StringLike { .. }
            | Transition::ConsumeUntilByte { .. }
            | Transition::ConsumeUntilSequence { .. } => TransitionEffects::Fallible,
            Transition::SaveState(_) | Transition::RestoreState(_) | Transition::CloseSpan(_) => {
                TransitionEffects::Infallible
            }
            Transition::Return(_) => TransitionEffects::Noreturn,
        }
    }
    pub fn advances_parser(&self) -> bool {
        match self {
            Transition::Error
            | Transition::ByteSet(_)
            | Transition::Bytes(_)
            | Transition::Rule(_)
            | Transition::PrattRule(_, _)
            | Transition::AnyByte
            | Transition::AnyUtf8
            | Transition::AnyToken
            | Transition::Not(_)
            | Transition::CharacterClass { .. }
            | Transition::StringLike { .. }
            | Transition::ConsumeUntilByte { .. }
            | Transition::ConsumeUntilSequence { .. } => true,
            Transition::Keyword(_)
            | Transition::CompareBindingPower(_)
            | Transition::SaveState(_)
            | Transition::RestoreState(_)
            | Transition::CloseSpan(_)
            | Transition::Return(_)
            | Transition::Dummy(_) => false,
        }
    }
    pub fn display(
        &self,
        f: &mut dyn Write,
        file: &crate::convert::ConvertedFile,
    ) -> std::fmt::Result {
        match *self {
            Transition::Error => write!(f, "Error"),
            Transition::ByteSet(ref a) => write!(f, "ByteSet({a})"),
            Transition::Bytes(ref a) => write!(f, "Bytes({:?})", String::from_utf8_lossy(a)),
            Transition::Keyword(ref a) => write!(f, "Keyword({:?})", String::from_utf8_lossy(a)),
            Transition::Rule(a) => write!(f, "Rule({})", a.name(file)),
            Transition::PrattRule(a, bp) => write!(f, "Pratt({}, {bp})", a.name(file)),
            Transition::CompareBindingPower(power) => write!(f, "CompareBindingPower({power})"),
            Transition::AnyByte => write!(f, "AnyByte"),
            Transition::AnyUtf8 => write!(f, "AnyUnicode"),
            Transition::AnyToken => write!(f, "AnyToken"),
            Transition::Not(ref inner) => {
                write!(f, "Not(")?;
                inner.display(f, file)?;
                write!(f, ")")
            }
            Transition::SaveState(a) => write!(f, "SaveState({})", a.index()),
            Transition::RestoreState(a) => write!(f, "RestoreState({})", a.index()),
            Transition::CloseSpan(a) => write!(f, "CloseSpan({})", a.name(file)),
            Transition::Return(ref value) => write!(f, "Return({value:?})"),
            Transition::Dummy(value) => write!(f, "Dummy({value})"),
            Transition::CharacterClass { class, unicode } => {
                write!(f, "CharacterClass({class:?} unicode: {unicode})")
            }
            Transition::StringLike { delimiter } => {
                write!(f, "StringLike({})", std::ascii::escape_default(delimiter))
            }
            Transition::ConsumeUntilByte { byte, inclusive } => {
                write!(
                    f,
                    "ConsumeUntilByte({} inclusive: {inclusive})",
                    std::ascii::escape_default(byte)
                )
            }
            Transition::ConsumeUntilSequence {
                ref sequence,
                inclusive,
            } => {
                write!(
                    f,
                    "ConsumeUntilSequence({} inclusive: {inclusive})",
                    String::from_utf8_lossy(sequence)
                )
            }
        }
    }
    pub fn display_as_string(
        &self,
        f: &mut dyn Write,
        file: &crate::convert::ConvertedFile,
    ) -> std::fmt::Result {
        let mut buf = String::with_capacity(16);
        self.display(&mut buf, file).unwrap();
        write!(f, "{buf:?}")
    }
}

#[derive(Clone, Debug)]
pub enum RuleExpr {
    Transition(Transition),

    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    Loop(Box<RuleExpr>),
    OneOrMore(Box<RuleExpr>),
    Maybe(Box<RuleExpr>),

    Commit,

    // inline rules (eliminated during lowering)
    InlineParameter(usize),
    InlineCall(Box<CallExpr>),
    UnresolvedIdentifier {
        name: Rc<str>,
        name_span: StrSpan,
    },
    UnresolvedLiteral {
        bytes: Rc<[u8]>,
        span: StrSpan,
    },

    // builtin lowered to control flow
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },

    // pratt
    Pratt(Rc<[RuleHandle]>),
}

impl RuleExpr {
    pub const BUILTIN_RULES: &'static [&'static str] = &["any", "not", "separated_list"];
    pub fn empty() -> RuleExpr {
        RuleExpr::Sequence(vec![])
    }
    pub fn error() -> RuleExpr {
        RuleExpr::Transition(Transition::Error)
    }
    pub fn rule(handle: RuleHandle) -> RuleExpr {
        RuleExpr::Transition(Transition::Rule(handle))
    }
    pub fn close_span(handle: RuleHandle) -> RuleExpr {
        RuleExpr::Transition(Transition::CloseSpan(handle))
    }
    pub fn bytes(bytes: impl Into<Rc<[u8]>>) -> RuleExpr {
        RuleExpr::Transition(Transition::Bytes(bytes.into()))
    }
    pub fn keyword(bytes: impl Into<Rc<[u8]>>) -> RuleExpr {
        RuleExpr::Transition(Transition::Keyword(bytes.into()))
    }
    pub fn visit_nodes_top_down(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_(true, &mut fun)
    }
    pub fn visit_nodes_bottom_up(&self, mut fun: impl FnMut(&RuleExpr)) {
        self.visit_nodes_(false, &mut fun)
    }
    pub fn visit_nodes_top_down_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_mut_(true, &mut fun)
    }
    pub fn visit_nodes_bottom_up_mut(&mut self, mut fun: impl FnMut(&mut RuleExpr)) {
        self.visit_nodes_mut_(false, &mut fun)
    }

    /// Replaces the contents with RuleExpr::empty(), returning the old value
    pub fn take(&mut self) -> RuleExpr {
        std::mem::replace(self, RuleExpr::empty())
    }

    pub fn to_sequence(&mut self) -> &mut Vec<RuleExpr> {
        loop {
            match self {
                RuleExpr::Sequence(vec) => return vec,
                _ => {
                    let mut vec = Vec::with_capacity(2);
                    vec.push(self.take());
                    *self = RuleExpr::Sequence(vec);
                    continue;
                }
            }
        }
    }

    fn visit_nodes_(&self, top_down: bool, fun: &mut dyn FnMut(&RuleExpr)) {
        if top_down {
            fun(self);
        }
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_(top_down, fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_(top_down, fun);
                separator.visit_nodes_(top_down, fun);
            }
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_(top_down, fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &call.parameters {
                    a.visit_nodes_(top_down, fun);
                }
            }
            RuleExpr::Pratt(_)
            | RuleExpr::Transition(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::UnresolvedIdentifier { .. }
            | RuleExpr::UnresolvedLiteral { .. }
            | RuleExpr::Commit => {}
        }
        if !top_down {
            fun(self);
        }
    }
    fn visit_nodes_mut_(&mut self, top_down: bool, fun: &mut dyn FnMut(&mut RuleExpr)) {
        if top_down {
            fun(self);
        }
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_mut_(top_down, fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_mut_(top_down, fun);
                separator.visit_nodes_mut_(top_down, fun);
            }
            RuleExpr::Maybe(a) | RuleExpr::Loop(a) | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_mut_(top_down, fun);
            }
            RuleExpr::InlineCall(call) => {
                for a in &mut call.parameters {
                    a.visit_nodes_mut_(top_down, fun);
                }
            }
            RuleExpr::Pratt(_)
            | RuleExpr::Transition(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::UnresolvedIdentifier { .. }
            | RuleExpr::UnresolvedLiteral { .. }
            | RuleExpr::Commit => {}
        }
        if !top_down {
            fun(self);
        }
    }
    pub fn display(&self, buf: &mut dyn std::fmt::Write, file: &ConvertedFile) {
        self.display_with_indent(buf, 0, file);
    }
    #[allow(unused_must_use)]
    pub fn display_with_indent(
        &self,
        buf: &mut dyn std::fmt::Write,
        indent: u32,
        file: &ConvertedFile,
    ) {
        let print_indent = |buf: &mut dyn std::fmt::Write| {
            for _ in 0..indent {
                write!(buf, "  ");
            }
        };

        let display_slice = |buf: &mut dyn std::fmt::Write, name: &str, exprs: &[RuleExpr]| {
            if !name.is_empty() {
                writeln!(buf, "{name}");
            }
            for expr in exprs {
                expr.display_with_indent(buf, indent + 1, file);
            }
            Ok(())
        };
        let display_nested = |buf: &mut dyn std::fmt::Write, name: &str, expr: &RuleExpr| {
            writeln!(buf, "{name}");
            expr.display_with_indent(buf, indent + 1, file);
            Ok(())
        };

        print_indent(buf);
        match self {
            RuleExpr::Transition(transition) => {
                transition.display(buf, file);
                writeln!(buf)
            }
            RuleExpr::Commit => writeln!(buf, "Commit"),
            RuleExpr::Sequence(a) => display_slice(buf, "Sequence", a),
            RuleExpr::Choice(a) => display_slice(buf, "Choice", a),
            RuleExpr::Loop(a) => display_nested(buf, "Loop", a),
            RuleExpr::OneOrMore(a) => display_nested(buf, "OneOrMore", a),
            RuleExpr::Maybe(a) => display_nested(buf, "Maybe", a),
            RuleExpr::InlineParameter(a) => writeln!(buf, "InlineParameter({a})"),
            RuleExpr::InlineCall(a) => {
                writeln!(buf, "InlineCall(\"{}\")", a.name);
                display_slice(buf, "", &a.parameters)
            }
            RuleExpr::UnresolvedIdentifier { name, name_span: _ } => {
                writeln!(buf, "UnresolvedIdentifier(\"{name}\")")
            }
            RuleExpr::UnresolvedLiteral { bytes, span: _ } => {
                writeln!(buf, "UnresolvedLiteral({:?})", &**bytes)
            }
            RuleExpr::SeparatedList { element, separator } => {
                writeln!(buf, "SeparatedList");
                element.display_with_indent(buf, indent + 1, file);
                separator.display_with_indent(buf, indent + 1, file);
                Ok(())
            }
            RuleExpr::Pratt(rules) => {
                writeln!(buf, "pratt");

                for rule in &**rules {
                    print_indent(buf);
                    writeln!(buf, "  {}", rule.name(file));
                }

                Ok(())
            }
        };
    }
}
