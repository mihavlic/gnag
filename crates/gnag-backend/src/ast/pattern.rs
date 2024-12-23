use std::{
    fmt::Write,
    ops::{BitAnd, BitOr},
    rc::Rc,
};

use gnag_runtime::lexer::{ByteSet, CharacterClass};

use crate::{
    backend::grammar::{Grammar, RuleHandle},
    span::Span,
};

use super::{
    display::{ByteExt, ByteSliceExt},
    Ident, RcBytes, RcString,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NotPattern {
    Byte(u8),
    Unicode(char),
    ByteSet(Rc<ByteSet>),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    Token(RuleHandle),
}

impl NotPattern {
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write, cx: &Grammar) -> std::fmt::Result {
        match *self {
            NotPattern::Byte(a) => write!(buf, "Byte({})", std::ascii::escape_default(a)),
            NotPattern::Unicode(a) => write!(buf, "Unicode({a})"),
            NotPattern::ByteSet(ref a) => write!(buf, "ByteSet({a})"),
            NotPattern::CharacterClass { class, unicode } => {
                write!(buf, "{class:?}(")?;
                if unicode {
                    write!(buf, " unicode")?;
                }
                write!(buf, ")")
            }
            NotPattern::Token(a) => write!(buf, "Token({})", a.name(cx)),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AnyPattern {
    Byte,
    Unicode,
    Token,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ConsumeUntil {
    Byte(u8),
    Sequence(RcBytes),
}

impl ConsumeUntil {
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write) -> std::fmt::Result {
        match self {
            ConsumeUntil::Byte(a) => write!(buf, "Byte({})", a.display()),
            ConsumeUntil::Sequence(a) => write!(buf, "Sequence({})", a.display()),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ComparisonKind {
    /// max_precedence_group < current_precedence_group
    ///
    /// Used for left asociativity (after matching this group, cannot match it again in its recursive right hand side)
    Lower,
    /// max_precedence_group <= current_precedence_group
    ///
    /// Used for right asociativity (after matching this group, will match it again in its recursive right hand side)
    LowerEqual,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Transition {
    Error,
    // mixed
    Rule(RuleHandle),
    Not(NotPattern),
    Any(AnyPattern),
    // lexer
    ByteSet(Rc<ByteSet>),
    Bytes(RcBytes),
    CharacterClass {
        class: CharacterClass,
        unicode: bool,
    },
    StringLike {
        delimiter: u8,
    },
    ConsumeUntil {
        until: ConsumeUntil,
        inclusive: bool,
    },
    Keyword(RcBytes),
    // parser
    PrattRule(RuleHandle, u32),
    CompareBindingPower(ComparisonKind, u32),
    // parse state control
    SaveState,
    RestoreState,
    CloseSpan(RuleHandle),
    Return(bool),
    LexerReturn(Option<RuleHandle>),
    // error handling
    EmitError(RcString),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TransitionEffects {
    Fallible,
    Infallible,
    Noreturn,
}

impl TransitionEffects {
    pub fn can_fail(self) -> bool {
        matches!(self, TransitionEffects::Fallible)
    }
    pub fn can_succeed(self) -> bool {
        !matches!(self, TransitionEffects::Noreturn)
    }
}

impl Transition {
    pub fn to_pattern(self, span: Span) -> Pattern {
        Pattern {
            kind: PatternKind::Transition(self),
            span,
            children: vec![],
        }
    }
    pub fn to_kind(self) -> PatternKind {
        PatternKind::Transition(self)
    }
    pub fn effects(&self) -> TransitionEffects {
        match self {
            Transition::Error
            | Transition::ByteSet(_)
            | Transition::Bytes(_)
            | Transition::Keyword(_)
            | Transition::Rule(_)
            | Transition::PrattRule(..)
            | Transition::CompareBindingPower(..)
            | Transition::Any(_)
            | Transition::Not(_)
            | Transition::CharacterClass { .. }
            | Transition::StringLike { .. }
            | Transition::ConsumeUntil { .. } => TransitionEffects::Fallible,
            Transition::SaveState
            | Transition::RestoreState
            | Transition::CloseSpan(_)
            | Transition::EmitError(_) => TransitionEffects::Infallible,
            Transition::Return(_) | Transition::LexerReturn(_) => TransitionEffects::Noreturn,
        }
    }
    pub fn advances_parser(&self) -> bool {
        match self {
            Transition::Error
            | Transition::ByteSet(_)
            | Transition::Bytes(_)
            | Transition::Rule(_)
            | Transition::PrattRule(_, _)
            | Transition::Any(_)
            | Transition::Not(_)
            | Transition::CharacterClass { .. }
            | Transition::StringLike { .. }
            | Transition::ConsumeUntil { .. } => true,
            Transition::Keyword(_)
            | Transition::CompareBindingPower(..)
            | Transition::SaveState
            | Transition::RestoreState
            | Transition::CloseSpan(_)
            | Transition::Return(_)
            | Transition::LexerReturn(_)
            | Self::EmitError(_) => false,
        }
    }
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write, cx: &Grammar) -> std::fmt::Result {
        match *self {
            Transition::Error => write!(buf, "Error"),
            Transition::Rule(a) => write!(buf, "Rule({})", a.name(cx)),
            Transition::Not(ref a) => {
                write!(buf, "Not")?;
                a.display_into(buf, cx)
            }
            Transition::Any(ref a) => {
                write!(buf, "Any({a:?})")
            }
            Transition::ByteSet(ref a) => {
                write!(buf, "ByteSet({a})")
            }
            Transition::Bytes(ref a) => write!(buf, "Bytes({})", a.display()),
            Transition::CharacterClass { class, unicode } => {
                let kind = match unicode {
                    true => "unicode",
                    false => "ascii",
                };
                write!(buf, "{class:?}({kind})")
            }
            Transition::StringLike { delimiter } => {
                write!(buf, "StringLike({})", delimiter.display())
            }
            Transition::ConsumeUntil {
                ref until,
                inclusive,
            } => {
                write!(buf, "ConsumeUntil")?;
                until.display_into(buf)?;
                let kind = match inclusive {
                    true => "inclusive",
                    false => "exclusive",
                };
                write!(buf, "[{kind}]")
            }
            Transition::Keyword(ref a) => {
                write!(buf, "Keyword({})", a.display())
            }
            Transition::PrattRule(a, bp) => write!(buf, "PrattRule({}, {})", a.name(cx), bp),
            Transition::CompareBindingPower(kind, a) => {
                write!(buf, "CompareBindingPower({kind:?}, {a})")
            }
            Transition::SaveState => write!(buf, "SaveState"),
            Transition::RestoreState => write!(buf, "RestoreState"),
            Transition::CloseSpan(a) => write!(buf, "CloseSpan({})", a.name(cx)),
            Transition::Return(a) => write!(buf, "Return({a})"),
            Transition::LexerReturn(a) => {
                let name = match a {
                    Some(a) => a.name(cx),
                    None => "None",
                };
                write!(buf, "LexerReturn({name})")
            }
            Transition::EmitError(ref a) => write!(buf, "EmitError({a})"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Group {
    Sequence { explicit: bool },
    Choice,
    Loop,
    OneOrMore,
    Maybe,

    InlineCall { name: Ident },
}

impl Group {
    pub fn to_pattern(self, children: Vec<Pattern>, span: Span) -> Pattern {
        Pattern {
            kind: PatternKind::Group(self),
            span,
            children,
        }
    }
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write) -> std::fmt::Result {
        match self {
            Group::Sequence { explicit: _ } => write!(buf, "Sequence"),
            Group::Choice => write!(buf, "Choice"),
            Group::Loop => write!(buf, "Loop"),
            Group::OneOrMore => write!(buf, "OneOrMore"),
            Group::Maybe => write!(buf, "Maybe"),
            Group::InlineCall { name } => write!(buf, "InlineCall({name})"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum PatternKind {
    UnresolvedIdent(RcString),
    UnresolvedLiteral(RcBytes),

    InlineParameter(u32),
    Pratt(Rc<[RuleHandle]>),

    Transition(Transition),
    Commit,

    Group(Group),
}

impl PatternKind {
    pub fn to_pattern(self, span: Span) -> Pattern {
        Pattern {
            kind: self,
            span,
            children: vec![],
        }
    }
    pub fn is_group(&self) -> bool {
        matches!(self, PatternKind::Group(_))
    }
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write, cx: &Grammar) -> std::fmt::Result {
        match self {
            PatternKind::UnresolvedIdent(a) => write!(buf, "UnresolvedIdent({a})"),
            PatternKind::UnresolvedLiteral(a) => {
                write!(buf, "UnresolvedLiteral({})", a.display())
            }
            PatternKind::InlineParameter(a) => write!(buf, "InlineParameter({a})"),
            PatternKind::Pratt(_) => write!(buf, "Pratt"),
            PatternKind::Transition(a) => a.display_into(buf, cx),
            PatternKind::Commit => write!(buf, "Commit"),
            PatternKind::Group(g) => g.display_into(buf),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Pattern {
    kind: PatternKind,
    span: Span,
    children: Vec<Pattern>,
}

impl Pattern {
    pub fn new_leaf(kind: PatternKind, span: Span) -> Pattern {
        assert!(!kind.is_group());
        Pattern {
            kind,
            span,
            children: vec![],
        }
    }
    pub fn new_group(kind: PatternKind, span: Span, children: Vec<Pattern>) -> Pattern {
        assert!(kind.is_group());
        Pattern {
            kind,
            span,
            children,
        }
    }
    pub fn take(&mut self) -> Pattern {
        std::mem::replace(self, Pattern::error(self.span()))
    }
    pub fn empty(span: Span) -> Pattern {
        Group::Sequence { explicit: false }.to_pattern(vec![], span)
    }
    pub fn error(span: Span) -> Pattern {
        Transition::Error.to_pattern(span)
    }
    pub fn set_kind(&mut self, kind: PatternKind) -> PatternKind {
        if !kind.is_group() {
            self.children = Vec::new();
        }
        std::mem::replace(&mut self.kind, kind)
    }
    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }
    pub fn to_sequence(&mut self, explicit: bool) -> &mut Vec<Pattern> {
        match &mut self.kind {
            PatternKind::Group(Group::Sequence {
                explicit: is_explicit,
            }) => {
                *is_explicit |= explicit;
            }
            _ => {
                *self = Group::Sequence { explicit }.to_pattern(vec![self.take()], self.span());
            }
        }

        return self.children_vec_mut();
    }
    pub fn to_choice(&mut self) -> &mut Vec<Pattern> {
        match &mut self.kind {
            PatternKind::Group(Group::Choice) => {}
            _ => {
                *self = Group::Choice.to_pattern(vec![self.take()], self.span());
            }
        }

        return self.children_vec_mut();
    }
    fn visit_impl(&self, f: &mut dyn FnMut(&Pattern)) {
        if self.kind.is_group() {
            for child in &self.children {
                child.visit_impl(f);
            }
        }
        f(self)
    }
    pub fn visit(&self, mut f: impl FnMut(&Pattern)) {
        self.visit_impl(&mut f)
    }
    fn visit_mut_impl(&mut self, f: &mut dyn FnMut(&mut Pattern)) {
        if self.kind.is_group() {
            for child in &mut self.children {
                child.visit_mut_impl(f);
            }
        }
        f(self)
    }
    pub fn visit_mut(&mut self, mut f: impl FnMut(&mut Pattern)) {
        self.visit_mut_impl(&mut f)
    }
    pub fn kind(&self) -> &PatternKind {
        &self.kind
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn children(&self) -> &[Pattern] {
        if !self.kind.is_group() {
            debug_assert!(self.children.is_empty());
        }
        &self.children
    }
    pub fn children_mut(&mut self) -> &mut [Pattern] {
        if !self.kind.is_group() {
            debug_assert!(self.children.is_empty());
        }
        &mut self.children
    }
    pub fn children_vec_mut(&mut self) -> &mut Vec<Pattern> {
        &mut self.children
    }
    pub fn into_children(self) -> Vec<Pattern> {
        assert!(self.kind.is_group());
        self.children
    }
    pub fn display_into_indent(
        &self,
        buf: &mut dyn std::fmt::Write,
        cx: &Grammar,
        indent: u32,
    ) -> std::fmt::Result {
        for _ in 0..indent {
            write!(buf, "  ")?;
        }
        self.kind().display_into(buf, cx)?;
        write!(buf, "\n")?;
        if let PatternKind::Pratt(children) = self.kind() {
            for handle in children.iter() {
                for _ in 0..(indent + 1) {
                    write!(buf, "  ")?;
                }
                write!(buf, "{}", handle.name(cx))?;
                write!(buf, "\n")?;
            }
        }
        for child in self.children() {
            child.display_into_indent(buf, cx, indent + 1)?;
        }

        Ok(())
    }
    pub fn display_into(&self, buf: &mut dyn std::fmt::Write, cx: &Grammar) -> std::fmt::Result {
        self.display_into_indent(buf, cx, 0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PatternProperties(u8);

impl PatternProperties {
    #![allow(non_upper_case_globals)]
    pub const MatchesEmpty: PatternProperties = PatternProperties(1);
    pub const MatchesFinite: PatternProperties = PatternProperties(2);
    pub const AdvancesParser: PatternProperties = PatternProperties(4);
    pub const CanFail: PatternProperties = PatternProperties(8);
}

impl PatternProperties {
    pub fn contains(self, flag: PatternProperties) -> bool {
        (self.0 & flag.0) == flag.0
    }
    pub fn insert(&mut self, flag: PatternProperties) {
        self.0 |= flag.0;
    }
    pub fn remove(&mut self, flag: PatternProperties) {
        self.0 &= !flag.0;
    }
}

impl BitOr for PatternProperties {
    type Output = PatternProperties;
    fn bitor(self, rhs: Self) -> Self::Output {
        PatternProperties(self.0 | rhs.0)
    }
}

impl BitAnd for PatternProperties {
    type Output = PatternProperties;
    fn bitand(self, rhs: Self) -> Self::Output {
        PatternProperties(self.0 | rhs.0)
    }
}
