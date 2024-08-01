pub mod lexer;
pub mod parser;

use std::u16;

use lexer::Lexer;
use parser::Parser;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpanStart(pub u32);

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeKind(pub std::num::NonZeroU16);

impl NodeKind {
    pub const fn new(raw: u16) -> NodeKind {
        match std::num::NonZeroU16::new(raw) {
            Some(a) => NodeKind(a),
            None => panic!("TreeKind cannot have value 0"),
        }
    }

    pub const fn raw(self) -> u16 {
        self.0.get()
    }
}

impl From<NodeKind> for u16 {
    fn from(value: NodeKind) -> Self {
        value.0.get()
    }
}

impl From<u16> for NodeKind {
    fn from(value: u16) -> Self {
        NodeKind::new(value)
    }
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeEvent {
    pub kind: NodeKind,
    pub max_lookahead: u16,
    pub size_or_start_or_children: u32,
}

#[derive(Clone)]
pub struct Language {
    pub lexer_entry: fn(&mut Lexer) -> Option<NodeEvent>,
    pub parser_entry: fn(&mut Parser) -> bool,
    pub nodes: LanguageNodes,
}

/// The TreeKind values ocurring in a grammar are laid out in a specific order.
/// This struct describes the ends (exclusive) of their respective TreeKind values.
///
///```ignore
/// 0             - reserved None value
/// skip tokens   - 0..skip_tokens_end
/// normal tokens - skip_tokens_end..tokens_end
/// tree kinds    - tokens_end..rules_end
///```
#[derive(Clone)]
pub struct LanguageNodes {
    skip_bound: u16,
    token_bound: u16,
    total_bound: u16,
    names: &'static [&'static str],
}

impl LanguageNodes {
    pub fn is_skip(&self, kind: NodeKind) -> bool {
        kind.raw() < self.skip_bound
    }

    pub fn is_token(&self, kind: NodeKind) -> bool {
        kind.raw() < self.token_bound
    }

    pub fn is_rule(&self, kind: NodeKind) -> bool {
        kind.raw() >= self.token_bound
    }

    pub fn is_valid(&self, kind: NodeKind) -> bool {
        kind.raw() < self.total_bound
    }

    pub fn name(&self, kind: NodeKind) -> Option<&'static str> {
        self.names.get(kind.raw() as usize).copied()
    }
}
