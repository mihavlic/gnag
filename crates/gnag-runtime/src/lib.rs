pub mod lexer;
pub mod parser;
pub mod trace;

mod resetable_slice;

use core::panic;
use std::{borrow::Borrow, u16};

use lexer::Lexer;
use parser::Parser;
use trace::{PostorderTrace, Tokens};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeType {
    Token = 0,
    Nonterminal,
}

impl From<u16> for NodeType {
    fn from(value: u16) -> NodeType {
        match value {
            0 => NodeType::Token,
            1 => NodeType::Nonterminal,
            _ => panic!("Invalid value"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeMeta {
    Skip = 0,
    Word,
    Error,
    None,
}

impl From<u16> for NodeMeta {
    fn from(value: u16) -> NodeMeta {
        match value {
            0 => NodeMeta::Skip,
            1 => NodeMeta::Word,
            2 => NodeMeta::Error,
            _ => panic!("Invalid value"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Bit packed syntax node metadata
///
/// 13b index | 1b NodeMeta | 2b TokenType
pub struct NodeKind(pub std::num::NonZeroU16);

impl NodeKind {
    pub const fn new(index: u16, kind: NodeType, meta: NodeMeta) -> NodeKind {
        assert!(index < ((1 << 13) - 1), "Index too high");

        // invert the index to turn 0 to MAX
        let index = !index;
        let kind = kind as u16;
        let meta = meta as u16;

        let raw = (index << 3) | (kind << 2) | meta;

        match std::num::NonZeroU16::new(raw) {
            Some(a) => NodeKind(a),
            None => unreachable!(),
        }
    }

    #[inline]
    pub const fn get_index(self) -> u16 {
        !self.0.get() >> 3
    }

    #[inline]
    pub const fn is_kind(self, kind: NodeType) -> bool {
        ((self.0.get() >> 2) & 0b1) == (kind as u16)
    }

    #[inline]
    pub const fn is_meta(self, meta: NodeMeta) -> bool {
        (self.0.get() & 0b11) == (meta as u16)
    }

    #[inline]
    pub const fn is_skip(self) -> bool {
        self.is_meta(NodeMeta::Skip)
    }

    #[inline]
    pub const fn is_token(self) -> bool {
        self.is_kind(NodeType::Token)
    }

    #[inline]
    pub const fn is_nonterminal(self) -> bool {
        self.is_kind(NodeType::Nonterminal)
    }

    pub fn name<T>(self, language: T) -> &'static str
    where
        T: Borrow<Language>,
    {
        language.borrow().name(self)
    }
}

#[test]
fn test_node_kind() {
    for &index in &[0, 1, 2, (1 << 13) - 1] {
        for &kind in &[NodeType::Token, NodeType::Nonterminal] {
            for &meta in &[NodeMeta::Skip, NodeMeta::Word, NodeMeta::Error] {
                let node = NodeKind::new(index, kind, meta);
                assert_eq!(node.get_index(), index);
                assert!(node.is_kind(kind));
                assert!(node.is_meta(meta));
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeEvent {
    pub kind: NodeKind,
    pub max_lookahead: u16,
    /// 32 bit integer with context-specific meaning:
    /// * postorder trace:
    ///     * token - size in bytes of token
    ///     * nonterminal - index in trace of the start of this nonterminal
    /// * preorder trace:
    ///     * token - size in bytes of token
    ///     * nonterminal - number of direct children of this nonterminal
    pub data: u32,
}

#[derive(Clone)]
pub struct Language {
    pub lexer_entry: fn(&mut Lexer) -> Option<NodeKind>,
    pub parser_entry: fn(&mut Parser) -> bool,
    pub names: &'static [&'static str],
}

impl Language {
    pub fn lex_all(&self, bytes: &[u8]) -> Tokens {
        self.lex_all_into(bytes, Vec::new())
    }
    pub fn parse_all(&self, tokens: &Tokens) -> PostorderTrace {
        self.parse_all_into(tokens, Vec::new())
    }
    pub fn lex_all_into(&self, bytes: &[u8], vec: Vec<NodeEvent>) -> Tokens {
        let mut vec = vec;
        vec.clear();

        let mut l = Lexer::new(bytes);
        while let Some(next) = l.lex_next(self) {
            vec.push(next);
        }

        Tokens::from_raw(vec)
    }
    pub fn parse_all_into(&self, tokens: &Tokens, vec: Vec<NodeEvent>) -> PostorderTrace {
        let mut p = Parser::new(tokens.get_raw(), vec);
        (self.parser_entry)(&mut p);
        p.finish()
    }
    pub fn name(&self, kind: NodeKind) -> &'static str {
        self.names[kind.get_index() as usize]
    }
}
