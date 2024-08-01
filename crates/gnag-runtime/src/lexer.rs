use crate::{NodeEvent, NodeKind};

#[repr(C)]
#[derive(Clone, PartialEq, Eq)]
pub struct LexerPosition {
    position: u32,
}

pub struct Lexer<'a> {
    position: u32,
    max_position: u32,
    bytes: &'a [u8],
}

impl<'a> Lexer<'a> {
    pub fn new(bytes: &'a [u8]) -> Lexer {
        Lexer {
            position: 0,
            max_position: 0,
            bytes,
        }
    }

    fn update_max_position(&mut self) {
        self.max_position = std::cmp::max(self.max_position, self.position);
    }

    pub fn save_position(&self) -> LexerPosition {
        LexerPosition {
            position: self.position,
        }
    }

    pub fn restore_position(&mut self, state: LexerPosition) {
        self.update_max_position();
        self.position = state.position;
    }

    pub fn advance(&mut self, count: u32) -> bool {
        debug_assert!(count != 0, "Advancing by 0 is forbidden");

        let new_position = self.position + count;
        if new_position as usize > self.bytes.len() {
            return false;
        } else {
            self.position = new_position;
            return true;
        }
    }

    pub fn finish_token(&mut self, kind: NodeKind) -> NodeEvent {
        self.update_max_position();
        let token_size = self.position;

        self.position = 0;
        self.max_position = self.max_position.saturating_sub(token_size);
        self.bytes = &self.bytes[token_size as usize..];

        let max_lookahead = self.max_position.try_into().unwrap_or(u16::MAX);

        NodeEvent {
            kind,
            max_lookahead,
            size_or_start_or_children: token_size,
        }
    }
}
