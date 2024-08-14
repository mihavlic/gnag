use crate::{resetable_slice::ResetableSlice, NodeEvent, NodeKind};

#[derive(Clone, PartialEq, Eq)]
pub struct LexerPosition {
    position: usize,
}

pub struct Lexer<'a> {
    bytes: ResetableSlice<'a, u8>,
    max_position: usize,
}

impl<'a> Lexer<'a> {
    #[inline]
    fn update_max_position(&mut self) {
        let position = self.bytes.get_position();
        self.max_position = std::cmp::max(self.max_position, position);
    }

    #[inline]
    fn advance_trusted(&mut self, count: usize) {
        self.bytes.skip(count);
    }

    #[inline]
    fn peek(&self) -> Option<u8> {
        self.bytes.peek().copied()
    }

    #[inline]
    fn peek_utf8(&self) -> Option<(usize, char)> {
        use bstr::ByteSlice;
        let bstr = self.bytes.remaining().as_bstr();
        bstr.char_indices().next().map(|(_, len, c)| (len, c))
    }
}

impl<'a> Lexer<'a> {
    pub fn new(bytes: &'a [u8]) -> Lexer {
        Lexer {
            bytes: ResetableSlice::new(bytes),
            max_position: 0,
        }
    }

    pub fn save_position(&self) -> LexerPosition {
        let position = self.bytes.get_position().try_into().unwrap();
        LexerPosition { position }
    }

    pub fn restore_position(&mut self, state: LexerPosition) {
        self.update_max_position();
        self.bytes.set_position(state.position);
    }

    pub fn advance(&mut self, count: usize) -> bool {
        debug_assert!(count != 0, "Advancing by 0 is forbidden");

        if count > self.bytes.len() {
            return false;
        } else {
            self.bytes.skip(count);
            return true;
        }
    }

    pub fn advance_at_most(&mut self, count: usize) -> bool {
        debug_assert!(count != 0, "Advancing by 0 is forbidden");

        let count = std::cmp::min(count, self.bytes.len());

        if count == 0 {
            return false;
        } else {
            self.bytes.skip(count);
            return true;
        }
    }

    #[inline]
    pub fn consume_if<F: FnOnce(u8) -> bool>(&mut self, fun: F) -> bool {
        if let Some(peek) = self.peek() {
            if fun(peek) {
                self.bytes.skip(1);
                return true;
            }
        }
        return false;
    }

    #[inline]
    pub fn consume_utf8_if<F: FnOnce(char) -> bool>(&mut self, fun: F) -> bool {
        if let Some((len, peek)) = self.peek_utf8() {
            if fun(peek) {
                self.bytes.skip(len);
                return true;
            }
        }
        return false;
    }

    pub fn finish_token(&mut self, kind: NodeKind) -> NodeEvent {
        self.update_max_position();
        let token_size = self.bytes.get_position();

        self.bytes = ResetableSlice::new(self.bytes.remaining());
        self.max_position = self.max_position.saturating_sub(token_size);

        let max_lookahead = self.max_position.try_into().unwrap_or(u16::MAX);

        NodeEvent {
            kind,
            max_lookahead,
            size_or_start_or_children: token_size.try_into().unwrap(),
        }
    }
}

        }
    }
}
