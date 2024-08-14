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

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ByteBitset(pub [u64; 4]);

#[derive(Clone, Copy)]
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

impl CharacterClass {
    #[inline]
    pub fn matches_ascii(self, b: u8) -> bool {
        match self {
            CharacterClass::IdentifierStart => b == b'_' || b.is_ascii_alphabetic(),
            CharacterClass::IdentifierContinue => b == b'_' || b.is_ascii_alphanumeric(),
            CharacterClass::Alphabetic => b.is_ascii_alphabetic(),
            CharacterClass::Lowercase => b.is_ascii_lowercase(),
            CharacterClass::Uppercase => b.is_ascii_uppercase(),
            CharacterClass::Digit => b.is_ascii_digit(),
            CharacterClass::Hexdigit => b.is_ascii_hexdigit(),
            CharacterClass::Alphanumeric => b.is_ascii_alphanumeric(),
            CharacterClass::Punctuation => b.is_ascii_punctuation(),
            CharacterClass::Whitespace => b.is_ascii_whitespace(),
        }
    }
    #[inline]
    pub fn matches_unicode(self, c: char) -> bool {
        match self {
            CharacterClass::IdentifierStart => todo!(),
            CharacterClass::IdentifierContinue => todo!(),
            CharacterClass::Alphabetic => c.is_alphabetic(),
            CharacterClass::Lowercase => c.is_lowercase(),
            CharacterClass::Uppercase => c.is_uppercase(),
            CharacterClass::Digit => c.is_digit(10),
            CharacterClass::Hexdigit => c.is_digit(16),
            CharacterClass::Alphanumeric => c.is_alphanumeric(),
            CharacterClass::Punctuation => c.is_ascii_punctuation(), // only ascii punctuation
            CharacterClass::Whitespace => c.is_whitespace(),
        }
    }
}

impl ByteBitset {
    #[inline]
    pub fn matches(self, b: u8) -> bool {
        let word = self.0[(b >> 6) as usize];
        let bit = (word >> (b & 0b00111111)) & 1;
        bit != 0
    }
}

pub struct UnicodeSet([std::ops::Range<char>]);

impl UnicodeSet {
    #[inline]
    pub fn matches(&self, c: char) -> bool {
        if let Ok(index) = self.0.binary_search_by_key(&c, |range| range.start) {
            let range = self.0[index].clone();
            range.contains(&c)
        } else {
            false
        }
    }
}

impl<'a> Lexer<'a> {
    pub fn any_byte(&mut self) -> bool {
        self.consume_if(|_| true)
    }
    pub fn byte(&mut self, byte: u8) -> bool {
        self.consume_if(|b| b == byte)
    }
    pub fn not_byte(&mut self, byte: u8) -> bool {
        self.consume_if(|b| b != byte)
    }
    pub fn byte_sequence(&mut self, sequence: &[u8]) -> bool {
        if self.bytes.remaining().starts_with(sequence) {
            self.bytes.skip(sequence.len());
            return true;
        } else {
            return false;
        }
    }
    pub fn byte_set(&mut self, set: ByteBitset) -> bool {
        self.consume_if(|b| set.matches(b))
    }
    pub fn not_byte_set(&mut self, set: ByteBitset) -> bool {
        self.consume_if(|b| !set.matches(b))
    }
    pub fn ascii_class(&mut self, class: CharacterClass) -> bool {
        self.consume_if(|b| class.matches_ascii(b))
    }
    pub fn not_ascii_class(&mut self, class: CharacterClass) -> bool {
        self.consume_if(|b| !class.matches_ascii(b))
    }

    pub fn any_utf8(&mut self) -> bool {
        self.consume_utf8_if(|_| true)
    }
    pub fn utf8(&mut self, char: char) -> bool {
        self.consume_utf8_if(|c| c == char)
    }
    pub fn not_utf8(&mut self, char: char) -> bool {
        self.consume_utf8_if(|c| c != char)
    }
    pub fn utf8_set(&mut self, set: &UnicodeSet) -> bool {
        self.consume_utf8_if(|c| set.matches(c))
    }
    pub fn not_utf8_set(&mut self, set: &UnicodeSet) -> bool {
        self.consume_utf8_if(|c| !set.matches(c))
    }
    pub fn utf8_class(&mut self, class: CharacterClass) -> bool {
        self.consume_utf8_if(|c| class.matches_unicode(c))
    }
    pub fn not_utf8_class(&mut self, class: CharacterClass) -> bool {
        self.consume_utf8_if(|c| !class.matches_unicode(c))
    }

    pub fn keyword(&mut self, sequence: &[u8]) -> bool {
        if self.bytes.get_position() == sequence.len() {
            if self.bytes.inner_slice().starts_with(sequence) {
                return true;
            }
        }
        return false;
    }

    pub fn string_like(&mut self, delimiter: u8) -> bool {
        let pos = self.save_position();
        if !self.byte(delimiter) {
            return false;
        }
        while let Some(peek) = self.peek() {
            self.advance_trusted(1);
            if peek == b'\\' {
                self.advance_trusted(1);
            } else if peek == delimiter {
                return true;
            }
        }
        self.restore_position(pos);
        return false;
    }

    /// Consumes bytes until the ending byte is found or until the end of input.
    pub fn consume_until_byte(&mut self, byte: u8, inclusive: bool) -> bool {
        use bstr::ByteSlice;
        let bytes = self.bytes.remaining();
        let len = match bytes.find_byte(byte) {
            Some(l) => l + inclusive as usize,
            None => bytes.len(),
        };

        if len == 0 {
            return false;
        } else {
            self.advance_trusted(len);
            true
        }
    }

    /// Consumes bytes until the ending byte sequence is found or until the end of input.
    pub fn consume_until_sequence(&mut self, sequence: &[u8], inclusive: bool) -> bool {
        use bstr::ByteSlice;
        let bytes = self.bytes.remaining();
        let len = match bytes.find(sequence) {
            Some(mut offset) => {
                if inclusive {
                    offset += sequence.len();
                }
                offset
            }
            None => bytes.len(),
        };

        if len == 0 {
            return false;
        } else {
            self.advance_trusted(len);
            true
        }
    }
}
