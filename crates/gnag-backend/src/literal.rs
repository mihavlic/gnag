use crate::{error::ErrorAccumulator, span::Span};

#[derive(Clone)]
struct Lexer<'a> {
    inner: std::iter::Copied<std::slice::Iter<'a, u8>>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a [u8]) -> Lexer {
        Self {
            inner: src.iter().copied(),
        }
    }

    fn peek(&self) -> Option<u8> {
        self.inner.clone().next()
    }

    fn next(&mut self) -> Option<u8> {
        self.inner.next()
    }

    fn byte(&mut self, b: u8) -> bool {
        if self.peek() == Some(b) {
            self.next();
            return true;
        } else {
            return false;
        }
    }

    fn offset(&self, original: &[u8]) -> u32 {
        let original = original.len();
        let smaller = self.inner.len();
        (original - smaller).try_into().unwrap()
    }
}

type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, u8>>;

pub fn extract_literal(src: &[u8], literal_span: Span, out: &mut Vec<u8>, err: &ErrorAccumulator) {
    assert!(
        !src.is_empty(),
        "Lexer could not have produced zero-sized token"
    );

    let error = |l: &Lexer, message: &'static str| {
        let span = Span::at(literal_span.start + l.offset(src));
        err.error_static(span, message);
    };

    let error_owned = |l: &Lexer, message: String| {
        let span = Span::at(literal_span.start + l.offset(src));
        err.error(span, message);
    };

    let mut l = Lexer::new(src);

    let is_raw = l.byte(b'r');

    if !l.byte(b'\'') {
        error(&l, "Expected opening quote");
        return;
    }

    loop {
        match l.next() {
            Some(b'\\') if !is_raw => {
                let copy = l.clone();
                let escaped = match l.next() {
                    Some(b'\\') => b'\\',
                    Some(b'n') => b'\n',
                    Some(b't') => b'\t',
                    Some(b'0') => b'\0',
                    Some(b'\'') => b'\'',
                    Some(b) => {
                        error_owned(
                            &copy,
                            format!(
                                "Unknown character escape '{}'",
                                std::ascii::escape_default(b)
                            ),
                        );
                        continue;
                    }
                    None => continue,
                };

                out.push(escaped);
            }
            Some(b'\'') => break,
            Some(normal) => {
                out.push(normal);
            }
            None => {
                error(&l, "Expected closing quote");
                return;
            }
        }
    }
}
