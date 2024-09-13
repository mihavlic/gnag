use std::{fmt::Display, ops::Deref};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Span {
    start: u32,
    end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Span {
        Self { start, end }
    }
    pub fn at(pos: u32) -> Span {
        Self {
            start: pos,
            end: pos,
        }
    }
    pub fn empty() -> Span {
        Self { start: 0, end: 0 }
    }
    pub fn is_empty(self) -> bool {
        self.start >= self.end
    }
    #[track_caller]
    pub fn as_str(self, src: &str) -> &str {
        &src[self.start as usize..self.end as usize]
    }
    #[track_caller]
    pub fn as_bytes(self, src: &[u8]) -> &[u8] {
        &src[self.start as usize..self.end as usize]
    }
    pub fn contains(self, pos: u32) -> bool {
        self.start <= pos && pos < self.end
    }
    /// Checks whether another span is fully covered by this one, empty spans are never covered.
    pub fn contains_span(self, span: Span) -> bool {
        (span.start < span.end) && (span.start >= self.start) && (span.end <= self.end)
    }
    /// Checks whether another span overlaps with this one. Empty ranges never overlap.
    pub fn overlaps(self, span: Span) -> bool {
        (self.start < span.end) && (span.start < self.end)
    }
    pub fn start(self) -> u32 {
        self.start
    }
    pub fn end(self) -> u32 {
        self.end
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Spanned<T> {
        Spanned { inner: value, span }
    }
    pub fn with_span(self, span: Span) -> Spanned<T> {
        Self {
            inner: self.inner,
            span,
        }
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
