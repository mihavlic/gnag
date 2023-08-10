/// The type of a byte offset in a string
// TODO add a feature to change this into a usize
pub type Offset = u32;

/// Use this for human output text spans.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct CodePointPos {
    /// zero-based line index
    pub line: u32,
    /// zero-based column offset relative to the start of the line, unicode code points (variable length)
    pub character: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Utf8Pos {
    /// zero-based line index
    pub line: u32,
    /// zero-based column offset relative to the start of the line, UTF-8 code units - u8
    pub character: u32,
}

impl Utf8Pos {
    pub const fn new(line: u32, character: u32) -> Utf8Pos {
        Self { line, character }
    }
}

impl From<(u32, u32)> for Utf8Pos {
    fn from((line, character): (u32, u32)) -> Self {
        Utf8Pos { line, character }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Utf16Pos {
    /// zero-based line index
    pub line: u32,
    /// zero-based column offset relative to the start of the line, UTF-16 code units - u16
    pub character: u32,
}

impl Utf16Pos {
    pub const fn new(line: u32, character: u32) -> Utf16Pos {
        Self { line, character }
    }
}

impl From<(u32, u32)> for Utf16Pos {
    fn from((line, character): (u32, u32)) -> Self {
        Utf16Pos { line, character }
    }
}

#[derive(Clone, Copy)]
pub struct LineInfo {
    /// index of the line within the file
    pub line: u32,
    /// byte offset of the start of the line
    pub line_start: Offset,
    /// Does the line contain non-ascii characters?
    pub is_unicode: bool,
}

pub struct LineMap {
    lines: Vec<(Offset, bool)>,
}

impl LineMap {
    pub fn new(src: &str) -> Self {
        assert!(src.len() <= Offset::MAX as usize);
        let mut lines = Vec::new();

        let mut prev_end = 0;
        let mut saw_unicode = false;
        let mut bytes = src.bytes().enumerate();

        // utf8 bytes are either encoding an ascii character or are >=128
        // so we can search for ascii characters by interpreting the string as bytes
        // and not getting any false positives

        // TODO use memchr?
        while let Some((mut i, b)) = bytes.next() {
            // we recognize \r\n  \n  \r as newlines
            // the LSP spec does the same
            match b {
                b'\n' | b'\r' => {
                    if b == b'\r' {
                        if let Some((new_i, b'\n')) = bytes.clone().next() {
                            bytes.next();
                            i = new_i;
                        }
                    }
                    lines.push((prev_end, saw_unicode));
                    saw_unicode = false;
                    prev_end = i as Offset + 1;
                }
                _ => {
                    if b >= 128 {
                        saw_unicode = true;
                    }
                }
            }
        }

        lines.push((prev_end, saw_unicode));

        Self { lines }
    }
    /// Returns zero-based Line and Column offset in utf8 code units (u8). Offset is clamped to the end of `src`
    pub fn offset_to_utf8(&self, src: &str, offset: Offset) -> Utf8Pos {
        let offset = Offset::min(offset, src.len() as Offset);

        let LineInfo {
            line,
            line_start,
            is_unicode: _,
        } = self.offset_to_line(offset);

        assert!(src.is_char_boundary(offset as usize));
        let len = self.line_length(src, line);
        let character = (offset - line_start).min(len);

        Utf8Pos {
            line,
            character: character.try_into().unwrap(),
        }
    }
    /// Returns zero-based Line and Column offset in utf16 code units (u16). Offset is clamped to the end of `src`
    pub fn offset_to_utf16(&self, src: &str, offset: Offset) -> Utf16Pos {
        let offset = Offset::min(offset, src.len() as Offset);

        let LineInfo {
            line,
            line_start,
            is_unicode,
        } = self.offset_to_line(offset);

        assert!(src.is_char_boundary(offset as usize));
        let character: u32 = if is_unicode {
            src[line_start as usize..offset as usize]
                .iter_codepoints()
                .map(|len| utf8_bytecount_to_utf16_codeunits(len))
                .sum()
        } else {
            let len = self.line_length(src, line);
            (offset - line_start).min(len).try_into().unwrap()
        };

        Utf16Pos { line, character }
    }
    /// Returns zero-based Line and Column offset in unicode codepoints. Offset is clamped to the end of `src`
    pub fn offset_to_codepoint(&self, src: &str, offset: Offset) -> CodePointPos {
        let offset = Offset::min(offset, src.len() as Offset);

        let LineInfo {
            line,
            line_start,
            is_unicode,
        } = self.offset_to_line(offset);

        assert!(src.is_char_boundary(offset as usize));
        let character: u32 = if is_unicode {
            src[line_start as usize..offset as usize]
                .iter_codepoints()
                .count()
                .try_into()
                .unwrap()
        } else {
            let len = self.line_length(src, line);
            (offset - line_start).min(len).try_into().unwrap()
        };

        CodePointPos { line, character }
    }
    /// Returns the byte offset (in the utf8 string) of the character pointed toby the `pos`.
    ///
    /// Note that this function clamps offsets to the end (one past) of the line. Such an offset would then be converted back to the start of the **next** line!
    pub fn utf8_to_offset(&self, src: &str, pos: Utf8Pos) -> Offset {
        let Utf8Pos { line, character } = pos;
        let (line_start, _is_unicode) = self.lines[line as usize];

        // clamp the offset to this line, zero-sized lines are impossible since a line includes its linebreaking byte sequence
        let end = self.line_end(src, line);
        (line_start + character as Offset).min(end)
    }
    /// Returns the byte offset (in the utf8 string) of the character pointed toby the `pos`.
    ///
    /// Note that this function clamps offsets to the end (one past) of the line. Such an offset would then be converted back to the start of the **next** line!
    pub fn utf16_to_offset(&self, src: &str, pos: Utf16Pos) -> Offset {
        let Utf16Pos { line, character } = pos;
        let (line_start, is_unicode) = self.lines[line as usize];

        if is_unicode {
            let mut pos = line_start;
            let mut remaining_u16 = character;
            for len in self.line_str(src, line).iter_codepoints() {
                if remaining_u16 == 0 {
                    break;
                }
                pos += len as Offset;
                remaining_u16 -= utf8_bytecount_to_utf16_codeunits(len);
            }

            pos
        } else {
            // clamp the offset to this line, zero-sized lines are impossible since a line includes its linebreaking byte sequence
            let end = self.line_end(src, line);
            (line_start + character as Offset).min(end)
        }
    }
    /// Returns the byte offset (in the utf8 string) of the character pointed toby the `pos`.
    ///
    /// Note that this function clamps offsets to the end (one past) of the line. Such an offset would then be converted back to the start of the **next** line!
    pub fn codepoint_to_offset(&self, src: &str, pos: CodePointPos) -> Offset {
        let CodePointPos { line, character } = pos;
        let (line_start, is_unicode) = self.lines[line as usize];

        if is_unicode {
            let mut pos = line_start;
            let mut remaining_unicode = character;

            for len in self.line_str(src, line).iter_codepoints() {
                if remaining_unicode == 0 {
                    break;
                }
                remaining_unicode -= 1;
                pos += len as Offset;
            }

            pos
        } else {
            // clamp the offset to this line, zero-sized lines are impossible since a line includes its linebreaking byte sequence
            let end = self.line_end(src, line);
            (line_start + character as Offset).min(end)
        }
    }
    /// Find the line which contains the offset and return its Offset is clamped to the end of `src`
    pub fn offset_to_line(&self, byte_offset: Offset) -> LineInfo {
        let index = self.lines.binary_search_by_key(&byte_offset, |a| a.0);
        let line = match index {
            Ok(a) => a,
            Err(a) => a - 1,
        };
        let (line_start, is_unicode) = self.lines[line];
        debug_assert!(line_start <= byte_offset);

        LineInfo {
            line: line.try_into().unwrap(),
            line_start,
            is_unicode,
        }
    }
    pub fn line_length(&self, src: &str, line: u32) -> Offset {
        let start = self.line_start(line);
        let end = self.line_end(src, line);
        end - start
    }
    pub fn line_start(&self, line: u32) -> Offset {
        self.lines[line as usize].0
    }
    pub fn line_end(&self, src: &str, line: u32) -> Offset {
        self.lines
            .get((line + 1) as usize)
            .map(|line| line.0)
            .unwrap_or_else(|| src.len().try_into().unwrap())
    }
    pub fn line_str<'a>(&self, src: &'a str, line: u32) -> &'a str {
        let start = self.line_start(line);
        let end = self.line_end(src, line);
        &src[start as usize..end as usize]
    }
}

trait StrExt {
    fn iter_codepoints(&self) -> IterCodepoints;
}

impl<T: AsRef<str> + ?Sized> StrExt for T {
    /// Iterate over the unicode codepoints of a utf8 string, this function is faster than using
    /// [`str::chars`] because it doesn't decode the codepoint into a character but yields only the
    /// codepoint bytecounts.
    fn iter_codepoints(&self) -> IterCodepoints {
        IterCodepoints(self.as_ref())
    }
}

struct IterCodepoints<'a>(&'a str);
impl<'a> Iterator for IterCodepoints<'a> {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.0.as_bytes();
        let b = *bytes.first()?;

        // Safety: we got the byte from a &str, which is guaranteed to be utf8
        let len = unsafe { utf8_byte_count(b) };
        self.0 = &self.0[len as usize..];

        Some(len)
    }
}

/// Safety: the byte is part of utf8 string, so that leading_ones() is always <= 4
///
/// https://en.wikipedia.org/wiki/UTF-8#Encoding
unsafe fn utf8_byte_count(b: u8) -> u32 {
    // leading_ones().max(1) makes the compiler emit some jumps
    // doing unreachable_unchecked fixes it
    let count = b.leading_ones();
    if count > 4 {
        std::hint::unreachable_unchecked()
    }
    count.max(1)
}

/// Correctness: `len` must come from [`utf8_byte_count`] which is always in the range of <1, 4>
///
/// Could possibly use <https://stackoverflow.com/a/5729436>
fn utf8_bytecount_to_utf16_codeunits(len: u32) -> u32 {
    // 0 -> bad
    // 1 -> 1
    // 2 -> 1
    // 3 -> 1
    // 4 -> 2
    1 + (len / 4)
}

#[test]
fn test_line_lookup() {
    let str = "abcd\nì\n\nế";
    let mapping = LineMap::new(str);

    let test = |offset: Offset, (l, c): (u32, u32)| {
        let res = mapping.offset_to_codepoint(str, offset);
        let expected = CodePointPos {
            line: l,
            character: c,
        };
        assert_eq!(expected, res);
    };

    test(0, (0, 0));
    test(4, (0, 4));
    test(5, (1, 0));
    test(7, (1, 1));
    test(8, (2, 0));
    test(9, (3, 0));
}

#[cfg(test)]
/// initially stolen from https://docs.rs/lsp-document/0.6.0/src/lsp_document/lib.rs.html#460
mod tests {
    use super::Offset;

    fn char_utf8_len(char: char) -> u32 {
        let mut buf = [0u8; 4];
        let result = char.encode_utf8(&mut buf);
        result.len().try_into().unwrap()
    }

    fn char_utf16_len(char: char) -> u32 {
        let mut buf = [0u16; 2];
        let result = char.encode_utf16(&mut buf);
        result.len().try_into().unwrap()
    }

    #[derive(Debug)]
    struct CharInfo {
        #[allow(unused)]
        char: char,
        offset: Offset,
        line: u32,
        line_codepoint_offset: u32,
        line_byte_offset: u32,
        line_u16_offset: u32,
    }

    fn iter_chars(str: &str, mut fun: impl FnMut(CharInfo)) {
        assert!(
            !str.contains('\r'),
            "Line detection is expecting only '\\n'"
        );

        let mut line = 0;
        let mut line_codepoint_offset = 0;
        let mut line_byte_offset = 0;
        let mut line_u16_offset = 0;
        for (index, char) in str.char_indices() {
            let info = CharInfo {
                char,
                offset: index.try_into().unwrap(),
                line,
                line_codepoint_offset,
                line_byte_offset,
                line_u16_offset,
            };

            fun(info);

            line_codepoint_offset += 1;
            line_byte_offset += char_utf8_len(char);
            line_u16_offset += char_utf16_len(char);

            if char == '\n' {
                line += 1;
                line_codepoint_offset = 0;
                line_byte_offset = 0;
                line_u16_offset = 0;
            }
        }
    }

    mod offset_map {
        use crate::linemap::{CodePointPos, LineMap, Utf16Pos, Utf8Pos};

        use super::iter_chars;

        #[test]
        fn no_newline() {
            //          012
            let text = "Hi!";
            let map = LineMap::new(text);
            assert_eq!(map.lines, &[(0, false)]);
        }

        #[test]
        fn newline() {
            //          012 3
            let text = "Hi!\n";
            let map = LineMap::new(text);
            assert_eq!(map.lines, &[(0, false), (4, false)]);
        }

        #[test]
        fn crlf_newline() {
            //          012 3 4
            let text = "Hi!\r\n";
            let map = LineMap::new(text);
            assert_eq!(map.lines, &[(0, false), (5, false)]);
        }

        #[test]
        fn two_lines() {
            //          012 345678
            let text = "Hi!\nWorld";
            let map = LineMap::new(text);
            assert_eq!(map.lines, &[(0, false), (4, false)]);
        }

        #[rustfmt::skip]
        const UNICODE_STR: &str = 
            //...3.......2....4............
            //01236789 012456 045678 012345
             "aa ᒣ bb\ncróbs\n𒀀gfrd\nnormal";

        #[test]
        fn line_detection() {
            let map = LineMap::new(UNICODE_STR);
            #[rustfmt::skip]
            assert_eq!(map.lines, &[
                (0, true),
                (10, true),
                (17, true),
                (26, false)
            ]);
        }

        #[test]
        fn utf8_to_offset() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = Utf8Pos {
                    line: info.line,
                    character: info.line_byte_offset,
                };
                let offset = map.utf8_to_offset(UNICODE_STR, pos);
                assert_eq!(info.offset, offset, "{info:?}");
            });
        }

        #[test]
        fn utf16_to_offset() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = Utf16Pos {
                    line: info.line,
                    character: info.line_u16_offset,
                };
                let offset = map.utf16_to_offset(UNICODE_STR, pos);
                assert_eq!(info.offset, offset, "{info:?}");
            });
        }

        #[test]
        fn codepoint_to_offset() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = CodePointPos {
                    line: info.line,
                    character: info.line_codepoint_offset,
                };
                let offset = map.codepoint_to_offset(UNICODE_STR, pos);
                assert_eq!(info.offset, offset, "{info:?}");
            });
        }

        #[test]
        fn offset_to_utf8() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = Utf8Pos {
                    line: info.line,
                    character: info.line_byte_offset,
                };
                let res = map.offset_to_utf8(UNICODE_STR, info.offset);
                assert_eq!(pos, res, "{info:?}");
            });
        }

        #[test]
        fn offset_to_utf16() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = Utf16Pos {
                    line: info.line,
                    character: info.line_u16_offset,
                };
                let res = map.offset_to_utf16(UNICODE_STR, info.offset);
                assert_eq!(pos, res, "{info:?}");
            });
        }

        #[test]
        fn offset_to_codepoint() {
            let map = LineMap::new(UNICODE_STR);
            iter_chars(UNICODE_STR, |info| {
                let pos = CodePointPos {
                    line: info.line,
                    character: info.line_codepoint_offset,
                };
                let res = map.offset_to_codepoint(UNICODE_STR, info.offset);
                assert_eq!(pos, res, "{info:?}");
            });
        }

        #[test]
        fn empty_offset() {
            let text = "";
            let map = LineMap::new(text);
            let pos = map.offset_to_utf8(text, 0);
            assert_eq!(pos, Utf8Pos::new(0, 0));
        }

        #[test]
        fn empty_offset_clamp() {
            let text = "";
            let map = LineMap::new(text);
            let pos = map.offset_to_utf8(text, 9000);
            assert_eq!(pos, Utf8Pos::new(0, 0));
        }

        #[test]
        fn offset_clamp() {
            let text = "a\nb\nc";
            let map = LineMap::new(text);
            let pos = map.offset_to_utf8(text, 9000);
            assert_eq!(pos, Utf8Pos::new(2, 1));
        }

        #[test]
        fn empty_utf8() {
            let text = "";
            let map = LineMap::new(text);
            let pos = map.utf8_to_offset(
                text,
                Utf8Pos {
                    line: 0,
                    character: 0,
                },
            );
            assert_eq!(pos, 0);
        }

        #[test]
        fn empty_utf8_clamp() {
            let text = "";
            let map = LineMap::new(text);
            let pos = map.utf8_to_offset(
                text,
                Utf8Pos {
                    line: 0,
                    character: 9000,
                },
            );
            assert_eq!(pos, 0);
        }

        #[test]
        fn utf8_line_clamp() {
            //                012 345 67
            let text: &str = "aa\nbb\ncc";
            let map = LineMap::new(text);
            let pos = map.utf8_to_offset(
                text,
                Utf8Pos {
                    line: 1,
                    character: 9000,
                },
            );

            // one past the end of the line / start of the next line
            assert_eq!(pos, 6);
        }
    }
}
