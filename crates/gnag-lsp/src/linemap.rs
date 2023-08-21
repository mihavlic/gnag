use std::ops;

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

fn parse_lines(
    start_offset: Offset,
    partial_reparse: bool,
    bytes: &[u8],
    lines: &mut Vec<(Offset, bool)>,
) {
    assert!(start_offset as usize + bytes.len() as usize <= Offset::MAX as usize);

    let len = lines.len();

    let mut saw_unicode = false;
    let mut prev_end = start_offset;
    let mut bytes = (start_offset..start_offset + bytes.len() as Offset).zip(bytes.iter().copied());

    // utf8 bytes are either encoding an ascii character or are >=128 so we can search for ascii
    // characters by interpreting the string as bytes without any false positives

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
                prev_end = i + 1;
            }
            _ => {
                if b >= 128 {
                    saw_unicode = true;
                }
            }
        }
    }

    // partial_reparse, lines.is_empty()
    // 0 0 | 1
    // 0 1 | 1
    // 1 0 | 0
    // 1 1 | 1
    if !partial_reparse || lines.len() == len {
        lines.push((prev_end, saw_unicode));
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
        let mut lines = Vec::new();
        parse_lines(0,  false, src.as_bytes(), &mut lines);
        Self {
            lines,
        }
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
    pub fn replace_whole(&mut self, file: &mut String, replace_with: &str) {
        self.lines.clear();
        file.clear();
        file.push_str(replace_with);
        parse_lines(0, false, file.as_bytes(), &mut self.lines);
    }
    pub fn replace_offset_range(
        &mut self,
        file: &mut String,
        range: ops::Range<Offset>,
        replace_with: &str,
    ) {
        assert!(range.start <= range.end);
        assert!(range.start as usize <= file.len());
        assert!(range.end as usize <= file.len());

        let start = range.start as usize;
        let end = range.end as usize;

        let prev_size = range.end - range.start;
        let new_size = replace_with.len().try_into().unwrap();
        let diff = prev_size.abs_diff(new_size);

        let file_plain_ascii = file.as_bytes()[start..end]
            .iter()
            .copied()
            .all(|b| b.is_ascii() && b != b'\n' && b != b'\n');

        // doing this does not invalidate the lookup structure, just have to remember to offset ranges past the replacement
        file.replace_range(start..end, replace_with);

        // fast path for the majority of edits where the change affects only one line
        let line = if file_plain_ascii
            && replace_with
                .bytes()
                .all(|b| b.is_ascii() && b != b'\n' && b != b'\r')
        {
            self.offset_to_line(range.start).line
        } else {
            let start_line = self.offset_to_line(range.start);
            let end_line = self.offset_to_line(range.end);

            // can't use `self.line_end()` because we need to apply the offset
            let (end_offset, is_eof) = {
                self.lines
                    .get((end_line.line + 1) as usize)
                    .map(|line| {
                        // fantastic
                        if new_size > prev_size {
                            (line.0 + diff, false)
                        } else {
                            (line.0 - diff, false)
                        }
                    })
                    .unwrap_or_else(|| (file.len().try_into().unwrap(), true))
            };

            // we must not include the last line, let's have:
            //  "aaaaa\nbbbb"
            //     ^ edit first line
            // the range `start_line.line_start..end_offset` contains this:
            //  "aaaaa\n"
            // now, the `parse_lines()` function would get to the end of the range and see a "\n",
            // pushing the entry for the line which it was until then inspecting (0, false)
            // at the end of the whole function, the very last line is pushed, which we don't want
            // because we're already aware of the second line and will correct its offset later
            let mut lines = Vec::new();
            parse_lines(
                start_line.line_start,
                !is_eof,
                &file.as_bytes()[start_line.line_start as usize..end_offset as usize],
                &mut lines
            );

            self.lines
                .splice(start_line.line as usize..=end_line.line as usize, lines);

            end_line.line
        };

        if let Some(lines) = self.lines.get_mut((line + 1) as usize..) {
            if new_size > prev_size {
                for (offset, _) in lines {
                    *offset += diff;
                }
            } else {
                for (offset, _) in lines {
                    *offset -= diff;
                }
            };
        }
    }
    pub fn replace_utf8_range(
        &mut self,
        file: &mut String,
        range: ops::Range<Utf8Pos>,
        replace_with: &str,
    ) {
        let start = self.utf8_to_offset(file, range.start);
        let end = self.utf8_to_offset(file, range.end);
        self.replace_offset_range(file, start..end, replace_with);
    }
    pub fn replace_utf16_range(
        &mut self,
        file: &mut String,
        range: ops::Range<Utf16Pos>,
        replace_with: &str,
    ) {
        let start = self.utf16_to_offset(file, range.start);
        let end = self.utf16_to_offset(file, range.end);
        self.replace_offset_range(file, start..end, replace_with);
    }
    pub fn replace_codepoint_range(
        &mut self,
        file: &mut String,
        range: ops::Range<CodePointPos>,
        replace_with: &str,
    ) {
        let start = self.codepoint_to_offset(file, range.start);
        let end = self.codepoint_to_offset(file, range.end);
        self.replace_offset_range(file, start..end, replace_with);
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
        let b = *self.0.as_bytes().first()?;

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

    use crate::linemap::{CodePointPos, LineMap, Utf16Pos, Utf8Pos};

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

    #[test]
    fn start_newline() {
        //          0123 456789
        let text = "\nHi!\nWorld";
        let map = LineMap::new(text);
        assert_eq!(map.lines, &[(0, false), (1, false)]);
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

    #[test]
    fn replace_fuzz() {
        let mut text = "aa\nbb\ncc\n\n\naa\nbb\nccaa\nbb\ncc".to_owned();
        let mut map = LineMap::new(&text);

        let mut state: usize = 0;
        let mut rng = || {
            state ^= 939847593342222225;
            state = state.rotate_left(1);
            state
        };

        for _ in 0..10000 {
            let start = rng() % text.len();
            let len = rng() % (text.len() - start);

            let replacement = (0..len)
                .map(|_| if rng() % 8 > 0 { 'a' } else { '\n' })
                .collect::<String>();

            test_replace_equivalent(&mut map, &mut text, start, len, replacement);
        }
    }

    #[test]
    fn replace_edgecases() {
        replace_manual("a\nc", 0..1, "\n");
        replace_manual("a\nc", 0..2, "\n");
        replace_manual("a\nc", 0..2, "a");
        replace_manual("a\nc", 0..2, "");
    }

    fn replace_manual(text: &str, range: std::ops::Range<usize>, replace_with: &str) {
        let mut text = text.to_owned();
        let mut map = LineMap::new(&text);
        test_replace_equivalent(
            &mut map,
            &mut text,
            range.start,
            range.end - range.start,
            replace_with.into(),
        );
    }

    fn test_replace_equivalent(
        map: &mut LineMap,
        text: &mut String,
        start: usize,
        len: usize,
        replace_with: String,
    ) {
        let mut copy = text.clone();

        copy.replace_range(start..start + len, &replace_with);
        let map2 = LineMap::new(&copy);

        eprintln!(
            "{text:?}\n{}..{} {replace_with:?}\n > {copy:?}\n",
            start,
            start + len
        );

        map.replace_offset_range(
            text,
            start.try_into().unwrap()..(start + len).try_into().unwrap(),
            &replace_with,
        );

        assert_eq!(map.lines, map2.lines);
    }
}
