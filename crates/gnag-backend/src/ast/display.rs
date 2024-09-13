pub struct ByteSliceDisplay<'a>(&'a [u8]);

impl<'a> std::fmt::Display for ByteSliceDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b")?;
        display_byte_literal(f, "\"", self.0)
    }
}

pub struct ByteDisplay(u8);

impl<'a> std::fmt::Display for ByteDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b\'{}\'", std::ascii::escape_default(self.0))
    }
}

pub trait ByteSliceExt {
    fn display(&self) -> ByteSliceDisplay;
}

impl ByteSliceExt for [u8] {
    fn display(&self) -> ByteSliceDisplay {
        ByteSliceDisplay(self)
    }
}

pub trait ByteExt {
    fn display(self) -> ByteDisplay;
}

impl ByteExt for u8 {
    fn display(self) -> ByteDisplay {
        ByteDisplay(self)
    }
}

/// Stolen from [u8]::utf8_chunks documentation example
pub fn display_byte_literal(
    buf: &mut dyn std::fmt::Write,
    delimiter: &str,
    bytes: &[u8],
) -> std::fmt::Result {
    buf.write_str(delimiter)?;
    for chunk in bytes.utf8_chunks() {
        for ch in chunk.valid().chars() {
            // Escapes \0, \t, \r, \n, \\, \', \", and uses \u{...} for non-printable characters.
            write!(buf, "{}", ch.escape_debug())?;
        }
        for byte in chunk.invalid() {
            write!(buf, "\\x{:02X}", byte)?;
        }
    }
    buf.write_str(delimiter)
}
