use std::fmt::Display;

use crate::{interner::FragmentValue, FragmentData, RenderCx, RenderCxInner};

#[derive(Clone, Copy)]
pub struct Fragments {
    pub offset: u32,
    pub len: u32,
}

impl Fragments {
    fn from_index(index: u32) -> Fragments {
        Fragments {
            offset: index,
            len: 1,
        }
    }
}

#[derive(Clone)]
pub struct FragmentIter {
    inner: std::ops::Range<u32>,
}

impl Iterator for FragmentIter {
    type Item = Fragments;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Fragments::from_index)
    }
}

impl IntoIterator for Fragments {
    type Item = Fragments;
    type IntoIter = FragmentIter;

    fn into_iter(self) -> Self::IntoIter {
        FragmentIter {
            inner: self.offset..(self.offset + self.len),
        }
    }
}

impl Fragments {
    fn fmt_write_to_impl(
        slice: &[FragmentData],
        writer: &mut dyn std::fmt::Write,
        rcx: &RenderCxInner,
    ) -> std::fmt::Result {
        let mut concat = true;
        for data in slice.iter().cloned() {
            let value = data.resolve(rcx);

            if let FragmentValue::Concatenate = value {
                concat = true;
                continue;
            }

            // TODO should we not conservatively emit whitespace between all not-concatenated siblings?
            if !concat {
                writer.write_str(" ")?;
            }
            concat = false;

            match value {
                FragmentValue::String(str) => {
                    writer.write_str(str)?;
                }
                FragmentValue::Composite(children) => {
                    Fragments::fmt_write_to_impl(children, writer, rcx)?;
                }
                FragmentValue::Concatenate => {}
            }
        }
        Ok(())
    }
    pub fn fmt_write_to(
        self,
        writer: &mut dyn std::fmt::Write,
        rcx: &RenderCx,
    ) -> std::fmt::Result {
        let rcx = rcx.borrow();
        let header = rcx.get_fragments(self);
        Self::fmt_write_to_impl(header, writer, &rcx)
    }
    fn fmt_debug_impl(
        slice: &[FragmentData],
        writer: &mut dyn std::fmt::Write,
        depth: u32,
        rcx: &RenderCxInner,
    ) -> std::fmt::Result {
        for data in slice.iter().cloned() {
            let value = data.resolve(rcx);
            for _ in 0..depth {
                write!(writer, "  ")?;
            }
            match value {
                FragmentValue::String(str) => {
                    write!(writer, "{:?}\n", str)?;
                }
                FragmentValue::Composite(children) => {
                    write!(writer, "Composite\n")?;
                    Fragments::fmt_debug_impl(children, writer, depth + 1, rcx)?;
                }
                FragmentValue::Concatenate => {
                    write!(writer, "Concatenate\n")?;
                }
            }
        }
        Ok(())
    }
    pub fn fmt_debug(self, writer: &mut dyn std::fmt::Write, rcx: &RenderCx) -> std::fmt::Result {
        let rcx = rcx.borrow();
        let header = rcx.get_fragments(self);
        Self::fmt_debug_impl(header, writer, 0, &rcx)
    }
    pub fn display(self, rcx: &RenderCx) -> FragmentDisplay {
        FragmentDisplay {
            fragment: self,
            rcx,
        }
    }
}

pub struct FragmentDisplay<'a> {
    fragment: Fragments,
    rcx: &'a RenderCx,
}

impl Display for FragmentDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fragment.fmt_write_to(f, self.rcx)
    }
}
