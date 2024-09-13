use std::fmt::Display;

use crate::{interner::InternedFragments, InternedString, RenderCx, RenderCxInner};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fragment(u32);

impl Fragment {
    pub(crate) fn new(index: usize) -> Fragment {
        Self(index.try_into().unwrap())
    }
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone)]
pub enum FragmentHeader {
    Static(&'static str),
    String(InternedString),
    Composite(InternedFragments),
}

impl FragmentHeader {
    pub fn resolve<'a, 'b>(&'a self, rcx: &'b RenderCxInner) -> FragmentData<'b> {
        match *self {
            FragmentHeader::Static(a) => FragmentData::String(a),
            FragmentHeader::String(a) => FragmentData::String(rcx.get_string(a)),
            FragmentHeader::Composite(a) => FragmentData::Composite(rcx.get_fragments(a)),
        }
    }
}

pub enum FragmentData<'a> {
    String(&'a str),
    Composite(&'a [FragmentHeader]),
}

impl Fragment {
    fn fmt_write_to_impl(
        header: &FragmentHeader,
        writer: &mut dyn std::fmt::Write,
        rcx: &RenderCxInner,
    ) -> std::fmt::Result {
        let data = header.resolve(rcx);
        match data {
            FragmentData::String(str) => {
                // TODO be more clever about this
                writer.write_str(str)?;
                writer.write_str(" ")
            }
            FragmentData::Composite(children) => {
                for child in children {
                    Fragment::fmt_write_to_impl(child, writer, rcx)?;
                }
                writer.write_str("\n")
            }
        }
    }
    pub fn fmt_write_to(
        self,
        writer: &mut dyn std::fmt::Write,
        rcx: &RenderCx,
    ) -> std::fmt::Result {
        let rcx = rcx.borrow();
        let header = rcx.get_fragment(self);
        Self::fmt_write_to_impl(&header, writer, &rcx)
    }
    pub fn display(self, rcx: &RenderCx) -> FragmentDisplay {
        FragmentDisplay {
            fragment: self,
            rcx,
        }
    }
}

pub struct FragmentDisplay<'a> {
    fragment: Fragment,
    rcx: &'a RenderCx,
}

impl Display for FragmentDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fragment.fmt_write_to(f, self.rcx)
    }
}
