use crate::{Fragment, FragmentHeader};

#[derive(Clone, Copy)]
pub struct InternedString {
    pub offset: usize,
    pub len: usize,
}

#[derive(Clone, Copy)]
pub struct InternedFragments {
    pub offset: usize,
    pub len: usize,
}

#[derive(Clone)]
pub struct FragmentIter {
    inner: std::ops::Range<usize>,
}

impl Iterator for FragmentIter {
    type Item = Fragment;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Fragment::new)
    }
}

impl IntoIterator for InternedFragments {
    type Item = Fragment;
    type IntoIter = FragmentIter;

    fn into_iter(self) -> Self::IntoIter {
        FragmentIter {
            inner: self.offset..(self.offset + self.len),
        }
    }
}

pub struct Interner {
    string_arena: String,
    fragment_arena: Vec<FragmentHeader>,
}

impl Interner {
    pub fn new() -> Interner {
        Self {
            string_arena: Default::default(),
            fragment_arena: Default::default(),
        }
    }

    pub fn intern_string(&mut self, str: &str) -> InternedString {
        let offset = self.string_arena.len();
        self.string_arena.push_str(str);
        InternedString {
            offset,
            len: str.len(),
        }
    }

    pub fn intern_fragments(&mut self, slice: &[FragmentHeader]) -> InternedFragments {
        let offset = self.fragment_arena.len();
        self.fragment_arena.extend_from_slice(slice);
        InternedFragments {
            offset,
            len: slice.len(),
        }
    }
    pub fn intern_fragment(&mut self, header: FragmentHeader) -> Fragment {
        let offset = self.fragment_arena.len();
        self.fragment_arena.push(header);
        Fragment::new(offset)
    }

    pub fn get_string(&self, header: InternedString) -> &str {
        &self.string_arena[header.offset..(header.offset + header.len)]
    }

    pub fn get_fragments(&self, header: InternedFragments) -> &[FragmentHeader] {
        &self.fragment_arena[header.offset..(header.offset + header.len)]
    }

    pub fn get_fragment(&self, handle: Fragment) -> &FragmentHeader {
        &self.fragment_arena[handle.index()]
    }
}
