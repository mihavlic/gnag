use crate::{Fragments, RenderCxInner};

#[derive(Clone, Copy)]
pub struct InternedString {
    pub offset: usize,
    pub len: usize,
}

#[derive(Clone)]
pub enum FragmentData {
    Static(&'static str),
    String(InternedString),
    Composite(Fragments),
    Concatenate,
}

impl FragmentData {
    pub fn resolve<'a, 'b>(&'a self, rcx: &'b RenderCxInner) -> FragmentValue<'b> {
        match *self {
            FragmentData::Static(a) => FragmentValue::String(a),
            FragmentData::String(a) => FragmentValue::String(rcx.get_string(a)),
            FragmentData::Composite(a) => FragmentValue::Composite(rcx.get_fragments(a)),
            FragmentData::Concatenate => FragmentValue::Concatenate,
        }
    }
}

#[derive(Clone, Copy)]
pub enum FragmentValue<'a> {
    String(&'a str),
    Composite(&'a [FragmentData]),
    Concatenate,
}

pub struct Interner {
    string_arena: String,
    fragment_arena: Vec<FragmentData>,
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

    pub fn intern_fragments(&mut self, slice: &[FragmentData]) -> Fragments {
        let offset = self.fragment_arena.len().try_into().unwrap();
        let len = slice.len().try_into().unwrap();

        self.fragment_arena.extend_from_slice(slice);

        Fragments { offset, len }
    }

    pub fn get_string(&self, header: InternedString) -> &str {
        &self.string_arena[header.offset..(header.offset + header.len)]
    }

    pub fn get_fragments(&self, header: Fragments) -> &[FragmentData] {
        let offset = header.offset as usize;
        let len = header.len as usize;
        &self.fragment_arena[offset..(offset + len)]
    }
}
