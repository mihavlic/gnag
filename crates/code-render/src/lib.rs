mod fragment;
mod interner;
mod renderable;

pub use fragment::*;
pub use interner::*;
pub use renderable::*;

// re-export proc macros
pub use code_render_macro::render;
pub use code_render_macro::render_into;
pub use code_render_macro::template;

use std::cell::Ref;
use std::fmt::Debug;
use std::{cell::RefCell, fmt::Display};

pub struct RenderCxInner {
    interner: Interner,
    string: String,
    stack: Vec<FragmentData>,
}

impl RenderCxInner {
    fn new() -> RenderCxInner {
        Self {
            interner: Interner::new(),
            string: Default::default(),
            stack: Default::default(),
        }
    }

    pub fn get_string(&self, header: InternedString) -> &str {
        self.interner.get_string(header)
    }

    pub fn get_fragments(&self, header: Fragments) -> &[FragmentData] {
        self.interner.get_fragments(header)
    }

    fn flush_writes(&mut self) {
        if !self.string.is_empty() {
            let interned = self.interner.intern_string(&self.string);
            self.stack.push(FragmentData::String(interned));
            self.string.clear();
        }
    }

    pub fn append_str(&mut self, str: &'static str) {
        self.flush_writes();
        self.stack.push(FragmentData::Static(str));
    }

    pub fn append_fragment(&mut self, fragment: Fragments) {
        self.flush_writes();
        self.stack.push(FragmentData::Composite(fragment));
    }

    pub fn append_display(&mut self, value: &dyn Display) {
        use std::fmt::Write;
        write!(self.string, "{value}").unwrap();
    }

    pub fn append_debug(&mut self, value: &dyn Debug) {
        use std::fmt::Write;
        write!(self.string, "{value:?}").unwrap();
    }

    pub fn append_concatenate(&mut self) {
        self.flush_writes();
        self.stack.push(FragmentData::Concatenate);
    }

    fn start_render(&self) -> usize {
        self.stack.len()
    }

    fn finish_render_slice(&mut self, render_start: usize) -> Fragments {
        self.flush_writes();
        let fragments = &self.stack[render_start..];

        let header = self.interner.intern_fragments(fragments);

        self.stack.truncate(render_start);
        header
    }

    fn finish_render(&mut self, render_start: usize) -> Fragments {
        self.flush_writes();
        let fragments = &self.stack[render_start..];

        let interned = self.interner.intern_fragments(fragments);

        self.stack.truncate(render_start);
        interned
    }
}

pub struct RenderCx {
    inner: RefCell<RenderCxInner>,
}

impl RenderCx {
    pub fn new() -> RenderCx {
        Self {
            inner: RefCell::new(RenderCxInner::new()),
        }
    }

    pub fn borrow(&self) -> Ref<'_, RenderCxInner> {
        self.inner.borrow()
    }

    pub fn append_str(&self, str: &'static str) {
        self.inner.borrow_mut().append_str(str);
    }

    pub fn append_fragment(&self, fragment: Fragments) {
        self.inner.borrow_mut().append_fragment(fragment);
    }

    pub fn append_display<T: Display>(&self, value: T) {
        self.inner.borrow_mut().append_display(&value);
    }

    pub fn append_debug<T: Debug>(&self, value: T) {
        self.inner.borrow_mut().append_debug(&value);
    }

    pub fn append_concatenate(&self) {
        self.inner.borrow_mut().append_concatenate();
    }

    #[doc(hidden)]
    pub fn start_render(&self) -> usize {
        self.inner.borrow().start_render()
    }

    #[doc(hidden)]
    pub fn finish_render_slice(&self, render_start: usize) -> Fragments {
        self.inner.borrow_mut().finish_render_slice(render_start)
    }

    #[doc(hidden)]
    pub fn finish_render(&self, render_start: usize) -> Fragments {
        self.inner.borrow_mut().finish_render(render_start)
    }

    pub fn scope(&self, fun: impl FnOnce()) -> Fragments {
        let start = self.start_render();
        fun();
        self.finish_render(start)
    }
}
