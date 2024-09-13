mod fragment;
mod interner;
mod renderable;

pub use fragment::*;
use interner::InternedFragments;
use interner::InternedString;
use interner::Interner;
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
    stack: Vec<FragmentHeader>,
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

    pub fn get_fragments(&self, header: InternedFragments) -> &[FragmentHeader] {
        self.interner.get_fragments(header)
    }

    pub fn get_fragment(&self, handle: Fragment) -> &FragmentHeader {
        self.interner.get_fragment(handle)
    }

    fn flush_writes(&mut self) {
        if !self.string.is_empty() {
            let interned = self.interner.intern_string(&self.string);
            self.stack.push(FragmentHeader::String(interned));
            self.string.clear();
        }
    }

    pub fn append_str(&mut self, str: &'static str) {
        self.flush_writes();
        self.stack.push(FragmentHeader::Static(str));
    }

    pub fn append_fragment(&mut self, fragment: Fragment) {
        self.flush_writes();
        let header = self.interner.get_fragment(fragment);
        self.stack.push(header.clone());
    }

    pub fn append_display(&mut self, value: &dyn Display) {
        use std::fmt::Write;
        write!(self.string, "{value}").unwrap();
    }

    pub fn append_debug(&mut self, value: &dyn Debug) {
        use std::fmt::Write;
        write!(self.string, "{value:?}").unwrap();
    }

    fn start_render(&self) -> usize {
        self.stack.len()
    }

    fn finish_render_slice(&mut self, render_start: usize) -> InternedFragments {
        self.flush_writes();
        let fragments = &self.stack[render_start..];

        let header = self.interner.intern_fragments(fragments);

        self.stack.truncate(render_start);
        header
    }

    fn finish_render(&mut self, render_start: usize) -> Fragment {
        self.flush_writes();
        let fragments = &self.stack[render_start..];

        let handle = if let [one] = fragments {
            self.interner.intern_fragment(one.clone())
        } else {
            let interned = self.interner.intern_fragments(fragments);
            self.interner
                .intern_fragment(FragmentHeader::Composite(interned))
        };

        self.stack.truncate(render_start);
        handle
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

    pub fn append_fragment(&self, fragment: Fragment) {
        self.inner.borrow_mut().append_fragment(fragment);
    }

    pub fn append_display<T: Display>(&self, value: T) {
        self.inner.borrow_mut().append_display(&value);
    }

    pub fn append_debug<T: Debug>(&self, value: T) {
        self.inner.borrow_mut().append_debug(&value);
    }

    #[doc(hidden)]
    pub fn start_render(&self) -> usize {
        self.inner.borrow().start_render()
    }

    #[doc(hidden)]
    pub fn finish_render_slice(&self, render_start: usize) -> InternedFragments {
        self.inner.borrow_mut().finish_render_slice(render_start)
    }

    #[doc(hidden)]
    pub fn finish_render(&self, render_start: usize) -> Fragment {
        self.inner.borrow_mut().finish_render(render_start)
    }

    pub fn scope(&self, fun: impl FnOnce()) -> Fragment {
        let start = self.start_render();
        fun();
        self.finish_render(start)
    }
}
