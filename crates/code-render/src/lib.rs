mod fragment;
mod renderable;

pub use fragment::*;
pub use renderable::*;

// re-export proc macros
pub use code_render_macro::render;
pub use code_render_macro::template;

use std::{
    cell::RefCell,
    fmt::{Display, Write},
};

struct RenderCxInner<'a> {
    bump: &'a bumpalo::Bump,
    fragments: Vec<RenderedFragment<'a>>,
    buffer: String,
}

impl<'a> RenderCxInner<'a> {
    fn new(bump: &'a bumpalo::Bump) -> RenderCxInner<'a> {
        Self {
            bump,
            fragments: Default::default(),
            buffer: Default::default(),
        }
    }

    fn flush_writes(&mut self) {
        if !self.buffer.is_empty() {
            let copy = self.bump.alloc_str(&self.buffer);
            self.fragments.push(RenderedFragment::Leaf(copy));
            self.buffer.clear();
        }
    }

    fn append_str(&mut self, str: &'a str) {
        self.flush_writes();
        self.fragments.push(RenderedFragment::Leaf(str));
    }

    fn append_fragment(&mut self, fragment: &'a RenderedFragment<'a>) {
        self.flush_writes();
        self.fragments.push(*fragment);
    }

    fn append_display(&mut self, value: &dyn Display) {
        write!(self.buffer, "{value}").unwrap();
    }

    fn start_render(&self) -> usize {
        self.fragments.len()
    }

    fn finish_render_into_slice(&mut self, render_start: usize) -> &'a [RenderedFragment<'a>] {
        let copy = self.bump.alloc_slice_copy(&self.fragments[render_start..]);
        self.fragments.truncate(render_start);
        copy
    }

    fn finish_render(&mut self, render_start: usize) -> &'a RenderedFragment<'a> {
        let copy = self.finish_render_into_slice(render_start);
        if let [single] = copy {
            single
        } else {
            self.bump.alloc(RenderedFragment::Parent(copy))
        }
    }
}

pub struct RenderCx<'a> {
    inner: RefCell<RenderCxInner<'a>>,
}

impl<'a> RenderCx<'a> {
    pub fn new(bump: &'a bumpalo::Bump) -> RenderCx<'a> {
        Self {
            inner: RefCell::new(RenderCxInner::new(bump)),
        }
    }

    pub fn append_str(&self, str: &'a str) {
        self.inner.borrow_mut().append_str(str);
    }

    pub fn append_fragment(&self, fragment: &'a RenderedFragment<'a>) {
        self.inner.borrow_mut().append_fragment(fragment);
    }

    pub fn append_display<T: Display>(&self, value: T) {
        self.inner.borrow_mut().append_display(&value);
    }

    #[doc(hidden)]
    pub fn start_render(&self) -> usize {
        self.inner.borrow().start_render()
    }

    fn finish_render_into_slice(&self, render_start: usize) -> &'a [RenderedFragment<'a>] {
        self.inner
            .borrow_mut()
            .finish_render_into_slice(render_start)
    }

    #[doc(hidden)]
    pub fn finish_render(&self, render_start: usize) -> &'a RenderedFragment<'a> {
        self.inner.borrow_mut().finish_render(render_start)
    }
}
