use std::fmt::Display;

use crate::{interner::InternedFragments, Fragment, RenderCx};

pub trait Renderable {
    fn render_into(&self, rcx: &RenderCx);
    fn render(&self, rcx: &RenderCx) -> Fragment {
        let start = rcx.start_render();
        self.render_into(rcx);
        rcx.finish_render(start)
    }
}

impl<T: Display> Renderable for T {
    fn render_into(&self, rcx: &RenderCx) {
        rcx.append_display(self)
    }
}

impl Renderable for Fragment {
    fn render_into(&self, rcx: &RenderCx) {
        rcx.append_fragment(*self)
    }
}

#[doc(hidden)]
#[derive(Clone)]
pub struct Template<T: Fn(&RenderCx)>(pub T);

impl<F> Renderable for Template<F>
where
    F: Fn(&RenderCx),
{
    fn render_into(&self, rcx: &RenderCx) {
        (self.0)(rcx)
    }
}

pub trait CollectFragments {
    fn collect_fragments(self, rcx: &RenderCx) -> InternedFragments;
}

impl<I> CollectFragments for I
where
    I: IntoIterator,
    I::Item: Renderable,
{
    fn collect_fragments(self, rcx: &RenderCx) -> InternedFragments {
        let start = rcx.start_render();
        for element in self {
            let fragment = element.render(rcx);
            rcx.append_fragment(fragment);
        }
        rcx.finish_render_slice(start)
    }
}
