use std::fmt::Display;

use crate::{fragment::RenderedFragment, RenderCx};

pub trait Renderable<'a> {
    fn render_into(&self, rcx: &RenderCx<'a>);
    fn render(&self, rcx: &RenderCx<'a>) -> &'a RenderedFragment<'a> {
        let start = rcx.start_render();
        self.render_into(rcx);
        rcx.finish_render(start)
    }
}

impl<'a, 'b, T: Display + 'a> Renderable<'b> for T
where
    'b: 'a,
{
    fn render_into(&self, rcx: &RenderCx<'b>) {
        rcx.append_display(self)
    }
}

impl<'b> Renderable<'b> for &'b RenderedFragment<'b> {
    fn render_into(&self, rcx: &RenderCx<'b>) {
        rcx.append_fragment(self)
    }
}

#[doc(hidden)]
pub struct Template<T: Fn(&RenderCx)>(pub T);

impl<T> Clone for Template<T>
where
    T: Clone + Fn(&RenderCx),
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'a, F> Renderable<'a> for Template<F>
where
    F: Fn(&RenderCx<'_>),
{
    fn render_into(&self, rcx: &RenderCx<'a>) {
        (self.0)(rcx)
    }
}
