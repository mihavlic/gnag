use std::fmt::Display;

use crate::{renderable::Renderable, RenderCx};

#[derive(Clone, Copy)]
pub enum RenderedFragment<'a> {
    Leaf(&'a str),
    Parent(&'a [RenderedFragment<'a>]),
}

impl<'a> RenderedFragment<'a> {
    pub fn fmt_write_to(&self, writer: &mut dyn std::fmt::Write) -> std::fmt::Result {
        match *self {
            RenderedFragment::Leaf(str) => {
                // TODO be more clever about this
                writer.write_str(str)?;
                writer.write_str(" ")
            }
            RenderedFragment::Parent(children) => {
                for fragment in children {
                    fragment.fmt_write_to(writer)?;
                }
                writer.write_str("\n")
            }
        }
    }
    pub fn io_write_to(&self, writer: &mut dyn std::io::Write) -> std::io::Result<()> {
        match *self {
            RenderedFragment::Leaf(str) => {
                writer.write(str.as_bytes())?;
                writer.write(b" ")?;
            }
            RenderedFragment::Parent(children) => {
                for fragment in children {
                    fragment.io_write_to(writer)?;
                }
                writer.write(b"\n")?;
            }
        }
        Ok(())
    }
    pub fn display(&self) -> FragmentDisplay<'_, 'a> {
        FragmentDisplay(self)
    }
}

pub trait CollectFragments<'a> {
    fn collect_fragments(self, rcx: &RenderCx<'a>) -> &'a [RenderedFragment<'a>];
}

impl<'a, I> CollectFragments<'a> for I
where
    I: IntoIterator,
    I::Item: Renderable<'a>,
{
    fn collect_fragments(self, rcx: &RenderCx<'a>) -> &'a [RenderedFragment<'a>] {
        let start = rcx.start_render();
        for element in self {
            let fragment = element.render(rcx);
            rcx.append_fragment(fragment);
        }
        rcx.finish_render_into_slice(start)
    }
}

pub struct FragmentDisplay<'a, 'b>(&'a RenderedFragment<'b>);

impl<'a, 'b> Display for FragmentDisplay<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_write_to(f)
    }
}
