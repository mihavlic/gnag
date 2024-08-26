use std::fmt::Display;

use crate::{Language, NodeEvent};

#[derive(Clone)]
pub struct Tokens(Vec<NodeEvent>);
impl Tokens {
    pub fn from_raw(vec: Vec<NodeEvent>) -> Tokens {
        Self(vec)
    }
    pub fn into_raw(self) -> Vec<NodeEvent> {
        self.0
    }
    pub fn get_raw(&self) -> &Vec<NodeEvent> {
        &self.0
    }
    pub fn get_raw_mut(&mut self) -> &mut Vec<NodeEvent> {
        &mut self.0
    }

    pub fn display_into<'a, 'b>(
        &'a self,
        buf: &mut dyn std::fmt::Write,
        language: &'b Language,
        print_skip_tokens: bool,
    ) -> std::fmt::Result {
        for node in self.get_raw().iter() {
            if node.kind.is_skip() && !print_skip_tokens {
                continue;
            }

            let name = node.kind.name(language);
            write!(buf, "{name}\n")?;
        }

        Ok(())
    }

    pub fn display<'a, 'b>(
        &'a self,
        language: &'b Language,
        print_skip_tokens: bool,
    ) -> TokensDisplay<'a, 'b> {
        TokensDisplay(self, language, print_skip_tokens)
    }
}

#[derive(Clone, Copy)]
pub struct TokensDisplay<'a, 'b>(&'a Tokens, &'b Language, bool);
impl Display for TokensDisplay<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.display_into(f, self.1, self.2)
    }
}

#[derive(Clone)]
pub struct PostorderTrace(Vec<NodeEvent>);
impl PostorderTrace {
    pub fn from_raw(vec: Vec<NodeEvent>) -> PostorderTrace {
        Self(vec)
    }
    pub fn into_raw(self) -> Vec<NodeEvent> {
        self.0
    }
    pub fn get_raw(&self) -> &Vec<NodeEvent> {
        &self.0
    }
    pub fn get_raw_mut(&mut self) -> &mut Vec<NodeEvent> {
        &mut self.0
    }

    pub fn to_preorder(self, stack: &mut Vec<TraceReorderScope>) -> PreorderTrace {
        let mut raw = self.into_raw();
        trace_postorder_to_preorder_inplace(&mut raw, stack);
        PreorderTrace::from_raw(raw)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TraceVisitEvent {
    Open,
    Token,
    Close,
}

#[derive(Clone)]
pub struct PreorderTrace(Vec<NodeEvent>);
impl PreorderTrace {
    pub fn from_raw(vec: Vec<NodeEvent>) -> PreorderTrace {
        Self(vec)
    }
    pub fn into_raw(self) -> Vec<NodeEvent> {
        self.0
    }
    pub fn get_raw(&self) -> &Vec<NodeEvent> {
        &self.0
    }
    pub fn get_raw_mut(&mut self) -> &mut Vec<NodeEvent> {
        &mut self.0
    }

    pub fn iter<'a, 'b>(&'a self, stack: &'b mut Vec<NodeEvent>) -> TraceIterator<'a, 'b> {
        stack.clear();
        TraceIterator {
            events: self.get_raw().iter(),
            stack,
        }
    }

    pub fn iter_offsets<'a, 'b>(
        &'a self,
        stack: &'b mut Vec<(NodeEvent, u32)>,
    ) -> TraceOffsetIterator<'a, 'b> {
        stack.clear();
        TraceOffsetIterator {
            events: self.get_raw().iter(),
            stack,
            current_offset: 0,
        }
    }

    pub fn display_into<'a, 'b>(
        &'a self,
        buf: &mut dyn std::fmt::Write,
        language: &'b Language,
        print_skip_tokens: bool,

        stack: &mut Vec<NodeEvent>,
    ) -> std::fmt::Result {
        let mut indent = 0;
        for (event, node) in self.iter(stack) {
            if node.kind.is_skip() && !print_skip_tokens {
                continue;
            }

            let old_indent = indent;

            match event {
                TraceVisitEvent::Open => indent += 1,
                TraceVisitEvent::Token => {}
                TraceVisitEvent::Close => {
                    indent -= 1;
                    continue;
                }
            }

            for _ in 0..old_indent {
                write!(buf, "  ")?;
            }

            let name = node.kind.name(language);
            write!(buf, "{name}\n")?;
        }

        Ok(())
    }

    pub fn display<'a, 'b>(
        &'a self,
        language: &'b Language,
        print_skip_tokens: bool,
    ) -> TraceDisplay<'a, 'b> {
        TraceDisplay(self, language, print_skip_tokens)
    }
}

pub struct TraceIterator<'a, 'b> {
    events: std::slice::Iter<'a, NodeEvent>,
    stack: &'b mut Vec<NodeEvent>,
}

impl Iterator for TraceIterator<'_, '_> {
    type Item = (TraceVisitEvent, NodeEvent);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(event) = self.stack.last_mut() {
            if event.size_or_start_or_children == 0 {
                let event = *event;
                self.stack.pop();
                return Some((TraceVisitEvent::Close, event));
            } else {
                event.size_or_start_or_children -= 1;
            }
        }

        let next = self.events.next()?;

        let event = if next.kind.is_token() {
            TraceVisitEvent::Token
        } else {
            self.stack.push(*next);
            TraceVisitEvent::Open
        };

        return Some((event, *next));
    }
}

pub struct TraceOffsetIterator<'a, 'b> {
    events: std::slice::Iter<'a, NodeEvent>,
    stack: &'b mut Vec<(NodeEvent, u32)>,
    current_offset: u32,
}

impl<'a, 'b> TraceOffsetIterator<'a, 'b> {
    pub fn current_offset(&self) -> u32 {
        self.current_offset
    }
}

impl Iterator for TraceOffsetIterator<'_, '_> {
    type Item = (u32, TraceVisitEvent, NodeEvent);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((event, start_offset)) = self.stack.last_mut() {
            if event.size_or_start_or_children == 0 {
                let event = *event;
                let start_offset = *start_offset;
                self.stack.pop();
                return Some((start_offset, TraceVisitEvent::Close, event));
            } else {
                event.size_or_start_or_children -= 1;
            }
        }

        let next = self.events.next()?;
        let offset = self.current_offset;

        let event = if next.kind.is_token() {
            self.current_offset += next.size_or_start_or_children;
            TraceVisitEvent::Token
        } else {
            self.stack.push((*next, self.current_offset));
            TraceVisitEvent::Open
        };

        return Some((offset, event, *next));
    }
}

#[derive(Clone, Copy)]
pub struct TraceDisplay<'a, 'b>(&'a PreorderTrace, &'b Language, bool);
impl Display for TraceDisplay<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.display_into(f, self.1, self.2, &mut Vec::new())
    }
}

struct TraceReorderWriter<'a> {
    len: u32,
    dst: u32,
    slice: &'a mut [NodeEvent],
}

impl<'a> TraceReorderWriter<'a> {
    fn new(trace: &'a mut [NodeEvent]) -> TraceReorderWriter<'a> {
        let len_u32: u32 = trace.len().try_into().unwrap();

        Self {
            len: len_u32,
            dst: len_u32,
            slice: trace,
        }
    }

    #[inline(always)]
    fn next(&mut self) -> Option<(u32, NodeEvent)> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        return Some((self.len, self.slice[self.len as usize]));
    }

    #[inline(always)]
    fn push(&mut self, event: NodeEvent) {
        debug_assert!(self.dst != u32::MAX, "Write overflows slice!");
        self.dst -= 1;
        self.slice[self.dst as usize] = event;
    }

    fn is_complete(&self) -> bool {
        self.len == 0 && self.dst == 0
    }
}

pub struct TraceReorderScope {
    event: NodeEvent,
    child_count: u32,
}

pub fn trace_postorder_to_preorder_inplace(
    trace: &mut [NodeEvent],
    stack: &mut Vec<TraceReorderScope>,
) {
    stack.clear();

    // we can do the postorder -> preorder step in place
    // TraceReorderWriter is just a wrapper which holds two cursors into the slice
    // one for taking elements out and another for inserting them back in a different order
    let mut writer = TraceReorderWriter::new(trace);

    while let Some((index, event)) = writer.next() {
        if let Some(current) = stack.last_mut() {
            current.child_count += 1;
        }

        if event.kind.is_token() {
            writer.push(event);
        } else {
            // push the event to the scope stack
            // we will write it back to the trace later when we pop this scope
            stack.push(TraceReorderScope {
                event,
                child_count: 0,
            });
        }

        while let Some(current) = stack.last_mut() {
            if current.event.size_or_start_or_children == index {
                writer.push(NodeEvent {
                    size_or_start_or_children: current.child_count,
                    kind: current.event.kind,
                    max_lookahead: current.event.max_lookahead,
                });

                stack.pop();
            } else {
                break;
            }
        }
    }

    assert!(writer.is_complete(), "Trace contains malformed spans");
}

#[test]
fn test_reorder() {
    use crate::parser::Parser;
    use crate::NodeKind;

    let language = Language {
        lexer_entry: |_| todo!(),
        parser_entry: |_| todo!(),
        names: &["1", "2"],
    };

    let token = NodeKind::new(0, crate::NodeKindTag::Token);
    let rule = NodeKind::new(1, crate::NodeKindTag::Rule);

    let tokens = &[NodeEvent {
        kind: token,
        max_lookahead: 0,
        size_or_start_or_children: 0,
    }; 10];

    let mut p = Parser::new(tokens, Vec::new());

    {
        {
            let c = p.open_span();
            {
                let c = p.open_span();
                p.next();
                p.close_span(c, rule);
                p.close_span(c, rule);
            }
            p.next();
            {
                let c = p.open_span();
                p.next();
                p.close_span(c, rule);
            }
            p.close_span(c, rule);
        }
    }

    let trace = p.finish().to_preorder(&mut Vec::new());

    for (event, _) in trace.iter(&mut Vec::new()) {
        eprintln!("{event:?}");
    }

    eprintln!("{}", trace.display(&language, false));
}
