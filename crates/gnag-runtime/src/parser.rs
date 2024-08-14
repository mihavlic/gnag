use crate::{resetable_slice::ResetableSlice, LanguageNodes, NodeEvent, NodeKind, SpanStart};

#[derive(Clone, PartialEq, Eq)]
pub struct ParserPosition {
    token_position: u32,
    trace_position: u32,
}

pub struct Parser<'a> {
    tokens: ResetableSlice<'a, NodeEvent>,
    tree_trace: Vec<NodeEvent>,
    language_nodes: LanguageNodes,
}

impl<'a> Parser<'a> {
    pub fn new(
        tokens: &'a [NodeEvent],
        tree_trace_buffer: Vec<NodeEvent>,
        language_nodes: LanguageNodes,
    ) -> Parser<'a> {
        Parser {
            tokens: ResetableSlice::new(tokens),
            tree_trace: tree_trace_buffer,
            language_nodes,
        }
    }

    pub fn save_position(&self) -> ParserPosition {
        ParserPosition {
            token_position: self.tokens.get_position() as u32,
            trace_position: self.tree_trace.len().try_into().unwrap(),
        }
    }

    pub fn restore_position(&mut self, state: ParserPosition) {
        debug_assert!(
            state.trace_position as usize <= self.tree_trace.len(),
            "Missing trace events to restore to. Mismatched save_position - load_position pair?"
        );

        self.tokens.set_position(state.token_position as usize);
        self.tree_trace.truncate(state.trace_position as usize);
    }

    pub fn consume_skip_tokens(&mut self) -> bool {
        let mut consumed_any = false;
        while let Some(&token) = self.tokens.next() {
            consumed_any = true;
            if !self.language_nodes.is_skip(token.kind) {
                break;
            }
            self.tree_trace.push(token);
        }

        return consumed_any;
    }

    pub fn peek(&mut self) -> Option<NodeKind> {
        if let Some((slice, _)) = self.tokens.remaining().split_at_checked(4) {
            for token in slice {
                if !self.language_nodes.is_skip(token.kind) {
                    return Some(token.kind);
                }
            }
        }

        self.peek_slow()
    }

    #[cold]
    fn peek_slow(&mut self) -> Option<NodeKind> {
        while let Some(&token) = self.tokens.next() {
            if !self.language_nodes.is_skip(token.kind) {
                return Some(token.kind);
            }
        }
        return None;
    }

    pub fn next(&mut self) -> Option<NodeKind> {
        let checkpoint = self.tree_trace.len();

        while let Some(&token) = self.tokens.next() {
            self.tree_trace.push(token);
            if !self.language_nodes.is_skip(token.kind) {
                return Some(token.kind);
            }
        }

        // we undo the pushes if we've reached eof
        // this compiles down to just a few instructions
        self.tree_trace.truncate(checkpoint);

        return None;
    }

    pub fn is_eof(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn open_span(&self) -> SpanStart {
        SpanStart(self.tree_trace.len() as u32)
    }

    pub fn close_span(&mut self, start: SpanStart, kind: NodeKind) {
        self.tree_trace.push(NodeEvent {
            kind,
            max_lookahead: 0, // TODO
            size_or_start_or_children: start.0,
        });
    }

    pub fn finish(self) -> Vec<NodeEvent> {
        self.tree_trace
    }
}

pub struct TraceReorderScope {
    event: NodeEvent,
    child_count: u32,
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
}

pub fn trace_postorder_to_preorder(
    trace: &mut [NodeEvent],
    stack: &mut Vec<TraceReorderScope>,
    language: &LanguageNodes,
) {
    stack.clear();

    // we can do the postorder -> preorder step in place
    // TraceReorderWriter is just a wrapper which hold two cursors into the slice
    // one for taking elements out and another for inserting them back in a different order
    let mut writer = TraceReorderWriter::new(trace);

    while let Some((index, event)) = writer.next() {
        if let Some(current) = stack.last_mut() {
            current.child_count += 1;
        }

        if language.is_token(event.kind) {
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
}

#[test]
fn test_reorder() {
    let lang = LanguageNodes {
        skip_bound: 0,
        token_bound: 2,
        total_bound: 3,
        names: &[],
    };

    let tokens = &[NodeEvent {
        kind: NodeKind::new(1),
        max_lookahead: 0,
        size_or_start_or_children: 0,
    }; 10];

    let mut p = Parser::new(tokens, Vec::new(), lang.clone());

    {
        let c = p.open_span();
        p.next();
        p.next();
        {
            let c = p.open_span();
            {
                let c = p.open_span();
                p.close_span(c, NodeKind::new(2))
            }
            p.next();
            p.close_span(c, NodeKind::new(2))
        }
        p.next();
        p.close_span(c, NodeKind::new(2))
    }

    let mut trace = p.finish();
    trace_postorder_to_preorder(&mut trace, &mut Vec::new(), &lang);

    for event in trace {
        if lang.is_token(event.kind) {
            println!(".");
        } else {
            println!("span {}", event.size_or_start_or_children)
        }
    }
}
