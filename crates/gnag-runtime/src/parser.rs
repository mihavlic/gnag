use crate::{resetable_slice::ResetableSlice, trace::PostorderTrace, NodeEvent, NodeKind};

#[derive(Clone, Copy)]
pub struct SpanStart(pub u32);

#[derive(Clone, PartialEq, Eq)]
pub struct ParserPosition {
    token_position: u32,
    trace_position: u32,
}

pub struct Parser<'a> {
    tokens: ResetableSlice<'a, NodeEvent>,
    tree_trace: Vec<NodeEvent>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [NodeEvent], tree_trace_buffer: Vec<NodeEvent>) -> Parser<'a> {
        let mut tree_trace_buffer = tree_trace_buffer;
        tree_trace_buffer.clear();
        Parser {
            tokens: ResetableSlice::new(tokens),
            tree_trace: tree_trace_buffer,
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
            if !token.kind.is_skip() {
                break;
            }
            self.tree_trace.push(token);
        }

        return consumed_any;
    }

    pub fn peek(&mut self) -> Option<NodeKind> {
        if let Some((slice, _)) = self.tokens.remaining().split_at_checked(4) {
            for token in slice {
                if !token.kind.is_skip() {
                    return Some(token.kind);
                }
            }
        }

        self.peek_slow()
    }

    #[cold]
    fn peek_slow(&mut self) -> Option<NodeKind> {
        for token in self.tokens.remaining() {
            if !token.kind.is_skip() {
                return Some(token.kind);
            }
        }
        return None;
    }

    pub fn next(&mut self) -> Option<NodeKind> {
        let checkpoint = self.tree_trace.len();

        while let Some(&token) = self.tokens.next() {
            self.tree_trace.push(token);
            if !token.kind.is_skip() {
                return Some(token.kind);
            }
        }

        // we undo the pushes if we've reached eof
        // this compiles down to just a few instructions
        self.tree_trace.truncate(checkpoint);

        return None;
    }

    pub fn next_if(&mut self, fun: impl FnOnce(NodeKind) -> bool) -> bool {
        let peek = self.peek();
        if let Some(peek) = peek {
            if fun(peek) {
                self.next();
                return true;
            }
        }
        return false;
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
            data: start.0,
        });
    }

    pub fn finish(self) -> PostorderTrace {
        PostorderTrace::from_raw(self.tree_trace)
    }
}

impl<'a> Parser<'a> {
    pub fn token(&mut self, kind: NodeKind) -> bool {
        self.next_if(|t| t == kind)
    }
    pub fn not(&mut self, kind: NodeKind) -> bool {
        self.next_if(|t| t != kind)
    }
}
