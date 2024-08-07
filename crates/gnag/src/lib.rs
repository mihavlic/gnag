pub mod ast;
pub mod ctx;
pub mod handle;

use std::ops::{Index, Range};

/// Starting code from
///  https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
///  - https://github.com/matklad/resilient-ll-parsing/blob/master/src/lib.rs
///  https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
///  - https://github.com/matklad/minipratt/blob/master/src/bin/pratt.rs


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[rustfmt::skip]
pub enum TreeKind {
    Comment, Newline, Whitespace,

    Ident, Literal, Number,
    ErrorToken,
  
    LParen, RParen, LCurly, RCurly, LBracket, RBracket, LAngle, RAngle,
    TokensKeyword, RulesKeyword, PrattKeyword,
    At, Comma, Dot, Pipe, Colon, Question, Plus, Star, Equals,

    File,
      ErrorTree,
      Attribute,
      TokensOrRules,
        SynRule,
            Parameters,
      SynExpr,
        AtomExpr,
        ParenExpr,
        CallExpr,
        PostExpr,
        BinExpr,
        SeqExpr,
        PrattExpr
}

use ast::ParsedFile;
use TreeKind::*;

#[derive(Clone, Copy, Debug)]
pub struct TokenSpan {
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct StrSpan {
    pub start: u32,
    pub end: u32,
}

impl StrSpan {
    pub fn at(pos: u32) -> StrSpan {
        Self {
            start: pos,
            end: pos,
        }
    }
    #[track_caller]
    pub fn as_str(self, src: &str) -> &str {
        &src[self.start as usize..self.end as usize]
    }
    pub fn contains(self, pos: u32) -> bool {
        pos >= self.start && pos < self.end
    }
    /// Checks whether another span is fully covered by this one, empty spans are never covered.
    pub fn contains_span(self, span: StrSpan) -> bool {
        (span.start < span.end) && (span.start >= self.start) && (span.end <= self.end)
    }
    /// Checks whether another span overlaps with this one. Empty ranges never overlap.
    pub fn overlaps(self, span: StrSpan) -> bool {
        (self.start < span.end) && (span.start < self.end)
    }
}

impl Index<StrSpan> for str {
    type Output = str;
    fn index(&self, index: StrSpan) -> &Self::Output {
        &self[index.start as usize..index.end as usize]
    }
}

impl StrSpan {
    pub fn empty() -> StrSpan {
        Self { start: 0, end: 0 }
    }
    pub fn is_empty(self) -> bool {
        self.end <= self.start
    }
    pub fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    kind: TreeKind,
    span: StrSpan,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Node {
    pub kind: TreeKind,
    pub span: StrSpan,
    pub children: Range<u32>,
}

impl Node {
    pub fn children<'a>(&self, arena: &'a [Node]) -> &'a [Node] {
        &arena[self.children.start as usize..self.children.end as usize]
    }
    pub fn contains(&self, pos: u32) -> bool {
        self.span.contains(pos)
    }
    /// Finds a [`Node`] which contains the given `pos` and has no children.
    pub fn find_leaf<'a>(&'a self, pos: u32, arena: &'a [Node]) -> Option<&'a Node> {
        let mut node = self;
        loop {
            if !node.contains(pos) {
                return None;
            }

            let children = node.children(arena);
            if children.is_empty() {
                return Some(node);
            } else {
                let next = match children.binary_search_by_key(&pos, |k| k.span.start) {
                    Ok(i) => i,
                    Err(i) => i.saturating_sub(1),
                };
                node = &children[next];
            }
        }
    }
    /// Finds the lowest [`Node`] which contains the given `span`.
    pub fn find_covering<'a>(&'a self, span: StrSpan, arena: &'a [Node]) -> Option<&'a Node> {
        let mut node = self;
        loop {
            if !node.span.contains_span(span) {
                return None;
            }

            let children = node.children(arena);
            if children.is_empty() {
                return Some(node);
            } else {
                let next = match children.binary_search_by_key(&span.start, |k| k.span.start) {
                    Ok(i) => i,
                    Err(i) => i.saturating_sub(1),
                };
                let child = &children[next];
                // return current node if the child doesn't contain the span anymore
                if child.span.end < span.end {
                    return Some(node);
                }

                node = child;
            }
        }
    }
    // pub fn find_immediate_child<'a>(&'a self, pos: u32, arena: &'a [Node]) -> Option<&'a Node> {
    //     if !self.contains(pos) {
    //         return None;
    //     }

    //     let children = self.children(arena);
    //     if children.is_empty() {
    //         return None;
    //     } else {
    //         let next = match children.binary_search_by_key(&pos, |k| k.span.start) {
    //             Ok(i) => i,
    //             // we can do a saturating sub, because the actual span is checked in the next iteration
    //             // we've also checked that the `children` are non-empty
    //             Err(i) => i.saturating_sub(1),
    //         };
    //         return Some(&children[next]);
    //     }
    // }
    pub fn visit_children<'a>(
        &'a self,
        pos: u32,
        visitor: &mut dyn ChildVisitor<'a>,
        arena: &'a [Node],
    ) {
        self.visit_downwards_(pos, visitor, arena)
    }
    #[inline]
    fn visit_downwards_<'a>(
        &'a self,
        pos: u32,
        visitor: &mut (impl ChildVisitor<'a> + ?Sized),
        arena: &'a [Node],
    ) {
        if visitor.begin(pos) == NodeVisitDecision::Stop {
            return;
        }

        let mut node = self;
        loop {
            if !node.contains(pos) {
                return;
            }

            let children = node.children(arena);
            if visitor.visit(node) == NodeVisitDecision::Stop || children.is_empty() {
                return;
            } else {
                let next = match children.binary_search_by_key(&pos, |k| k.span.start) {
                    Ok(i) => i,
                    Err(i) => i.saturating_sub(1),
                };
                node = &children[next];
            }
        }
    }
    pub fn find_with_trace<'a>(&'a self, pos: u32, arena: &'a [Node]) -> TreeTrace<'a> {
        let mut trace = TreeTrace::new();
        self.visit_downwards_(pos, &mut trace, arena);
        trace
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeVisitDecision {
    Continue,
    Stop,
}

pub trait ChildVisitor<'a> {
    fn begin(&mut self, _target_pos: u32) -> NodeVisitDecision {
        NodeVisitDecision::Continue
    }
    fn visit(&mut self, node: &'a Node) -> NodeVisitDecision;
}

#[derive(Clone, Debug)]
pub struct TreeTrace<'a> {
    nodes: Vec<&'a Node>,
}

impl<'a> TreeTrace<'a> {
    pub fn new() -> TreeTrace<'a> {
        TreeTrace { nodes: Vec::new() }
    }
    pub fn current(&self) -> Option<&Node> {
        self.nodes.last().copied()
    }
    pub fn current_children<'b>(&'a self, arena: &'b [Node]) -> &'b [Node] {
        self.nodes.last().map_or(&[], |node| node.children(arena))
    }
    pub fn parent(&self) -> Option<&Node> {
        let len = self.nodes.len();
        if len >= 2 {
            self.nodes.get(len - 2).copied()
        } else {
            None
        }
    }

    fn find_current_in_parent(&self, arena: &'a [Node]) -> Option<usize> {
        let parent = self.parent()?;
        let current = self.current().unwrap();
        let children = parent.children(arena);
        let current_index = children
            .binary_search_by_key(&current.span.start, |k| k.span.start)
            .expect("Parent does not contain current??");
        Some(current_index)
    }
    pub fn sibling_before<'b>(&mut self, arena: &'b [Node]) -> Option<&'b Node> {
        let Some(index) = self.find_current_in_parent(arena) else {
            return None;
        };
        let [.., parent, _] = self.nodes.as_mut_slice() else {
            unreachable!()
        };
        if index != 0 {
            if let Some(sibling) = parent.children(arena).get(index - 1) {
                return Some(sibling);
            }
        }
        None
    }
    pub fn sibling_after<'b>(&mut self, arena: &'b [Node]) -> Option<&'b Node> {
        let Some(index) = self.find_current_in_parent(arena) else {
            return None;
        };
        let [.., parent, _] = self.nodes.as_mut_slice() else {
            unreachable!()
        };
        if let Some(sibling) = parent.children(arena).get(index + 1) {
            return Some(sibling);
        }
        None
    }

    /// Enters the current node's child (the index relates to the array returned by [`Self::current_children()`])
    ///
    /// Panics if the index is out of bounds.
    #[track_caller]
    pub fn enter_child(&mut self, index: usize, arena: &'a [Node]) {
        let current = self.current().expect("TreeTrace is empty");
        let child = current
            .children(arena)
            .get(index)
            .expect("index out of bounds");
        self.nodes.push(child);
    }
    /// Pops the current node, making its parent current. Does nothing if empty.
    pub fn enter_parent(&mut self) {
        self.nodes.pop();
    }
    pub fn enter_sibling_before(&mut self, arena: &'a [Node]) {
        if let Some(sibling) = self.sibling_before(arena) {
            *self.nodes.last_mut().unwrap() = sibling;
        }
    }
    pub fn enter_sibling_after(&mut self, arena: &'a [Node]) {
        if let Some(sibling) = self.sibling_after(arena) {
            *self.nodes.last_mut().unwrap() = sibling;
        }
    }
    pub fn enter_leftmost_leaf(&mut self, arena: &'a [Node]) {
        let Some(mut current) = self.current() else {
            return;
        };

        while let Some(leftmost) = current.children(arena).first() {
            current = leftmost;
            self.nodes.push(leftmost);
        }
    }
    pub fn enter_rightmost_leaf(&mut self, arena: &'a [Node]) {
        let Some(mut current) = self.current() else {
            return;
        };

        while let Some(leftmost) = current.children(arena).last() {
            current = leftmost;
            self.nodes.push(leftmost);
        }
    }
    // pub fn enter_sibling_after(&mut self, arena: &'a [Node]) {
    //     if let Some(sibling) = self.sibling_after(arena) {
    //         *self.nodes.last_mut().unwrap() = sibling;
    //     }
    // }
    /// Returns an iterator visiting the current current node and then its parents.
    pub fn backward_iter(&self) -> std::iter::Copied<std::iter::Rev<std::slice::Iter<'_, &Node>>> {
        self.nodes.iter().rev().copied()
    }
    /// Returns an iterator visiting the current current node and then its parents.
    pub fn ancestor_iter(&self) -> std::iter::Copied<std::iter::Rev<std::slice::Iter<'_, &Node>>> {
        let len = self.nodes.len();
        let slice = if len >= 2 {
            &self.nodes[..len - 1]
        } else {
            &[]
        };
        slice.iter().rev().copied()
    }
    pub fn backward_contain_kind(&self, kind: TreeKind) -> bool {
        for node in self.backward_iter() {
            if node.kind == kind {
                return true;
            }
        }
        false
    }
    pub fn ancestor_contain_kind(&self, kind: TreeKind) -> bool {
        for node in self.ancestor_iter() {
            if node.kind == kind {
                return true;
            }
        }
        false
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

impl<'a> ChildVisitor<'a> for TreeTrace<'a> {
    fn begin(&mut self, target_pos: u32) -> NodeVisitDecision {
        if let Some(current) = self.current() {
            if !current.span.contains(target_pos) {
                return NodeVisitDecision::Stop;
            }
        }
        NodeVisitDecision::Continue
    }

    fn visit(&mut self, node: &'a Node) -> NodeVisitDecision {
        #[cfg(debug_assertions)]
        if let Some(current) = self.current() {
            if !current.span.contains_span(node.span) {
                unreachable!();
            }
        }
        self.nodes.push(node);
        NodeVisitDecision::Continue
    }
}

impl<'a, F: FnMut(&'a Node) -> NodeVisitDecision> ChildVisitor<'a> for F {
    fn visit(&mut self, node: &'a Node) -> NodeVisitDecision {
        self(node)
    }
}

impl Node {
    pub fn recursive_format_into(
        &self,
        buf: &mut dyn std::fmt::Write,
        src: &str,
        nodes: &[Node],
        errors: &mut std::slice::Iter<'_, SpannedError>,
        level: usize,
    ) {
        for _ in 0..level {
            _ = buf.write_str("  ");
        }
        _ = write!(buf, "{:?}", self.kind);
        if self.children.is_empty() {
            _ = write!(buf, " {:?}", self.span.as_str(src));
        }
        while let Some(peek) = errors.clone().next() {
            if self.span == peek.span {
                errors.next();
                _ = write!(buf, " !!{}", peek.err);
            } else {
                break;
            }
        }
        _ = write!(buf, "\n");
        for child in self.children(nodes) {
            child.recursive_format_into(buf, src, nodes, errors, level + 1);
        }
    }
    pub fn pretty_print(&self, src: &str, nodes: &[Node], errors: &[SpannedError]) -> String {
        // TODO what to do about errors?
        let mut buf = String::new();
        self.recursive_format_into(&mut buf, src, nodes, &mut errors.iter(), 0);
        buf
    }
    pub fn pretty_print_with_file(&self, src: &str, file: &ParsedFile) -> String {
        self.pretty_print(src, &file.arena, &[])
    }
}

pub struct Lexer<'a> {
    str: &'a [u8],
    pos: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(str: &'a [u8]) -> Self {
        Self { str, pos: 0 }
    }

    pub fn pos(&self) -> u32 {
        self.pos
    }

    pub fn span_since(&self, start: u32) -> StrSpan {
        StrSpan {
            start,
            end: self.pos(),
        }
    }

    pub fn restore_pos(&mut self, pos: u32) {
        debug_assert!(pos as usize <= self.str.len());
        self.pos = pos;
    }

    pub fn is_empty(&self) -> bool {
        self.pos as usize == self.str.len()
    }

    pub fn next(&mut self) -> Option<u8> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let byte = self.str[pos];
            self.pos += 1;
            Some(byte)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<u8> {
        let pos = self.pos as usize;
        if pos < self.str.len() {
            let byte = self.str[pos];
            Some(byte)
        } else {
            None
        }
    }

    pub fn is_boundary(&self, predicate: impl std::ops::Fn(u8) -> bool) -> bool {
        match self.peek() {
            Some(b) => !predicate(b),
            None => true,
        }
    }

    pub fn consume(&mut self, value: u8) -> bool {
        if self.peek() == Some(value) {
            self.next();
            true
        } else {
            false
        }
    }

    pub fn consume_while(&mut self, predicate: impl std::ops::Fn(u8) -> bool) -> StrSpan {
        let start = self.pos();
        while let Some(c) = self.peek() {
            if predicate(c) {
                self.next();
            } else {
                break;
            }
        }
        StrSpan {
            start,
            end: self.pos(),
        }
    }

    pub fn sequence(&mut self, sequence: &[u8]) -> bool {
        if self.str[self.pos as usize..].starts_with(sequence) {
            self.pos += sequence.len() as u32;
            true
        } else {
            false
        }
    }
}

pub fn lex(l: &mut Lexer) -> (Vec<Token>, Vec<Token>) {
    let mut tokens = Vec::new();
    let mut trivia = Vec::new();
    while !l.is_empty() {
        let pos = l.pos();
        let kind = match l.next().unwrap() {
            b'\n' => Newline,
            b' ' | b'\t' | b'\r' => {
                l.consume_while(|c| b" \t\r".contains(&c));
                Whitespace
            }
            b'#' => {
                l.consume_while(|c| c != b'\n');
                Comment
            }
            b'{' => LCurly,
            b'}' => RCurly,
            b'(' => LParen,
            b')' => RParen,
            b'[' => LBracket,
            b']' => RBracket,
            b'<' => LAngle,
            b'>' => RAngle,
            b'?' => Question,
            b'|' => Pipe,
            b'*' => Star,
            b'+' => Plus,
            b'@' => At,
            b':' => Colon,
            b',' => Comma,
            b'.' => Dot,
            b'=' => Equals,
            _ => 'choice: {
                let is_ident_char = |c| matches!(c, b'_' | b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9');

                l.restore_pos(pos);
                if l.sequence(b"tokens") && l.is_boundary(is_ident_char) {
                    break 'choice TokensKeyword;
                }
                if l.sequence(b"rules") && l.is_boundary(is_ident_char) {
                    break 'choice RulesKeyword;
                }
                if l.sequence(b"pratt") && l.is_boundary(is_ident_char) {
                    break 'choice PrattKeyword;
                }
                let is_regex = l.consume(b'r');
                if l.consume(b'\'') {
                    while let Some(next) = l.next() {
                        match next {
                            b'\\' if !is_regex => _ = l.next(),
                            b'\'' => break 'choice Literal,
                            _ => {}
                        }
                    }
                }

                l.restore_pos(pos);
                if !l.consume_while(is_ident_char).is_empty() {
                    break 'choice Ident;
                }
                l.restore_pos(pos);
                {
                    let span = l.consume_while(|c| !c.is_ascii_whitespace());
                    if span.is_empty() {
                        l.next();
                    }
                    ErrorToken
                }
            }
        };

        let span = l.span_since(pos);
        assert!(!span.is_empty());

        if kind == Whitespace || kind == Comment {
            trivia.push(Token { kind, span })
        } else {
            tokens.push(Token { kind, span })
        }
    }
    return (tokens, trivia);
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SpanStart(u32);

#[derive(Clone, Copy)]
pub struct ParserCheckpoint {
    pos: u32,
    spans_len: u32,
    errors_len: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct TreeSpan {
    pub kind: TreeKind,
    pub span: StrSpan,
}

#[derive(Clone, Hash, Debug)]
pub struct SpannedError {
    pub span: StrSpan,
    pub err: String,
}

pub struct Parser<'a> {
    tokens: Vec<Token>,
    trivia: Vec<Token>,
    pos: u32,
    spans: Vec<TreeSpan>,
    errors: Vec<SpannedError>,
    src: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, tokens: Vec<Token>, trivia: Vec<Token>) -> Parser<'a> {
        Parser {
            tokens,
            trivia,
            pos: 0,
            spans: Vec::new(),
            errors: Vec::new(),
            src,
        }
    }
    pub fn finish(self) -> Vec<SpannedError> {
        self.errors
    }

    // We push tree spans (and their errors) when we close them, so we end up with a reversed topological order; the root will always be last.
    // Let there be tree:
    //  |-----root----|
    //  |--a---| |--b-|
    //  | |-c| | |    |
    //  0123456789abcdef  -- indices of tokens
    // The spans will be like so:
    //  (label, start..end)
    //  [ (b, 9..f) (c, 2..6) (a, 0..8) (root, 0..f) ]
    pub fn build_tree(&self, arena: &mut Vec<Node>) -> Node {
        arena.reserve(self.spans.len() + self.tokens.len() + self.trivia.len());

        let mut merged_tokens = {
            let mut tokens = self.tokens.iter().copied();
            let mut trivia = self.trivia.iter().copied();
            let mut len = self.tokens.len() + self.trivia.len();

            std::iter::from_fn(move || {
                if len > 0 {
                    len -= 1;

                    let token_start = tokens.clone().next().map_or(u32::MAX, |a| a.span.start);
                    let trivia_start = trivia.clone().next().map_or(u32::MAX, |a| a.span.start);

                    debug_assert_ne!(token_start, trivia_start);
                    if token_start < trivia_start {
                        Some(tokens.next().unwrap())
                    } else {
                        Some(trivia.next().unwrap())
                    }
                } else {
                    None
                }
            })
        };

        let mut stack: Vec<Node> = Vec::new();

        let mut pos = 0;
        for span in &self.spans {
            debug_assert!(!span.span.is_empty());

            let StrSpan { start, end } = span.span;

            // we split the token pushing into two branches depending on whether the next span
            // is closing over already pushed elements or is just starting
            //
            // this specialization actually makes it faster (maybe only on very large files?)
            let start_idx = if pos <= start {
                // the cursor has yet to enter the span
                let mut start_idx = stack.len();
                while pos < end {
                    let token = merged_tokens.next().unwrap();
                    pos = token.span.end;
                    if token.span.start == start {
                        start_idx = stack.len();
                    }
                    stack.push(Node {
                        kind: token.kind,
                        span: token.span,
                        children: 0..0,
                    });
                }

                start_idx
            } else {
                // the cursor is already in the span, need to find the start
                let start_idx = stack
                    .binary_search_by_key(&start, |s| s.span.start)
                    .unwrap();

                while pos < end {
                    let token = merged_tokens.next().unwrap();
                    pos = token.span.end;
                    stack.push(Node {
                        kind: token.kind,
                        span: token.span,
                        children: 0..0,
                    });
                }

                start_idx
            };

            let start = arena.len() as u32;
            arena.extend_from_slice(&stack[start_idx..]);
            let end = arena.len() as u32;

            stack.truncate(start_idx);
            stack.push(Node {
                kind: span.kind,
                span: span.span,
                children: start..end,
            });
        }

        assert_eq!(stack.len(), 1);
        stack.pop().unwrap()
    }

    pub fn checkpoint(&self) -> ParserCheckpoint {
        ParserCheckpoint {
            pos: self.pos,
            spans_len: self.spans.len().try_into().unwrap(),
            errors_len: self.errors.len().try_into().unwrap(),
        }
    }

    pub fn restore(&mut self, checkpoint: ParserCheckpoint) {
        let ParserCheckpoint {
            pos,
            spans_len,
            errors_len,
        } = checkpoint;

        self.pos = pos;

        assert!(spans_len as usize <= self.spans.len());
        self.spans.truncate(spans_len as usize);

        assert!(errors_len as usize <= self.errors.len());
        self.errors.truncate(errors_len as usize);
    }

    pub fn open(&mut self) -> SpanStart {
        let start = self
            .tokens
            .get(self.pos as usize)
            .map_or(0, |s| s.span.start);
        SpanStart(start)
    }

    pub fn close(&mut self, m: SpanStart, kind: TreeKind) -> StrSpan {
        let end = self
            .tokens
            .get(self.pos.saturating_sub(1) as usize)
            .map_or(0, |s| s.span.end);
        let tree = TreeSpan {
            kind,
            span: StrSpan { start: m.0, end },
        };
        debug_assert!(!tree.span.is_empty(), "Span is empty {tree:?}");
        self.spans.push(tree);
        tree.span
    }

    pub fn close_toplevel(&mut self, _m: SpanStart, kind: TreeKind) -> StrSpan {
        let tree = TreeSpan {
            kind,
            span: StrSpan {
                start: 0,
                end: self.src.len().try_into().unwrap(),
            },
        };
        self.spans.push(tree);
        tree.span
    }

    pub fn close_with_err(&mut self, m: SpanStart, err: impl ToString) {
        let kind = TreeKind::ErrorTree;
        let err = err.to_string();
        let span = self.close(m, kind);
        self.errors.push(SpannedError { span, err });
    }

    pub fn error(&mut self, err: impl ToString) {
        let err = err.to_string();
        let end = self.tokens.get(self.pos as usize).map_or(0, |s| s.span.end);
        self.errors.push(SpannedError {
            span: StrSpan {
                start: end,
                end: end,
            },
            err,
        });
    }

    pub fn advance(&mut self) {
        assert!(!self.eof());
        self.pos += 1;
    }

    pub fn try_advance(&mut self) {
        if !self.eof() {
            self.pos += 1;
        }
    }

    #[inline]
    pub fn eof(&self) -> bool {
        self.pos as usize == self.tokens.len()
    }

    pub fn peek(&self) -> Option<TreeKind> {
        self.nth(0)
    }

    pub fn nth(&self, lookahead: u32) -> Option<TreeKind> {
        self.nth_impl(lookahead).map(|it| it.kind)
    }

    pub fn nth_impl(&self, lookahead: u32) -> Option<&Token> {
        self.tokens.get((self.pos + lookahead) as usize)
    }

    #[inline]
    pub fn at(&self, kind: TreeKind) -> bool {
        self.nth(0) == Some(kind)
    }

    #[inline]
    pub fn at_any(&self, kinds: &[TreeKind]) -> bool {
        if let Some(any) = self.nth(0) {
            kinds.contains(&any)
        } else {
            false
        }
    }

    pub fn token(&mut self, kind: TreeKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub fn expect(&mut self, kind: TreeKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            self.error(format!("Expected '{kind:?}'"));
            false
        }
    }
}

pub trait RecoverMethod {
    fn recover(&self, p: &mut Parser);
}

pub struct StepRecoverUntil<'a>(&'a [TreeKind]);
impl<'a> RecoverMethod for StepRecoverUntil<'a> {
    #[cold]
    fn recover(&self, p: &mut Parser) {
        let m = p.open();
        p.try_advance();
        while !(p.eof() || p.at_any(self.0)) {
            p.advance()
        }
        p.close_with_err(m, "Unexpected input");
    }
}

// @root
// File = (Newline | Tokens | Rules)*
pub fn file(p: &mut Parser) -> bool {
    let r = StepRecoverUntil(&[TokensKeyword, RulesKeyword]);
    let m = p.open();
    while !p.eof() {
        'choice: {
            let checkpoint = p.checkpoint();
            if p.token(Newline) {
                break 'choice;
            }

            if tokens_or_rules(p) {
                break 'choice;
            }

            p.restore(checkpoint);
            r.recover(p);
        }
    }
    p.close_toplevel(m, TreeKind::File);
    true
}

fn inline_rules_block(p: &mut Parser) {
    while p.token(Newline) {}
    p.token(LCurly);
    loop {
        let checkpoint = p.checkpoint();
        if p.token(Newline) {
            continue;
        }
        if rule(p) {
            continue;
        }
        p.restore(checkpoint);
        break;
    }
    p.token(RCurly);
}

// TokensOrRules = ('tokens' | 'rules') '{' (Newline | Rule)* '}'
fn tokens_or_rules(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(TokensKeyword) && !p.token(RulesKeyword) {
        return false;
    }

    inline_rules_block(p);

    p.close(m, TreeKind::TokensOrRules);
    true
}

// Attribute = '@' Ident
fn attribute(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(At) {
        return false;
    }
    p.expect(Ident);
    p.token(Newline);

    p.close(m, TreeKind::Attribute);
    true
}

// Parameters = '(' <comma_list Ident> ')'
fn parameters(p: &mut Parser) -> bool {
    let m = p.open();

    if !p.token(LParen) {
        return false;
    }
    loop {
        if !p.token(Ident) {
            break;
        }
        if !p.token(Comma) {
            break;
        }
    }
    p.expect(RParen);

    p.close(m, TreeKind::Parameters);
    true
}

// Rule = Attribute* Ident Parameters? '=' Expr
fn rule(p: &mut Parser) -> bool {
    let m = p.open();

    while attribute(p) {}

    if !p.token(Ident) {
        return false;
    }

    parameters(p);

    p.token(Equals);
    expr(p, 0);
    p.token(Newline);

    p.close(m, TreeKind::SynRule);
    true
}

// Expr = pratt {
//     Atom = Ident | String | RegexString
//     CallExpr = '<' Ident Expr? '>'
//     ParenExpr = '(' Expr ')'
//     PrattExpr = 'pratt' '{' (Newline | Rule)* '}'
//
//     PostExpr = Expr ('?' | '*' | '+')
//     SeqExpr = Expr Expr+
//     BinExpr = Expr '|' Expr
// }

// atom bp
//  '<'  _ _
//  '('  _ _
// postfix bp
//  '?'  5 _
//  '+'  5 _
//  '*'  5 _
//  Expr 3 _
// binary bp
//  '|'  2 1

fn base_expr(p: &mut Parser) -> bool {
    let m = p.open();
    let Some(peek) = p.peek() else {
        return false;
    };
    match peek {
        Ident | Literal => {
            p.advance();
            p.close(m, TreeKind::AtomExpr);
        }
        LParen => {
            p.advance();
            expr(p, 0);
            p.expect(RParen);
            p.close(m, TreeKind::ParenExpr);
        }
        LAngle => {
            p.advance();
            p.expect(Ident);
            expr(p, 0);
            p.expect(RAngle);
            p.close(m, TreeKind::CallExpr);
        }
        PrattKeyword => {
            p.advance();
            inline_rules_block(p);
            p.close(m, TreeKind::PrattExpr);
        }
        _ => return false,
    }
    true
}

fn expr(p: &mut Parser, min_bp: u8) -> bool {
    let m = p.open();

    if !base_expr(p) {
        return false;
    }
    while let Some(peek) = p.peek() {
        match peek {
            Question | Plus | Star => {
                // bp table lookup
                let bp = (5, ());
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                p.close(m, TreeKind::PostExpr);
                continue;
            }
            Pipe => {
                // bp table lookup
                let bp = (2, 1);
                if bp.0 <= min_bp {
                    break;
                }

                p.advance();
                expr(p, bp.1);
                p.close(m, TreeKind::BinExpr);
                continue;
            }
            Ident | Literal | LAngle | LParen | At => {
                // bp table lookup
                let bp = (3, ());
                if bp.0 <= min_bp {
                    break;
                }

                let mut first = true;
                while expr(p, bp.0) {
                    first = false;
                }

                if !first {
                    p.close(m, TreeKind::SeqExpr);
                    continue;
                }
            }
            _ => {}
        }

        break;
    }

    true
}

#[test]
fn node_find() {
    let str = "rules { A = B | C }";

    let mut lexer = Lexer::new(str.as_bytes());

    let (tokens, trivia) = lex(&mut lexer);
    let mut parser = crate::Parser::new(str, tokens, trivia);
    file(&mut parser);

    let mut arena = Vec::new();
    let root = parser.build_tree(&mut arena);

    assert_eq!(
        root.find_leaf(0, &arena),
        Some(&Node {
            kind: RulesKeyword,
            span: StrSpan { start: 0, end: 5 },
            children: 0..0
        })
    );
}
