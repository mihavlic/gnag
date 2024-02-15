use crate::convert::ConvertedFile;
use crate::graph::Graph;
use crate::graph::NodeHandle;
use gnag::handle::HandleCounter;
use gnag::handle::TypedHandle;
use gnag::simple_handle;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Write;

simple_handle! {
    pub ScopeHandle
}

impl Display for ScopeHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

pub enum ScopeVisit<'a> {
    Open(&'a ScopeNode),
    Statement(NodeHandle),
    Close(&'a ScopeNode),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScopeKind {
    Loop,
    Block,
}

#[derive(Debug)]
pub struct ScopeNode {
    pub handle: ScopeHandle,
    pub kind: ScopeKind,
    pub start: NodeHandle,
    pub end: NodeHandle,
    pub children: Vec<ScopeNode>,
}

impl ScopeNode {
    pub fn new(handle: ScopeHandle, start: NodeHandle, end: NodeHandle) -> ScopeNode {
        ScopeNode {
            handle,
            kind: ScopeKind::Block,
            start,
            end,
            children: vec![],
        }
    }
    pub fn set_kind(&mut self, kind: ScopeKind) {
        // do not overwrite the kind if it is Loop
        if self.kind == ScopeKind::Block {
            self.kind = kind;
        }
    }
    /// Assumes that `start <= end`
    pub fn contains_range(&self, start: NodeHandle, end: NodeHandle) -> bool {
        self.start <= start && end <= self.end
    }
    /// Find the range of children whose ranges overlap start..end.
    ///
    /// Will enlarge the range in case of partial overlaps.
    ///
    /// # Examples
    /// ```ignore
    /// range = 1..4 //     <--------->
    /// children = [(0..1), (1..3), (3..5), (6..8)]
    /// range = 1..5 //     <------------>
    /// returns = 1..3
    ///
    /// range = 2..5 //     <-------->
    /// children = [(0..1), (2..3),     (6..8)]
    /// range = 2..5 //     <-------->
    /// returns = 1..2
    /// ```
    pub fn find_child_range(
        &self,
        start: &mut NodeHandle,
        end: &mut NodeHandle,
    ) -> std::ops::Range<usize> {
        let start_index = self.children.partition_point(|x| *start > x.end);
        let end_index = self.children.partition_point(|x| *end > x.start);

        if let Some(scope) = self.children.get(start_index) {
            *start = (*start).min(scope.start);
        }
        if let Some(scope) = end_index.checked_sub(1).and_then(|i| self.children.get(i)) {
            *end = (*end).max(scope.end);
        }

        start_index..end_index
    }
    pub fn add_scope(
        &mut self,
        counter: &mut HandleCounter<ScopeHandle>,
        start: NodeHandle,
        end: NodeHandle,
        kind: ScopeKind,
    ) -> ScopeHandle {
        assert!(self.contains_range(start, end));

        for child in &mut self.children {
            if child.contains_range(start, end) {
                let reuse = match kind {
                    ScopeKind::Loop => child.start == start,
                    ScopeKind::Block => child.end == end,
                };
                // no need to recurse deeper, we can use this scope
                if reuse {
                    child.set_kind(kind);
                    return child.handle;
                }
                return child.add_scope(counter, start, end, kind);
            }
        }

        let mut start_copy = start;
        let mut end_copy = end;
        let range = self.find_child_range(&mut start_copy, &mut end_copy);

        assert!(
            match kind {
                ScopeKind::Loop => start == start_copy,
                ScopeKind::Block => end == end_copy,
            },
            "Scope overlaps with existing scope. This is a bug!"
        );

        let handle = counter.next();
        let new = ScopeNode {
            handle,
            kind,
            start: start_copy,
            end: end_copy,
            children: self.children.drain(range.clone()).collect(),
        };

        self.children.insert(range.start, new);
        handle
    }
    pub fn validate(&self, root: bool) {
        match root {
            true => assert!(self.start <= self.end),
            false => assert!(self.start < self.end),
        }
        let mut end = self.start;
        for child in &self.children {
            assert!(end <= child.start);
            child.validate(false);
            end = child.end;
        }
        assert!(end <= self.end);
    }
    pub fn visit_dfs(&self, mut fun: impl FnMut(ScopeVisit)) {
        self.visit_dfs_impl(&mut fun)
    }
    pub fn visit_dfs_impl(&self, fun: &mut dyn FnMut(ScopeVisit)) {
        fun(ScopeVisit::Open(self));
        let mut i = self.start;
        for child in &self.children {
            while i < child.start {
                fun(ScopeVisit::Statement(i));
                i.bump();
            }
            child.visit_dfs_impl(fun);
            i = child.end;
        }
        while i < self.end {
            fun(ScopeVisit::Statement(i));
            i.bump();
        }
        fun(ScopeVisit::Close(self));
    }
    pub fn find_scope_with_end(&self, end: NodeHandle) -> Option<ScopeHandle> {
        let mut this = self;
        'outer: loop {
            if self.end == end {
                return Some(this.handle);
            }

            for child in self.children.iter().rev() {
                if child.start < end && end <= child.end {
                    this = child;
                    continue 'outer;
                }
            }

            return None;
        }
    }
    pub fn find_scope_with_start(&self, start: NodeHandle) -> Option<ScopeHandle> {
        let mut this = self;
        'outer: loop {
            if self.start == start {
                return Some(this.handle);
            }

            for child in self.children.iter() {
                if child.start <= start && start < child.end {
                    this = child;
                    continue 'outer;
                }
            }

            return None;
        }
    }
    #[allow(unused_must_use)]
    pub fn debug_display(&self, buf: &mut dyn Write, graph: &Graph, file: &ConvertedFile) {
        fn print_indent(buf: &mut dyn Write, indent: i32) {
            for _ in 0..indent {
                write!(buf, "  ");
            }
        }

        let mut indent = 0;
        self.visit_dfs(|event| match event {
            ScopeVisit::Open(scope) => {
                print_indent(buf, indent);
                match scope.kind {
                    ScopeKind::Loop => {
                        _ = writeln!(
                            buf,
                            "#{}: {}..{} loop {{",
                            scope.handle.index(),
                            scope.start,
                            scope.end
                        )
                    }
                    ScopeKind::Block => {
                        _ = writeln!(
                            buf,
                            "#{}: {}..{} {{",
                            scope.handle.index(),
                            scope.start,
                            scope.end
                        )
                    }
                }
                indent += 1;
            }
            ScopeVisit::Statement(handle) => {
                let node = graph.get_node(handle).unwrap();
                print_indent(buf, indent);
                node.transition.display(buf, file);
                writeln!(buf);
            }
            ScopeVisit::Close(_) => {
                indent -= 1;
                print_indent(buf, indent);
                writeln!(buf, "}}");
            }
        })
    }
}
