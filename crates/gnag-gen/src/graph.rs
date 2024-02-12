use std::fmt::{Display, Formatter, Write};

use gnag::{
    ast::ParsedFile,
    handle::{HandleCounter, HandleVec, SecondaryVec, TypedHandle},
    simple_handle,
};

use crate::{
    convert::{ConvertedFile, RuleExpr, RuleHandle, TokenHandle},
    lower::LoweredFile,
};

#[derive(Clone, Debug, Copy)]
pub enum Transition {
    Error,
    Fail,
    Token(TokenHandle),
    Rule(RuleHandle),
    // builtins
    Any,
    Not(TokenHandle),
    // function start/end
    StartSpan,
    CloseSpan(RuleHandle),
    ReturnFail,
}

impl Transition {
    pub fn display(
        self,
        f: &mut dyn Write,
        file: &crate::convert::ConvertedFile,
    ) -> std::fmt::Result {
        match self {
            Transition::Error => write!(f, "Error"),
            Transition::Fail => write!(f, "Fail"),
            Transition::Token(a) => write!(f, "Token({})", file.tokens[a].name),
            Transition::Rule(a) => write!(f, "Rule({})", file.rules[a].name),
            Transition::Any => write!(f, "Any"),
            Transition::Not(a) => write!(f, "Not({})", file.tokens[a].name),

            Transition::StartSpan => write!(f, "StartSpan"),
            Transition::CloseSpan(a) => write!(f, "CloseSpan({})", file.rules[a].name),
            Transition::ReturnFail => write!(f, "ReturnFail"),
        }
    }
}

simple_handle! {
    pub NodeHandle
}

#[derive(Clone, Copy)]
pub struct IncomingEdge {
    pub from: NodeHandle,
    pub is_fail: bool,
}

struct PegNode {
    transition: Transition,
    success: Option<NodeHandle>,
    fail: Option<NodeHandle>,
}

impl PegNode {
    fn new(transition: Transition) -> PegNode {
        Self {
            transition,
            success: None,
            fail: None,
        }
    }
    fn connect_edge(&mut self, is_fail: bool, to: NodeHandle) {
        if is_fail {
            assert!(self.fail.is_none());
            self.fail = Some(to);
        } else {
            assert!(self.success.is_none());
            self.success = Some(to);
        }
    }
    fn for_edges(&self, mut fun: impl FnMut(NodeHandle)) {
        if let Some(success) = self.success {
            fun(success);
        }
        if let Some(fail) = self.fail {
            fun(fail);
        }
    }
}

struct PegEdges {
    success: Vec<IncomingEdge>,
    fail: Vec<IncomingEdge>,
}

impl PegEdges {
    pub fn merged_edges(&self) -> Vec<IncomingEdge> {
        let mut vec = Vec::with_capacity(self.success.len() + self.fail.len());
        vec.extend_from_slice(&self.fail);
        vec.extend_from_slice(&self.success);
        vec
    }
}

struct GraphBuilder {
    nodes: HandleVec<NodeHandle, PegNode>,
    // TODO spans
    errors: Vec<String>,
}

impl GraphBuilder {
    fn new() -> GraphBuilder {
        GraphBuilder {
            nodes: HandleVec::new(),
            errors: Vec::new(),
        }
    }
    fn connect_edges(
        &mut self,
        node: NodeHandle,
        incoming: impl IntoIterator<Item = IncomingEdge>,
    ) {
        for edge in incoming {
            self.nodes[edge.from].connect_edge(edge.is_fail, node);
        }
    }
    fn new_node(
        &mut self,
        transition: Transition,
        incoming: impl IntoIterator<Item = IncomingEdge>,
    ) -> NodeHandle {
        let handle = self.nodes.push(PegNode::new(transition));
        self.connect_edges(handle, incoming);
        handle
    }
    fn peek_next_node(&self) -> NodeHandle {
        self.nodes.next_handle()
    }
    fn get_node(&self, node: NodeHandle) -> Option<&PegNode> {
        self.nodes.get(node)
    }
    fn iter_nodes(
        &self,
    ) -> impl Iterator<Item = (TapeOffset, &PegNode)> + Clone + ExactSizeIterator + DoubleEndedIterator
    {
        self.nodes.iter_kv().map(|(k, v)| (TapeOffset::from(k), v))
    }
    #[allow(unused_must_use)]
    fn debug_graphviz(
        &self,
        buf: &mut dyn Write,
        subgraph: &str,
        index_offset: usize,
        file: &crate::convert::ConvertedFile,
    ) {
        writeln!(buf, "subgraph cluster_{subgraph} {{");
        writeln!(buf, "    label={subgraph:?}");
        for (k, v) in self.nodes.iter_kv() {
            let offset_index = k.index() + index_offset;
            writeln!(buf, "    v{offset_index}[label={}]", k.index());

            if v.success == v.fail {
                print_dot_edge(
                    buf,
                    k,
                    v.success,
                    v.transition,
                    Some("color=purple"),
                    index_offset,
                    file,
                );
            } else {
                print_dot_edge(buf, k, v.success, v.transition, None, index_offset, file);
                print_dot_edge(
                    buf,
                    k,
                    v.fail,
                    Transition::Fail,
                    Some("color=red"),
                    index_offset,
                    file,
                );
            }
        }
        writeln!(buf, "}}");
    }
    fn debug_statements(&self, buf: &mut dyn Write, file: &ConvertedFile) {
        let need_label = self.analyze_control_flow();

        #[allow(unused_must_use)]
        for (handle, node) in self.iter_nodes() {
            let prev = handle.0.checked_sub(1).map(NodeHandle);
            let next = TapeOffset::from(handle).next();

            {
                let label = need_label[handle];
                let is_target = label.is_target;
                let previous_is_reachable =
                    prev.map(|n| need_label[n].is_reachable).unwrap_or(true);
                let is_dead = !label.is_reachable && (previous_is_reachable || is_target);

                if is_target {
                    write!(buf, "{}", handle.0);
                }
                if is_dead {
                    if is_target {
                        write!(buf, " ");
                    }
                    write!(buf, "dead");
                }
                if is_target || is_dead {
                    write!(buf, ":\n");
                }
            }

            write!(buf, "  ");
            node.transition.display(buf, file);

            let mut print_target = |jump: Option<NodeHandle>| {
                if let Some(jump) = jump {
                    if jump == next {
                        write!(buf, " ↓");
                    } else {
                        write!(buf, " {}", jump.0);
                    }
                } else {
                    write!(buf, " _");
                }
            };

            print_target(node.success);
            print_target(node.fail);
            write!(buf, "\n");
        }
    }
    fn analyze_control_flow(&self) -> HandleVec<TapeOffset, StatementLabel> {
        let mut need_label = self.nodes.map_fill(StatementLabel::default());
        if let Some(first) = need_label.first_mut() {
            first.is_reachable = true;
        }

        for (current, node) in self.iter_nodes() {
            let next = current.next();
            node.for_edges(|jump| {
                if next != jump.into() {
                    need_label[jump].is_target = true;
                }
                if need_label[current].is_reachable {
                    need_label[jump].is_reachable = true;
                }
            });
        }
        need_label
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Default)]
struct StatementLabel {
    is_target: bool,
    is_reachable: bool,
}

#[allow(unused_must_use)]
fn print_dot_edge(
    buf: &mut dyn Write,
    from: NodeHandle,
    to: Option<NodeHandle>,
    transition: Transition,
    style: Option<&str>,
    index_offset: usize,
    file: &ConvertedFile,
) {
    let start = from.index() + index_offset;
    let (end, suffix) = if let Some(to) = to {
        (to.index() + index_offset, "")
    } else {
        writeln!(buf, "    v{start}_dangling[style=invis]");
        (start, "_dangling")
    };

    write!(buf, "    v{start} -> v{end}{suffix}[label=\"");
    transition.display(buf, file);
    write!(buf, "\"");

    if let Some(style) = style {
        write!(buf, ",{style}");
    }
    write!(buf, "]\n");
}

impl GraphBuilder {
    pub fn convert_expr(&mut self, expr: &RuleExpr, incoming: Vec<IncomingEdge>) -> PegEdges {
        match expr {
            RuleExpr::Empty => PegEdges {
                success: incoming,
                fail: vec![],
            },
            // some error that has already been reported, pass it along in a dummy state transition
            RuleExpr::Error => self.error_transition(incoming),
            RuleExpr::Token(token) => self.single_transition(incoming, Transition::Token(*token)),
            RuleExpr::Rule(rule) => self.single_transition(incoming, Transition::Rule(*rule)),
            RuleExpr::Sequence(vec) => {
                let mut fail = Vec::new();
                let mut success = incoming;

                let mut commit = false;
                for rule in vec {
                    let incoming = std::mem::take(&mut success);
                    let mut result = self.convert_expr(rule, incoming);

                    let fail_dest = match commit {
                        true => &mut success,
                        false => &mut fail,
                    };

                    fail_dest.append(&mut result.fail);
                    success.append(&mut result.success);

                    // TODO user-controlled commit
                    commit = true;
                }

                PegEdges { success, fail }
            }
            RuleExpr::Choice(vec) => {
                let mut fail = incoming;
                let mut success = Vec::new();

                for rule in vec {
                    let incoming = std::mem::take(&mut fail);
                    let mut result = self.convert_expr(rule, incoming);

                    fail = result.fail;
                    success.append(&mut result.success);
                }

                PegEdges { success, fail }
            }
            RuleExpr::Loop(expr) => {
                // Loop('a')
                //
                //    ┌─►* root
                // 'a'└──┤
                //       │ fail
                //       ▼
                //       * done

                let next = self.peek_next_node();
                let mut result = self.convert_expr(expr, incoming);
                self.verify_next_node_exists(next, &mut result);

                // connect the looping edges to the start
                self.connect_edges(next, result.success);

                PegEdges {
                    success: result.fail,
                    fail: vec![],
                }
            }
            RuleExpr::OneOrMore(expr) => {
                let lowered =
                    RuleExpr::Sequence(vec![(**expr).clone(), RuleExpr::Loop(expr.clone())]);
                self.convert_expr(&lowered, incoming)
            }
            RuleExpr::Maybe(expr) => {
                let result = self.convert_expr(expr, incoming);
                PegEdges {
                    success: result.merged_edges(),
                    fail: vec![],
                }
            }
            RuleExpr::Any => self.single_transition(incoming, Transition::Any),
            RuleExpr::Not(expr) => {
                if let RuleExpr::Token(token) = **expr {
                    self.single_transition(incoming, Transition::Not(token))
                } else {
                    self.errors
                        .push("RuleExpr::Not only works with tokens".to_owned());
                    self.error_transition(incoming)
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                // SeparatedList('a', ',')
                //      start
                //   ┌─►*──┐
                //  ,│  │a │
                //   │  ▼  │
                //   └──*  │fail
                // fail │  │
                //      ▼  │
                // done *◄─┘

                let next = self.peek_next_node();
                let mut element = self.convert_expr(element, incoming);
                self.verify_next_node_exists(next, &mut element);

                let mut separator = self.convert_expr(separator, element.success);
                self.connect_edges(next, separator.success);

                let mut fail = element.fail;
                fail.append(&mut separator.fail);

                PegEdges {
                    success: fail,
                    fail: vec![],
                }
            }
            RuleExpr::InlineParameter(_) | RuleExpr::InlineCall(_) => {
                unreachable!("These should have been eliminated during lowering")
            }
        }
    }
    fn verify_next_node_exists(&mut self, next: NodeHandle, result: &mut PegEdges) {
        if self.get_node(next).is_none() {
            self.errors.push("Loop body generated no nodes".to_owned());
            *result = self.error_transition(result.merged_edges());
        }
    }
    fn error_transition(&mut self, incoming: Vec<IncomingEdge>) -> PegEdges {
        self.single_transition(incoming, Transition::Error)
    }
    fn single_transition(
        &mut self,
        incoming: Vec<IncomingEdge>,
        transition: Transition,
    ) -> PegEdges {
        let node = self.new_node(transition, incoming);
        PegEdges {
            success: vec![IncomingEdge {
                from: node,
                is_fail: false,
            }],
            fail: vec![IncomingEdge {
                from: node,
                is_fail: true,
            }],
        }
    }
}

#[derive(Clone, Default)]
struct StatementJumps {
    block_start: Option<NodeHandle>,
    loop_end: Option<NodeHandle>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ScopeKind {
    Loop,
    Block,
}

simple_handle! {
    TapeOffset, ScopeHandle
}

impl From<NodeHandle> for TapeOffset {
    fn from(value: NodeHandle) -> Self {
        TapeOffset(value.0)
    }
}

impl From<usize> for TapeOffset {
    fn from(value: usize) -> Self {
        TapeOffset(value.try_into().unwrap())
    }
}

impl TapeOffset {
    fn prev(self) -> Option<TapeOffset> {
        self.0.checked_sub(1).map(TapeOffset)
    }
    fn next(self) -> TapeOffset {
        TapeOffset(self.0 + 1)
    }
    fn bump(&mut self) {
        self.0 += 1;
    }
}

enum CfgAction {
    Break(ScopeHandle),
    Continue(ScopeHandle),
    None,
}

enum Statement {
    Open(ScopeHandle),
    Close(ScopeHandle),
    Switch {
        condition: NodeHandle,
        success: CfgAction,
        fail: CfgAction,
    },
}

enum ScopeVisit<'a> {
    Open(&'a ScopeNode),
    Statement(TapeOffset),
    Close(&'a ScopeNode),
}

#[derive(Debug)]
struct ScopeNode {
    handle: ScopeHandle,
    kind: ScopeKind,
    start: TapeOffset,
    end: TapeOffset,
    children: Vec<ScopeNode>,
}

impl ScopeNode {
    fn set_kind(&mut self, kind: ScopeKind) {
        // do not overwrite the kind if it is Loop
        if self.kind == ScopeKind::Block {
            self.kind = kind;
        }
    }
    /// Assumes that `start <= end`
    fn contains_range(&self, start: TapeOffset, end: TapeOffset) -> bool {
        self.start <= start && end <= self.end
    }
    /// Find the range of children whose ranges overlap start..end.
    ///
    /// Will enlarge the range in case of partial overlaps.
    ///
    /// # Examples
    /// ```
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
    fn find_child_range(
        &self,
        start: &mut TapeOffset,
        end: &mut TapeOffset,
    ) -> std::ops::Range<usize> {
        let mut start_index = 0;
        let mut end_index = self.children.len();

        for (i, child) in self.children.iter().enumerate() {
            if *start < child.end {
                start_index = i;
                *start = (*start).min(child.start);
                break;
            }
        }

        for (child, i) in self.children[start_index..].iter().zip(start_index..) {
            if *end > child.start {
                end_index = i + 1;
                *end = (*end).max(child.end);
            }
            if *end <= child.start {
                break;
            }
        }

        start_index..end_index
    }
    fn add_scope(
        &mut self,
        counter: &mut HandleCounter<ScopeHandle>,
        start: TapeOffset,
        end: TapeOffset,
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
    fn visit_dfs(&self, mut fun: impl FnMut(ScopeVisit)) {
        self.visit_dfs_impl(&mut fun)
    }
    fn visit_dfs_impl(&self, fun: &mut dyn FnMut(ScopeVisit)) {
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
    fn find_scope_with_end(&self, end: TapeOffset) -> Option<ScopeHandle> {
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
    fn find_scope_with_start(&self, start: TapeOffset) -> Option<ScopeHandle> {
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
    fn debug_display(&self, buf: &mut dyn Write, graph: &GraphBuilder, file: &ConvertedFile) {
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
                    ScopeKind::Loop => _ = writeln!(buf, "{}: loop {{", scope.handle.index()),
                    ScopeKind::Block => _ = writeln!(buf, "{}: {{", scope.handle.index()),
                }
                indent += 1;
            }
            ScopeVisit::Statement(index) => {
                let handle = NodeHandle::new(index.index());
                let node = &graph.nodes[handle];
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

struct TapeStructuring {
    statements: HandleVec<NodeHandle, StatementJumps>,
    scopes: ScopeNode,
    counter: HandleCounter<ScopeHandle>,
}

impl TapeStructuring {
    pub fn new(graph: &GraphBuilder) -> TapeStructuring {
        let mut counter = HandleCounter::new();
        let mut scopes = Self {
            statements: graph.nodes.map_fill(StatementJumps::default()),
            scopes: ScopeNode {
                handle: counter.next(),
                kind: ScopeKind::Block,
                start: 0.into(),
                end: graph.nodes.len().into(),
                children: vec![],
            },
            counter,
        };
        scopes.build(graph);
        scopes
    }
    fn add_scope(&mut self, start: TapeOffset, end: TapeOffset, kind: ScopeKind) -> ScopeHandle {
        self.scopes.add_scope(&mut self.counter, start, end, kind)
    }
    fn build(&mut self, graph: &GraphBuilder) -> Vec<Statement> {
        //                                start           0:                       loop {
        //                             ┌─►0──┐              Rule(A) ↓ 2                if !next(A) {
        //                            B│  │A │              Rule(B) 0 ↓                   break;
        //  <separated_list A B>       │  ▼  │            2:                           }
        //                             └──1  │fail          CloseSpan(C) _ _           if !next(B) {
        //                           fail │  │                                           break;
        //                                ▼  │                                         }
        //                           done 2◄─┘                                     }

        fn for_back_edges(
            (current, node): (NodeHandle, &PegNode),
            mut fun: impl FnMut(TapeOffset, TapeOffset),
        ) {
            node.for_edges(|to| {
                if to <= current {
                    fun(current.into(), to.into());
                }
            })
        }

        fn for_forward_jumps(
            (current, node): (NodeHandle, &PegNode),
            mut fun: impl FnMut(TapeOffset, TapeOffset),
        ) {
            let next = TapeOffset::from(current).next();
            node.for_edges(|to| {
                let to = TapeOffset::from(to);
                if to > next {
                    fun(current.into(), to);
                }
            })
        }

        let mut loop_cache = SecondaryVec::with_capacity(graph.nodes.len());
        for node in graph.nodes.iter_kv().rev() {
            for_back_edges(node, |from, to| {
                loop_cache
                    .entry(to)
                    .get_or_insert_with(|| self.add_scope(to, from.next(), ScopeKind::Loop));
            })
        }

        let mut jump_cache = SecondaryVec::with_capacity(graph.nodes.len());
        for node in graph.nodes.iter_kv() {
            for_forward_jumps(node, |from, to| {
                jump_cache
                    .entry(to)
                    .get_or_insert_with(|| self.add_scope(from, to, ScopeKind::Block));
            })
        }

        vec![]
    }
}

#[test]
fn test_graph() {
    let src = include_str!("../../../grammar.gng");
    // let src = "
    //     rule A {}
    //     rule B {}
    //     rule C { <separated_list A B> }
    // ";

    let parsed = ParsedFile::new(src);
    let converted = ConvertedFile::new(src, &parsed);
    let lowered = LoweredFile::new(src, &converted);

    let mut offset = 0;
    for (handle, expr) in lowered.rules.iter_kv() {
        let mut builder = GraphBuilder::new();

        let result = builder.convert_expr(expr, vec![]);
        builder.single_transition(result.success, Transition::CloseSpan(handle));
        builder.single_transition(result.fail, Transition::ReturnFail);

        let mut buf = String::new();

        // let mut structuring = TapeStructuring::new(&builder);
        // structuring.build(&builder);
        // structuring
        //     .scopes
        //     .debug_display(&mut buf, &builder, &converted);

        // let name = converted.rules[handle].name.as_str();
        // _ = writeln!(buf, "rule {}", name);
        // builder.debug_statements(&mut buf, &converted);

        _ = writeln!(buf);
        builder.debug_graphviz(&mut buf, &converted.rules[handle].name, offset, &converted);

        println!("{buf}");
        offset += builder.nodes.len();
    }
}
