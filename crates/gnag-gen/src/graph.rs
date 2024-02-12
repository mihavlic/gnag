use std::{
    cmp::Ordering,
    fmt::{Display, Formatter, Write},
};

use gnag::{
    ast::ParsedFile,
    handle::{HandleBitset, HandleCounter, HandleVec, SecondaryVec, TypedHandle},
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

impl Display for NodeHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.index().fmt(f)
    }
}

impl From<usize> for NodeHandle {
    fn from(value: usize) -> Self {
        NodeHandle(value.try_into().unwrap())
    }
}

impl NodeHandle {
    fn prev(self) -> Option<NodeHandle> {
        self.0.checked_sub(1).map(NodeHandle)
    }
    fn next(self) -> NodeHandle {
        NodeHandle(self.0 + 1)
    }
    fn bump(&mut self) {
        self.0 += 1;
    }
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

#[derive(Clone, Copy)]
pub struct IncomingEdge {
    pub from: NodeHandle,
    pub is_fail: bool,
}

pub struct PegEdges {
    pub success: Vec<IncomingEdge>,
    pub fail: Vec<IncomingEdge>,
}

impl PegEdges {
    pub fn merged_edges(&self) -> Vec<IncomingEdge> {
        let mut vec = Vec::with_capacity(self.success.len() + self.fail.len());
        vec.extend_from_slice(&self.fail);
        vec.extend_from_slice(&self.success);
        vec
    }
}

pub struct GraphBuilder {
    nodes: HandleVec<NodeHandle, PegNode>,
    // TODO spans
    errors: Vec<String>,
}

impl GraphBuilder {
    pub fn new() -> GraphBuilder {
        GraphBuilder {
            nodes: HandleVec::new(),
            errors: Vec::new(),
        }
    }
    pub fn connect_edges(
        &mut self,
        node: NodeHandle,
        incoming: impl IntoIterator<Item = IncomingEdge>,
    ) {
        for edge in incoming {
            self.nodes[edge.from].connect_edge(edge.is_fail, node);
        }
    }
    pub fn new_node(
        &mut self,
        transition: Transition,
        incoming: impl IntoIterator<Item = IncomingEdge>,
    ) -> NodeHandle {
        let handle = self.nodes.push(PegNode::new(transition));
        self.connect_edges(handle, incoming);
        handle
    }
    pub fn peek_next_node(&self) -> NodeHandle {
        self.nodes.next_handle()
    }
    pub fn get_node(&self, node: NodeHandle) -> Option<&PegNode> {
        self.nodes.get(node)
    }
    #[allow(unused_must_use)]
    pub fn debug_graphviz(
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
    pub fn debug_statements(&self, buf: &mut dyn Write, file: &ConvertedFile) {
        let need_label = self.analyze_control_flow();

        #[allow(unused_must_use)]
        for (current, node) in self.nodes.iter_kv() {
            let prev = current.prev();
            let next = current.next();

            {
                let label = need_label[current];
                let is_target = label.is_target;
                let previous_is_reachable =
                    prev.map(|n| need_label[n].is_reachable).unwrap_or(true);
                let is_dead = !label.is_reachable && (previous_is_reachable || is_target);

                if is_target {
                    write!(buf, "{current}");
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
                        write!(buf, " {jump}");
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
    pub fn analyze_control_flow(&self) -> HandleVec<NodeHandle, StatementLabel> {
        let mut need_label = self.nodes.map_fill(StatementLabel::default());
        if let Some(first) = need_label.first_mut() {
            first.is_reachable = true;
        }

        for (current, node) in self.nodes.iter_kv() {
            let next = current.next();
            node.for_edges(|jump| {
                if next != jump {
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
pub struct StatementLabel {
    pub is_target: bool,
    pub is_reachable: bool,
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

simple_handle! {
    ScopeHandle
}

impl Display for ScopeHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FlowAction {
    Break(ScopeHandle),
    Continue(ScopeHandle),
    Panic,
    None,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct BlockCondition {
    condition: NodeHandle,
    negate: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct StatementBlock {
    kind: ScopeKind,
    condition: Option<BlockCondition>,
}

impl From<ScopeKind> for StatementBlock {
    fn from(kind: ScopeKind) -> Self {
        StatementBlock {
            kind,
            condition: None,
        }
    }
}

#[derive(Clone)]
pub enum Statement {
    Open(ScopeHandle, StatementBlock),
    Close(ScopeHandle),
    Statement {
        condition: NodeHandle,
        success: FlowAction,
        fail: FlowAction,
    },
}

enum ScopeVisit<'a> {
    Open(&'a ScopeNode),
    Statement(NodeHandle),
    Close(&'a ScopeNode),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ScopeKind {
    Loop,
    Block,
}

#[derive(Debug)]
struct ScopeNode {
    handle: ScopeHandle,
    kind: ScopeKind,
    start: NodeHandle,
    end: NodeHandle,
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
    fn contains_range(&self, start: NodeHandle, end: NodeHandle) -> bool {
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
    fn find_child_range(
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
    fn add_scope(
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
    fn validate(&self, root: bool) {
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
    fn find_scope_with_end(&self, end: NodeHandle) -> Option<ScopeHandle> {
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
    fn find_scope_with_start(&self, start: NodeHandle) -> Option<ScopeHandle> {
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
            ScopeVisit::Statement(handle) => {
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

#[derive(Clone, Default)]
struct StatementJumps {
    jump_forward: Option<ScopeHandle>,
    back_edge: Option<ScopeHandle>,
}

struct GraphStructure {
    scope: ScopeNode,
    jump_table: HandleVec<NodeHandle, StatementJumps>,
}

impl GraphStructure {
    pub fn new() -> GraphStructure {
        Self {
            scope: ScopeNode {
                handle: ScopeHandle::new(0),
                kind: ScopeKind::Block,
                start: 0.into(),
                end: 0.into(),
                children: vec![],
            },
            jump_table: HandleVec::new(),
        }
    }
    fn reset(&mut self, handle: ScopeHandle, graph: &GraphBuilder) {
        self.scope.handle = handle;
        self.scope.kind = ScopeKind::Block;
        self.scope.start = 0.into();
        self.scope.end = graph.nodes.len().into();
        self.scope.children.clear();

        self.jump_table.clear();
        self.jump_table
            .resize(graph.nodes.len(), StatementJumps::default());
    }
    fn build(&mut self, graph: &GraphBuilder) {
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
            mut fun: impl FnMut(NodeHandle, NodeHandle),
        ) {
            node.for_edges(|to| {
                if to <= current {
                    fun(current, to);
                }
            })
        }

        fn for_forward_jumps(
            (current, node): (NodeHandle, &PegNode),
            mut fun: impl FnMut(NodeHandle, NodeHandle),
        ) {
            let next = current.next();
            node.for_edges(|to| {
                if to > next {
                    fun(current, to);
                }
            })
        }

        let mut counter = HandleCounter::new();
        self.reset(counter.next(), graph);

        for node in graph.nodes.iter_kv().rev() {
            for_back_edges(node, |from, to| {
                self.jump_table[to].back_edge.get_or_insert_with(|| {
                    self.scope
                        .add_scope(&mut counter, to, from.next(), ScopeKind::Loop)
                });
            })
        }

        for node in graph.nodes.iter_kv() {
            for_forward_jumps(node, |from, to| {
                self.jump_table[to].jump_forward.get_or_insert_with(|| {
                    self.scope
                        .add_scope(&mut counter, from, to, ScopeKind::Block)
                });
            })
        }

        #[cfg(debug_assertions)]
        self.scope.validate(true);
    }
    fn translate_jump(&self, jump: Option<NodeHandle>, next: NodeHandle) -> FlowAction {
        if let Some(to) = jump {
            let entry = &self.jump_table[to];
            match to.cmp(&next) {
                Ordering::Less => FlowAction::Continue(entry.back_edge.unwrap()),
                Ordering::Equal => FlowAction::None,
                Ordering::Greater => FlowAction::Break(entry.jump_forward.unwrap()),
            }
        } else {
            FlowAction::Panic
        }
    }
    pub fn emit_code(&mut self, conditional_blocks: bool, graph: &GraphBuilder) -> Vec<Statement> {
        self.build(graph);
        let reachable_statements = graph.analyze_control_flow();

        let mut statements = Vec::new();

        let mut last_statement = None;
        let mut last_scope = None;
        let mut first_loop = None;
        let mut last_loop = None;

        self.scope.visit_dfs(|event| match event {
            ScopeVisit::Open(scope) => {
                statements.push(Statement::Open(scope.handle, scope.kind.into()));
            }
            ScopeVisit::Statement(handle) => {
                if !reachable_statements[handle].is_reachable {
                    return;
                }

                let node = graph.get_node(handle).unwrap();
                let next = handle.next();

                if let Some(last) = last_statement {
                    if let Some(first_loop) = first_loop {
                        let Statement::Statement {
                            condition: _,
                            success,
                            fail,
                        } = &mut statements[last]
                        else {
                            unreachable!()
                        };

                        if let FlowAction::None = success {
                            *success = FlowAction::Break(last_loop.unwrap());
                        }
                        if let FlowAction::None = fail {
                            *fail = FlowAction::Break(last_loop.unwrap());
                        }
                        if let FlowAction::Continue(scope) = success {
                            if *scope == first_loop {
                                *success = FlowAction::None;
                            }
                        }
                        if let FlowAction::Continue(scope) = fail {
                            if *scope == first_loop {
                                *fail = FlowAction::None;
                            }
                        }
                    }
                }

                last_statement = Some(statements.len());
                first_loop = None;
                last_loop = None;
                last_scope = None;

                statements.push(Statement::Statement {
                    condition: handle,
                    success: self.translate_jump(node.success, next),
                    fail: self.translate_jump(node.fail, next),
                });
            }
            ScopeVisit::Close(scope) => {
                statements.push(Statement::Close(scope.handle));

                last_scope = Some(scope.handle);
                if scope.kind == ScopeKind::Loop {
                    first_loop.get_or_insert(scope.handle);
                    last_loop = Some(scope.handle);
                }
            }
        });

        if !conditional_blocks {
            return statements;
        }

        // we need to do this in a second pass because some ::Continue may be turned into ::None
        // after we've passed over them in the main loop
        let mut i = 0;
        while i < statements.len() {
            let open_index = i;
            i += 1;

            let next = statements.get(i).cloned();
            if let Statement::Open(scope_handle, block) = &mut statements[open_index] {
                if block.condition.is_some() {
                    continue;
                }

                let Some(Statement::Statement {
                    condition,
                    success,
                    fail,
                }) = next
                else {
                    continue;
                };

                let eligible = match (success, fail) {
                    (FlowAction::Break(scope), FlowAction::None) if scope == *scope_handle => {
                        Some(true)
                    }
                    (FlowAction::None, FlowAction::Break(scope)) if scope == *scope_handle => {
                        Some(false)
                    }
                    _ => None,
                };

                if let Some(negate) = eligible {
                    block.condition = Some(BlockCondition { condition, negate });
                    statements.remove(i);
                }
            }
        }

        statements
    }
}

fn mark_used_labels<'a>(
    statements: &'a [Statement],
    stack: &mut Vec<(ScopeHandle, &'a StatementBlock)>,
) -> HandleBitset<ScopeHandle> {
    let mut bitset = HandleBitset::new();
    for statement in statements {
        match statement {
            Statement::Open(handle, block) => {
                stack.push((*handle, block));
            }
            Statement::Close(_) => _ = stack.pop(),
            &Statement::Statement { success, fail, .. } => {
                let &(current_scope, block) = stack.last().unwrap();
                let force_label = block.kind == ScopeKind::Block;
                if let FlowAction::Break(handle) | FlowAction::Continue(handle) = success {
                    if current_scope != handle || force_label {
                        bitset.insert(handle);
                    }
                }
                if let FlowAction::Break(handle) | FlowAction::Continue(handle) = fail {
                    if current_scope != handle || force_label {
                        bitset.insert(handle);
                    }
                }
            }
        }
    }

    bitset
}

#[allow(unused_must_use)]
fn display_code(
    buf: &mut dyn Write,
    statements: &[Statement],
    graph: &GraphBuilder,
    file: &ConvertedFile,
) {
    fn print_indent(buf: &mut dyn Write, indent: i32) {
        for _ in 0..indent {
            write!(buf, "    ");
        }
    }

    let mut stack = Vec::new();
    let used_labels = mark_used_labels(statements, &mut stack);

    let mut indent = 0;
    let mut i = 0;
    while i < statements.len() {
        let current = i;
        i += 1;
        match &statements[current] {
            Statement::Open(handle, block) => {
                print_indent(buf, indent);

                let print_label = used_labels.contains(*handle);
                if print_label && !(block.kind == ScopeKind::Block && block.condition.is_some()) {
                    write!(buf, "'b{handle}: ");
                }

                match (block.kind, block.condition) {
                    (ScopeKind::Loop, None) => _ = write!(buf, "loop {{"),
                    (ScopeKind::Block, None) => _ = write!(buf, "{{"),
                    (kind, Some(condition)) => {
                        match kind {
                            ScopeKind::Loop => _ = write!(buf, "while "),
                            ScopeKind::Block => _ = write!(buf, "if "),
                        }
                        if condition.negate {
                            write!(buf, "!");
                        }
                        graph
                            .get_node(condition.condition)
                            .unwrap()
                            .transition
                            .display(buf, file);

                        write!(buf, " {{");
                        if print_label && kind == ScopeKind::Block {
                            write!(buf, " 'b{handle}: {{");
                        }
                    }
                }

                if let Some(Statement::Close(_)) = statements.get(i) {
                    writeln!(buf, " }}");
                    i += 1;
                } else {
                    indent += 1;
                    stack.push((*handle, block));
                    writeln!(buf);
                }
            }
            &Statement::Statement {
                condition,
                success,
                fail,
            } => {
                print_indent(buf, indent);
                let transition = graph.get_node(condition).unwrap().transition;

                fn print_action(
                    buf: &mut dyn Write,
                    action: FlowAction,
                    prefix: &str,
                    suffix: &str,
                    stack: &[(ScopeHandle, &StatementBlock)],
                ) {
                    write!(buf, "{prefix}");
                    match action {
                        FlowAction::Break(_) => _ = write!(buf, "break"),
                        FlowAction::Continue(_) => _ = write!(buf, "continue"),
                        FlowAction::Panic => _ = write!(buf, "panic!()"),
                        FlowAction::None => {}
                    }
                    if let FlowAction::Break(scope) | FlowAction::Continue(scope) = action {
                        let (current_scope, block) = *stack.last().unwrap();
                        let force_label = block.kind == ScopeKind::Block;
                        if current_scope != scope || force_label {
                            write!(buf, " 'b{scope}");
                        }
                    }
                    writeln!(buf, "{suffix}");
                }

                if let Transition::CloseSpan(_) | Transition::ReturnFail = transition {
                    transition.display(buf, file);
                    writeln!(buf, ";");
                    continue;
                }

                match (success, fail) {
                    (FlowAction::None, FlowAction::None) => {
                        transition.display(buf, file);
                        writeln!(buf, ";");
                    }
                    (FlowAction::None, other) | (other, FlowAction::None) => {
                        write!(buf, "if ");
                        if success == FlowAction::None {
                            write!(buf, "!");
                        }
                        transition.display(buf, file);
                        writeln!(buf, " {{");

                        print_indent(buf, indent);
                        print_action(buf, other, "    ", ";", &stack);

                        print_indent(buf, indent);
                        writeln!(buf, "}}");
                    }
                    (success, fail) => {
                        write!(buf, "match ");
                        transition.display(buf, file);
                        writeln!(buf, " {{");

                        print_indent(buf, indent);
                        print_action(buf, success, "    true => ", ",", &stack);
                        print_indent(buf, indent);
                        print_action(buf, fail, "    false => ", ",", &stack);

                        print_indent(buf, indent);
                        writeln!(buf, "}}");
                    }
                }
            }
            Statement::Close(_) => {
                indent -= 1;
                print_indent(buf, indent);

                let (scope, block) = stack.pop().unwrap();
                if used_labels.contains(scope)
                    && block.kind == ScopeKind::Block
                    && block.condition.is_some()
                {
                    write!(buf, "}}");
                }
                writeln!(buf, "}}");
            }
        }
    }
}

#[test]
fn test_graph() {
    let src = include_str!("../../../grammar.gng");
    // let src = "
    //     rule A {}
    //     rule B {}
    //     rule C { A* (B | C) }
    // ";

    let parsed = ParsedFile::new(src);
    let converted = ConvertedFile::new(src, &parsed);
    let lowered = LoweredFile::new(src, &converted);

    let mut offset = 0;
    for (handle, expr) in lowered.rules.iter_kv() {
        let mut graph = GraphBuilder::new();

        let result = graph.convert_expr(expr, vec![]);
        graph.single_transition(result.success, Transition::CloseSpan(handle));
        graph.single_transition(result.fail, Transition::ReturnFail);

        let mut buf = String::new();
        let _name = converted.rules[handle].name.as_str();

        let mut structure = GraphStructure::new();

        {
            // structure.scope.debug_display(&mut buf, &graph, &converted);
        }

        {
            _ = write!(buf, "rule {_name} ");
            let statements = structure.emit_code(true, &graph);
            display_code(&mut buf, &statements, &graph, &converted);

            // _ = write!(buf, "\n");
            // structure.scope.debug_display(&mut buf, &graph, &converted);

            // _ = writeln!(buf, "\n{:#?}", structure.scope);
        }

        {
            // _ = writeln!(buf, "\nrule {_name}");
            // graph.debug_statements(&mut buf, &converted);
        }

        {
            // _ = writeln!(buf);
            // builder.debug_graphviz(&mut buf, _name, offset, &converted);
        }

        println!("{buf}");
        offset += graph.nodes.len();
    }
}
