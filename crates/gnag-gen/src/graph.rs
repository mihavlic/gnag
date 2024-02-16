use std::fmt::{Display, Formatter, Write};

use gnag::{
    handle::{Bitset, HandleBitset, HandleVec, TypedHandle},
    simple_handle,
};

use crate::convert::{ConvertedFile, RuleExpr, RuleHandle, TokenHandle};

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
            Transition::CloseSpan(a) => write!(f, "CloseSpan({})", file.rules[a].name),
            Transition::ReturnFail => write!(f, "ReturnFail"),
        }
    }
}

simple_handle! {
    pub NodeHandle
}

impl NodeHandle {
    pub fn prev(self) -> Option<NodeHandle> {
        self.0.checked_sub(1).map(NodeHandle)
    }
    pub fn next(self) -> NodeHandle {
        NodeHandle(self.0 + 1)
    }
    pub fn bump(&mut self) {
        self.0 += 1;
    }
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

pub struct PegNode {
    pub transition: Transition,
    pub success: Option<NodeHandle>,
    pub fail: Option<NodeHandle>,
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
    pub fn for_edges(&self, mut fun: impl FnMut(NodeHandle)) {
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

#[derive(Default)]
pub struct Graph {
    nodes: HandleVec<NodeHandle, PegNode>,
    // TODO spans
    errors: Vec<String>,
}

impl Graph {
    pub fn new(handle: RuleHandle, expr: &RuleExpr) -> Graph {
        let mut graph = Graph::default();

        let result = graph.convert_expr(expr, vec![]);
        graph.single_transition(result.success, Transition::CloseSpan(handle));
        graph.single_transition(result.fail, Transition::ReturnFail);

        graph
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
    pub fn get_node(&self, node: NodeHandle) -> Option<&PegNode> {
        self.nodes.get(node)
    }
    pub fn get_nodes(&self) -> &HandleVec<NodeHandle, PegNode> {
        &self.nodes
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
        let reachability = self.analyze_reachability();

        let mut previous_reachable = None;

        #[allow(unused_must_use)]
        for (current, node) in self.nodes.iter_kv() {
            {
                let is_target = reachability.is_target(current);
                let is_reachable = reachability.is_reachable(current);

                let previous_is_reachable = previous_reachable.unwrap_or(true);
                let is_dead = !is_reachable && (previous_is_reachable || is_target);

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

                previous_reachable = Some(is_reachable);
            }

            {
                write!(buf, "  ");
                node.transition.display(buf, file);

                let next = current.next();
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
            }
            write!(buf, "\n");
        }
    }
    pub fn analyze_reachability(&self) -> Reachability {
        let mut need_label = Reachability::with_capacity(self.nodes.len());

        if self.nodes.is_empty() {
            return need_label;
        }

        need_label.set_is_reachable(0.into());

        for (current, node) in self.nodes.iter_kv() {
            let next = current.next();
            node.for_edges(|jump| {
                if next != jump {
                    need_label.set_is_target(jump);
                }
                if need_label.is_reachable(current) {
                    need_label.set_is_reachable(jump);
                }
            });
        }
        need_label
    }
    pub fn analyze_state_changes(&self) -> Reachability {
        todo!()
    }
}

pub struct Reachability {
    set: Bitset,
}

impl Reachability {
    pub fn new() -> Reachability {
        Reachability { set: Bitset::new() }
    }
    pub fn with_capacity(capacity: usize) -> Reachability {
        Reachability {
            set: Bitset::with_capacity(capacity * 2),
        }
    }
    pub fn set_is_reachable(&mut self, node: NodeHandle) {
        let index = node.index() * 2;
        self.set.insert(index);
    }
    pub fn set_is_target(&mut self, node: NodeHandle) {
        let index = node.index() * 2 + 1;
        self.set.insert(index);
    }
    pub fn is_reachable(&self, node: NodeHandle) -> bool {
        let index = node.index() * 2;
        self.set.contains(index)
    }
    pub fn is_target(&self, node: NodeHandle) -> bool {
        let index = node.index() * 2 + 1;
        self.set.contains(index)
    }
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

impl Graph {
    pub fn convert_expr(&mut self, expr: &RuleExpr, incoming: Vec<IncomingEdge>) -> PegEdges {
        match expr {
            RuleExpr::Empty | RuleExpr::Commit => PegEdges {
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

                let commit = vec
                    .iter()
                    .position(|e| matches!(e, RuleExpr::Commit))
                    .unwrap_or(0);

                for (i, rule) in vec.iter().enumerate() {
                    let incoming = std::mem::take(&mut success);
                    let mut result = self.convert_expr(rule, incoming);

                    let fail_dest = match i > commit {
                        true => &mut success,
                        false => &mut fail,
                    };

                    fail_dest.append(&mut result.fail);
                    success.append(&mut result.success);
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
