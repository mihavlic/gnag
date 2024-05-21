use std::fmt::{Display, Formatter, Write};

use gnag::{
    handle::{Bitset, HandleBitset, HandleVec, SecondaryVec, TypedHandle},
    simple_handle,
};

use crate::convert::{ConvertedFile, RuleExpr, RuleHandle, TokenHandle};

#[derive(Clone, Debug, Copy)]
pub enum Transition {
    Error,
    Fail,
    Token(TokenHandle),
    Rule(RuleHandle),
    PrattRule(RuleHandle, u32),
    // builtins
    Any,
    Not(TokenHandle),
    // function start/end
    RestoreState(NodeHandle),
    CloseSpan(RuleHandle),
    ReturnFail,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TransitionEffects {
    Fallible,
    Infallible,
    Noreturn,
}

impl Transition {
    pub fn effects(self) -> TransitionEffects {
        match self {
            Transition::Error
            | Transition::Token(_)
            | Transition::Rule(_)
            | Transition::PrattRule(_, _)
            | Transition::Any
            | Transition::Not(_) => TransitionEffects::Fallible,
            Transition::Fail | Transition::RestoreState(_) => TransitionEffects::Infallible,
            Transition::ReturnFail | Transition::CloseSpan(_) => TransitionEffects::Noreturn,
        }
    }
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
            Transition::PrattRule(a, bp) => write!(f, "Pratt({}, {bp})", file.rules[a].name),
            Transition::Any => write!(f, "Any"),
            Transition::Not(a) => write!(f, "Not({})", file.tokens[a].name),
            Transition::RestoreState(a) => write!(f, "RestoreState({})", a.index()),
            Transition::CloseSpan(a) => write!(f, "CloseSpan({})", file.rules[a].name),
            Transition::ReturnFail => write!(f, "ReturnFail"),
        }
    }
}

simple_handle! {
    pub NodeHandle
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodePeekHandle(NodeHandle);

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

#[derive(Clone)]
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
    fn add_outgoing_edge(&mut self, to: NodeHandle, is_fail: bool) {
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
    pub fn for_edges_mut(&mut self, mut fun: impl FnMut(&mut NodeHandle)) {
        if let Some(success) = &mut self.success {
            fun(success);
        }
        if let Some(fail) = &mut self.fail {
            fun(fail);
        }
    }
}

#[derive(Clone, Copy)]
pub struct IncomingEdge {
    pub from: NodeHandle,
    pub is_fail: bool,
}

pub struct PegResult {
    pub entry: Option<NodeHandle>,
    pub success: Vec<IncomingEdge>,
    pub fail: Vec<IncomingEdge>,
}

impl PegResult {
    pub fn merged_edges(self) -> Vec<IncomingEdge> {
        let mut vec = Vec::with_capacity(self.success.len() + self.fail.len());
        vec.extend_from_slice(&self.fail);
        vec.extend_from_slice(&self.success);
        vec
    }
    pub fn can_fail(&self) -> bool {
        !self.fail.is_empty()
    }
    pub fn can_succeed(&self) -> bool {
        !self.success.is_empty()
    }
}

pub struct Graph {
    nodes: HandleVec<NodeHandle, PegNode>,
    // TODO spans
    errors: Vec<String>,
    entry: Option<NodeHandle>,
}

impl Graph {
    pub fn new(handle: RuleHandle, expr: &RuleExpr) -> Graph {
        let mut graph = Graph {
            nodes: HandleVec::new(),
            errors: Vec::new(),
            entry: None,
        };

        let result = graph.convert_expr(expr, vec![]);

        if let Some(entry) = result.entry {
            graph.entry = Some(entry);
            let _success = graph.single_transition(&result.success, Transition::CloseSpan(handle));
            let _fail = graph.single_transition(&result.fail, Transition::ReturnFail);
        }

        let mut reachable = HandleBitset::new();
        let mut bitset2 = HandleBitset::new();
        // reorder does not move the entry
        graph.reorder(&mut reachable, &mut bitset2);
        graph.merge_state_resets(&mut reachable, &mut bitset2);

        graph
    }
    fn connect_backward_edges(&mut self, node: NodeHandle, incoming: &[IncomingEdge]) {
        for edge in incoming {
            assert!(edge.from >= node);
            self.nodes[edge.from].add_outgoing_edge(node, edge.is_fail);
        }
    }
    fn new_node(&mut self, transition: Transition, incoming: &[IncomingEdge]) -> NodeHandle {
        let node = self.nodes.push(PegNode::new(transition));
        for edge in incoming {
            assert!(edge.from < node);
            self.nodes[edge.from].add_outgoing_edge(node, edge.is_fail);
        }
        node
    }
    fn peek_next_node(&self) -> NodePeekHandle {
        NodePeekHandle(self.nodes.next_handle())
    }
    fn verify_peek(&mut self, peek: NodePeekHandle) -> Option<NodeHandle> {
        let next = peek.0;
        self.get_node(next).is_some().then_some(next)
    }
    pub fn get_node(&self, node: NodeHandle) -> Option<&PegNode> {
        self.nodes.get(node)
    }
    pub fn get_nodes(&self) -> &HandleVec<NodeHandle, PegNode> {
        &self.nodes
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    fn convert_expr_nonempty(
        &mut self,
        expr: &RuleExpr,
        incoming: Vec<IncomingEdge>,
        error: &str,
    ) -> PegResult {
        let result = self.convert_expr(expr, incoming);
        if result.entry.is_none() {
            self.errors.push(error.to_owned());
            return self.error_transition(&result.merged_edges());
        };
        result
    }
    fn convert_expr(&mut self, expr: &RuleExpr, incoming: Vec<IncomingEdge>) -> PegResult {
        match expr {
            RuleExpr::Empty | RuleExpr::Commit => PegResult {
                entry: None,
                success: incoming,
                fail: vec![],
            },
            // some error that has already been reported, pass it along in a dummy state transition
            RuleExpr::Error => self.error_transition(&incoming),
            RuleExpr::Token(token) => self.single_transition(&incoming, Transition::Token(*token)),
            RuleExpr::Rule(rule) => self.single_transition(&incoming, Transition::Rule(*rule)),
            RuleExpr::Sequence(vec) => {
                let mut fail = Vec::new();
                let mut fail_reset = Vec::new();
                let mut success = incoming;

                let mut commit_index = vec.iter().position(|e| matches!(e, RuleExpr::Commit));
                let mut entry = None;

                let peek = self.peek_next_node();
                for (i, rule) in vec.iter().enumerate() {
                    let incoming = std::mem::take(&mut success);
                    let mut result = self.convert_expr(rule, incoming);

                    let consumed_any = entry.is_some();
                    if let Some(first) = result.entry {
                        entry.get_or_insert(first);
                    }

                    let is_comitted = commit_index.map(|index| i > index).unwrap_or(false);

                    // if no commit point was specified, commit as soon as the sequence can fail
                    //
                    // for example
                    // ( A? B C )
                    //       ^
                    // we commit after B, if we committed after the first member by default
                    // we could commit without consuming anything
                    if commit_index.is_none() && result.can_fail() {
                        commit_index = Some(i);
                    }

                    if is_comitted {
                        success.append(&mut result.fail);
                    } else {
                        if consumed_any {
                            fail_reset.append(&mut result.fail);
                        } else {
                            fail.append(&mut result.fail);
                        }
                    }
                    success.append(&mut result.success);
                }

                if let Some(entry) = entry {
                    if !fail_reset.is_empty() {
                        let mut restore =
                            self.single_transition(&fail_reset, Transition::RestoreState(entry));
                        fail.append(&mut restore.success);
                    }
                }

                PegResult {
                    entry: self.verify_peek(peek),
                    success,
                    fail,
                }
            }
            RuleExpr::Choice(vec) => {
                let mut fail = incoming;
                let mut success = Vec::new();

                let peek = self.peek_next_node();
                for rule in vec {
                    let incoming = std::mem::take(&mut fail);
                    let mut result = self.convert_expr(rule, incoming);

                    fail = result.fail;
                    success.append(&mut result.success);
                }

                PegResult {
                    entry: self.verify_peek(peek),
                    success,
                    fail,
                }
            }
            RuleExpr::Loop(expr) => {
                // Loop('a')
                //
                //    ┌─►* root
                // 'a'└──┤
                //       │ fail
                //       ▼
                //       * done

                let result = self.convert_expr_nonempty(
                    expr,
                    incoming,
                    "Looped expressions cannot be empty",
                );

                // connect the looping edges to the start
                self.connect_backward_edges(result.entry.unwrap(), &result.success);

                PegResult {
                    entry: result.entry,
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
                PegResult {
                    entry: result.entry,
                    success: result.merged_edges(),
                    fail: vec![],
                }
            }
            RuleExpr::Any => self.single_transition(&incoming, Transition::Any),
            RuleExpr::Not(expr) => {
                if let RuleExpr::Token(token) = **expr {
                    self.single_transition(&incoming, Transition::Not(token))
                } else {
                    self.errors
                        .push("RuleExpr::Not only works with tokens".to_owned());
                    self.error_transition(&incoming)
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                // SeparatedList('a', ',')
                //
                //      start
                //   ┌─►*──┐
                //  ,│  │a │
                //   │  ▼  │
                //   └──*  │fail
                // fail │  │
                //      ▼  │
                // done *◄─┘

                let element = self.convert_expr_nonempty(
                    element,
                    incoming,
                    "Element expression cannot be empty",
                );

                let mut separator = self.convert_expr_nonempty(
                    separator,
                    element.success,
                    "Separator expression cannot be empty",
                );

                let mut fail = element.fail;
                fail.append(&mut separator.fail);

                PegResult {
                    entry: element.entry,
                    success: fail,
                    fail: vec![],
                }
            }
            RuleExpr::InlineParameter(_) | RuleExpr::InlineCall(_) => {
                unreachable!("These should have been eliminated during lowering")
            }
            RuleExpr::Pratt(rules) => {
                // TODO eliminate clone?
                let choice = RuleExpr::Choice(rules.iter().map(|r| r.expr.clone()).collect());
                self.convert_expr(&choice, incoming)
            }
        }
    }
    fn error_transition(&mut self, incoming: &[IncomingEdge]) -> PegResult {
        self.single_transition(incoming, Transition::Error)
    }
    fn single_transition(
        &mut self,
        incoming: &[IncomingEdge],
        transition: Transition,
    ) -> PegResult {
        let node = self.new_node(transition, incoming);
        let effects = transition.effects();
        PegResult {
            entry: Some(node),
            success: match effects {
                TransitionEffects::Fallible | TransitionEffects::Infallible => vec![IncomingEdge {
                    from: node,
                    is_fail: false,
                }],
                TransitionEffects::Noreturn => vec![],
            },
            fail: match effects {
                TransitionEffects::Fallible => vec![IncomingEdge {
                    from: node,
                    is_fail: true,
                }],
                TransitionEffects::Infallible | TransitionEffects::Noreturn => vec![],
            },
        }
    }
    fn visit_edges_dfs(
        &self,
        handle: NodeHandle,
        explored: &mut HandleBitset<NodeHandle>,
        scratch: &mut HandleBitset<NodeHandle>,
        //                           parent       child     is_backward_edge
        mut fun: impl FnMut(Option<NodeHandle>, NodeHandle, bool) -> bool,
    ) {
        fn dyn_impl(
            graph: &Graph,
            parent: Option<NodeHandle>,
            child: NodeHandle,
            explored: &mut HandleBitset<NodeHandle>,
            on_stack: &mut HandleBitset<NodeHandle>,
            fun: &mut dyn FnMut(Option<NodeHandle>, NodeHandle, bool) -> bool,
        ) {
            let is_explored = explored.contains(child);
            let is_back_edge = on_stack.contains(child);
            let should_enter = fun(parent, child, is_back_edge);

            if should_enter && !is_back_edge && !is_explored {
                explored.insert(child);
                on_stack.insert(child);

                graph.get_node(child).unwrap().for_edges(|node| {
                    dyn_impl(graph, Some(child), node, explored, on_stack, fun);
                });

                on_stack.remove(child);
            }
        }

        explored.clear();
        scratch.clear();
        dyn_impl(self, None, handle, explored, scratch, &mut fun);
    }
    /// Maps the state of the parser through the graph and transitively propagates state resets
    /// to the earliest checkpoint.
    ///
    /// The target pattern is what results from `( A A <commit> | B B <commit> )`
    /// when `B B` fails, it resets to the checkpoint of when it tried to match - after `A A` failed.
    /// But `A A` also resets state after its failure, the states at the start of `A A` and
    /// `B B` are equal, so we can use only one checkpoint.
    ///
    /// ```ignore
    ///  // left edges omitted
    ///  // reset(node) means reset parser to the state at the beginning of node
    ///
    ///          │
    ///    ... ──A
    ///          │ match token
    ///    ... ──B
    ///          │ fail
    ///          C
    ///          │ reset(A)
    ///    ... ──D
    ///          │ match token
    ///    ... ──E
    ///          │ fail
    ///          F
    ///          │ reset(D)
    ///
    /// // turned into
    ///
    ///          │
    ///    ... ──A
    ///          │ match token
    ///    ... ──B
    ///          │ fail
    ///          C
    ///          │ reset(A)
    ///    ... ──D
    ///          │ match token
    ///    ... ──E
    ///          │ fail
    ///          F
    ///          │ reset(A) // <<<<<<<<<<<<<<<<<<
    /// ```
    fn merge_state_resets(
        &mut self,
        reachable: &mut HandleBitset<NodeHandle>,
        scratch: &mut HandleBitset<NodeHandle>,
    ) {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum InitialState {
            None,
            Original(NodeHandle),
            Sameas(NodeHandle),
        }

        impl InitialState {
            fn same_as(&mut self, this: NodeHandle, same_as: NodeHandle) {
                if *self == InitialState::None || *self == InitialState::Sameas(same_as) {
                    *self = InitialState::Sameas(same_as);
                } else {
                    self.original(this);
                }
            }
            fn original(&mut self, this: NodeHandle) {
                *self = InitialState::Original(this);
            }
        }

        let Some(entry) = self.entry else {
            return;
        };

        let nodes = self.get_nodes();
        let mut states = nodes.map_fill(InitialState::None);

        states[entry].original(entry);

        for (handle, node) in nodes.iter_kv() {
            if !reachable.contains(handle) {
                continue;
            }

            if let Some(child) = node.success {
                if let Transition::RestoreState(state) = node.transition {
                    states[child].same_as(child, state);
                } else {
                    states[child].original(child);
                }
            }
            if let Some(child) = node.fail {
                states[child].same_as(child, handle);
            }
        }

        self.visit_edges_dfs(entry, reachable, scratch, |_, child, _| {
            if let InitialState::Sameas(node) = states[child] {
                states[child] = states[node];
            }
            true
        });

        for node in &mut self.nodes {
            if let Transition::RestoreState(to) = node.transition {
                let InitialState::Original(state) = states[to] else {
                    unreachable!(
                        "Original nodes should have been propagated to all reachable nodes"
                    );
                };
                node.transition = Transition::RestoreState(state);
            }
        }
    }
    /// Reorder the nodes into a new topological order where success edge children are placed
    /// directly after their parents (Backward edges are preserved), which leads to more natural generated code.
    ///
    /// Also eliminates unreachable nodes.
    fn reorder(
        &mut self,
        reachable: &mut HandleBitset<NodeHandle>,
        scratch: &mut HandleBitset<NodeHandle>,
    ) {
        let Some(entry) = self.entry else {
            return;
        };

        // count the number of incoming forward edges
        //  A   B
        //   \ /
        // ┌─►C    C has 2 parents
        // └──┘
        let mut parent_count = self.nodes.map_fill(0);
        self.visit_edges_dfs(entry, reachable, scratch, |_, child, is_backward_edge| {
            if !is_backward_edge {
                parent_count[child] += 1;
            }
            true
        });

        assert_eq!(parent_count[entry], 1);

        // old_node -> new_node
        let mut renames = SecondaryVec::new();
        // new_node -> old_node
        let mut collect = HandleVec::new();

        // iterate the graph in topological order, storing the visited sequence
        self.visit_edges_dfs(entry, reachable, scratch, |_, child, is_backward_edge| {
            if !is_backward_edge {
                let parents = &mut parent_count[child];
                *parents -= 1;

                if *parents == 0 {
                    let new_handle = collect.push(child);
                    let prev = renames.insert(child, new_handle);
                    assert!(prev.is_none());

                    return true;
                }
            }
            false
        });

        // collect nodes in the new order
        let new_nodes = collect.map(|source| {
            let mut new = self.get_node(source).unwrap().clone();
            new.for_edges_mut(|child| {
                *child = renames[*child];
            });
            new
        });

        self.nodes = new_nodes;
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

            let effects = v.transition.effects();

            if v.success == v.fail {
                let style = match effects {
                    TransitionEffects::Noreturn => "color=orange",
                    _ => "color=purple",
                };
                print_dot_edge(
                    buf,
                    k,
                    v.success,
                    v.transition,
                    Some(style),
                    index_offset,
                    file,
                );
            } else {
                print_dot_edge(buf, k, v.success, v.transition, None, index_offset, file);
                if effects == TransitionEffects::Fallible {
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
        }
        writeln!(buf, "}}");
    }
    pub fn debug_statements(&self, buf: &mut dyn Write, file: &ConvertedFile) {
        let reachability = self.analyze_flow_targets();

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
    pub fn analyze_flow_targets(&self) -> FlowTargets {
        let mut reachability = FlowTargets::with_capacity(self.nodes.len());

        if self.nodes.is_empty() {
            return reachability;
        }

        reachability.set_is_reachable(0.into());

        for (current, node) in self.nodes.iter_kv() {
            let next = current.next();
            node.for_edges(|jump| {
                if next != jump {
                    reachability.set_is_target(jump);
                }
                if reachability.is_reachable(current) {
                    reachability.set_is_reachable(jump);
                }
            });
        }
        reachability
    }
}

pub struct FlowTargets {
    set: Bitset,
}

impl FlowTargets {
    pub fn new() -> FlowTargets {
        FlowTargets { set: Bitset::new() }
    }
    pub fn with_capacity(capacity: usize) -> FlowTargets {
        FlowTargets {
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
