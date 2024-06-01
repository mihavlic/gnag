use std::fmt::{Display, Formatter, Write};

use gnag::{
    ctx::ErrorAccumulator,
    handle::{Bitset, HandleBitset, HandleVec, SecondaryVec, TypedHandle},
    simple_handle, StrSpan,
};

use crate::{
    convert::{ConvertedFile, RuleExpr, RuleHandle, TokenHandle},
    lower::LoweredFile,
};

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
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
    Return(bool),
    // does nothing
    Dummy,
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
            | Transition::Not(_)
            | Transition::Dummy => TransitionEffects::Fallible,
            Transition::Fail | Transition::RestoreState(_) | Transition::CloseSpan(_) => {
                TransitionEffects::Infallible
            }
            Transition::Return(_) => TransitionEffects::Noreturn,
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
            Transition::Return(value) => write!(f, "Return({value})"),
            Transition::Dummy => write!(f, "Dummy"),
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
    /// return whether failure in this node has the same control flow as success
    fn fail_same_as_success(&self) -> bool {
        return self.fail.is_none() || self.fail == self.success;
    }
    fn free_fail_edge(&mut self) -> bool {
        if self.fail.is_some() {
            self.fail = None;
            return true;
        }
        return false;
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

pub struct GraphBuilder<'a> {
    nodes: HandleVec<NodeHandle, PegNode>,
    err: &'a ErrorAccumulator,
    // a sidechannel to give information to convert_expr for pratt conversion
    current_rule: Option<RuleHandle>,

    // scratch data for rule conversion
    // TODO use a bump allocator and allocate as needed
    scratch1: HandleBitset<NodeHandle>,
    scratch2: HandleBitset<NodeHandle>,
}

impl<'a> GraphBuilder<'a> {
    pub fn new(err: &'a ErrorAccumulator) -> GraphBuilder {
        GraphBuilder {
            nodes: HandleVec::new(),
            err,
            current_rule: None,
            scratch1: Default::default(),
            scratch2: Default::default(),
        }
    }
    pub fn convert_file(
        &mut self,
        optimize: bool,
        lowered: &LoweredFile,
    ) -> HandleVec<RuleHandle, HandleVec<NodeHandle, PegNode>> {
        self.clear();
        lowered.rules.map_ref_with_key(|handle, expr| {
            self.clear();
            let entry = self.convert_rule(handle, expr);
            if let Some(entry) = entry {
                if optimize {
                    self.optimize(entry);
                }
            }
            self.get_nodes().clone()
        })
    }
    pub fn convert_rule(&mut self, handle: RuleHandle, expr: &RuleExpr) -> Option<NodeHandle> {
        // good code right here
        self.current_rule = Some(handle);
        let mut result = self.convert_expr(expr, vec![]);
        self.current_rule = None;

        if let Some(_) = result.entry {
            if !matches!(expr, RuleExpr::Pratt(_)) {
                let success =
                    self.single_transition(&result.success, Transition::CloseSpan(handle));
                result.success = success.success;
            }
            self.single_transition(&result.success, Transition::Return(true));
            self.single_transition(&result.fail, Transition::Return(false));
        }

        result.entry
    }
    /// Reorder the graph into a topological order which is suitable for lowering to code, Removes reduntand parser state resets.
    /// The new graph only contains nodes reachable from the entry.
    pub fn optimize(&mut self, entry: NodeHandle) {
        // reorder does not move the entry
        self.reorder(entry);
        self.merge_state_resets(entry);
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
    pub fn clear(&mut self) {
        self.nodes.clear();
    }
}

impl<'a> GraphBuilder<'a> {
    fn connect_backward_edges(&mut self, node: NodeHandle, incoming: &[IncomingEdge]) {
        for edge in incoming {
            assert!(edge.from >= node);
            self.nodes[edge.from].add_outgoing_edge(node, edge.is_fail);
        }
    }
    fn connect_forward_edges(&mut self, node: NodeHandle, incoming: &[IncomingEdge]) {
        for edge in incoming {
            assert!(edge.from < node);
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
    fn error(&self, /* span: StrSpan, */ error: String) {
        self.err.error(StrSpan::empty(), error);
    }
    fn convert_expr_nonempty(
        &mut self,
        expr: &RuleExpr,
        incoming: Vec<IncomingEdge>,
        error: &str,
    ) -> PegResult {
        let result = self.convert_expr(expr, incoming);
        if result.entry.is_none() {
            self.error(error.to_owned());
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
                    self.error("RuleExpr::Not only works with tokens".to_owned());
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
            RuleExpr::Pratt(vec) => {
                // TODO improve robustness, left recursion recognition is very dumb
                let mut prefix_entry = None;
                let mut prefix_fail = incoming;
                let mut prefix_success = Vec::new();

                let mut otherwise_entry = None;
                let mut otherwise_fail = Vec::new();
                let mut otherwise_success = Vec::new();

                for rule in vec {
                    let mut result = self.convert_expr(&rule.expr, vec![]);

                    let Some(mut first_handle) = result.entry else {
                        continue;
                    };

                    let first_node = &self.nodes[first_handle];

                    let mut is_recursive = false;
                    if let Transition::Rule(rule) = first_node.transition {
                        if Some(rule) == self.current_rule {
                            let Some(next_handle) = first_node.success else {
                                // TODO emit error
                                continue;
                            };
                            let next_node = &mut self.nodes[next_handle];
                            // we are skipping the first rule, if the rule expression was a sequence,
                            // it may have been committed after the first node
                            // so we have to reintroduce a correct fail edge
                            if next_node.fail_same_as_success() {
                                if next_node.free_fail_edge() {
                                    result.fail.push(IncomingEdge {
                                        from: next_handle,
                                        is_fail: true,
                                    });
                                }
                            }
                            first_handle = next_handle;

                            is_recursive = true;
                        }
                    }

                    if is_recursive {
                        result.success = self
                            .single_transition(
                                &result.success,
                                Transition::CloseSpan(self.current_rule.unwrap()),
                            )
                            .success;
                    }

                    let (fail, success, entry) = match is_recursive {
                        false => (&mut prefix_fail, &mut prefix_success, &mut prefix_entry),
                        true => (
                            &mut otherwise_fail,
                            &mut otherwise_success,
                            &mut otherwise_entry,
                        ),
                    };

                    if entry.is_none() {
                        *entry = Some(first_handle);
                    }

                    self.connect_forward_edges(first_handle, fail);
                    *fail = std::mem::take(&mut result.fail);
                    success.append(&mut result.success);
                }

                if prefix_entry.is_none() {
                    prefix_entry = otherwise_entry;
                }

                if let Some(otherwise_entry) = otherwise_entry {
                    let mut dummy = self.single_transition(&otherwise_fail, Transition::Dummy);
                    otherwise_fail = dummy.success;
                    otherwise_success.append(&mut dummy.fail);

                    self.connect_forward_edges(otherwise_entry, &prefix_success);
                    self.connect_backward_edges(otherwise_entry, &otherwise_success);
                    otherwise_success = std::mem::take(&mut otherwise_fail);
                } else {
                    otherwise_success = prefix_success;
                }

                PegResult {
                    entry: prefix_entry,
                    success: otherwise_success,
                    fail: prefix_fail,
                }
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
        nodes: &HandleVec<NodeHandle, PegNode>,
        handle: NodeHandle,
        explored: &mut HandleBitset<NodeHandle>,
        scratch: &mut HandleBitset<NodeHandle>,
        //                           parent       child     is_backward_edge
        mut fun: impl FnMut(Option<NodeHandle>, NodeHandle, bool) -> bool,
    ) {
        fn dyn_impl(
            nodes: &HandleVec<NodeHandle, PegNode>,
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

                nodes[child].for_edges(|node| {
                    dyn_impl(nodes, Some(child), node, explored, on_stack, fun);
                });

                on_stack.remove(child);
            }
        }

        explored.clear();
        scratch.clear();
        dyn_impl(nodes, None, handle, explored, scratch, &mut fun);
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
    fn merge_state_resets(&mut self, entry: NodeHandle) {
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

        let Self {
            nodes,
            scratch1: reachable,
            scratch2: scratch,
            ..
        } = self;

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

        Self::visit_edges_dfs(&self.nodes, entry, reachable, scratch, |_, child, _| {
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
    fn reorder(&mut self, entry: NodeHandle) {
        let reachable = &mut self.scratch1;
        let scratch = &mut self.scratch2;

        // count the number of incoming forward edges
        //  A   B
        //   \ /
        // ┌─►C    C has 2 parents
        // └──┘
        let mut parent_count = self.nodes.map_fill(0);
        Self::visit_edges_dfs(
            &self.nodes,
            entry,
            reachable,
            scratch,
            |_, child, is_backward_edge| {
                if !is_backward_edge {
                    parent_count[child] += 1;
                }
                true
            },
        );

        assert_eq!(parent_count[entry], 1);

        // old_node -> new_node
        let mut renames = SecondaryVec::with_capacity(self.nodes.len());
        // new_node -> old_node
        let mut collect = HandleVec::new();

        // iterate the graph in topological order, storing the visited sequence
        Self::visit_edges_dfs(
            &self.nodes,
            entry,
            reachable,
            scratch,
            |_, child, is_backward_edge| {
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
            },
        );

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

pub fn analyze_flow_targets(nodes: &HandleVec<NodeHandle, PegNode>) -> FlowTargets {
    let mut reachability = FlowTargets::with_capacity(nodes.len());

    if nodes.is_empty() {
        return reachability;
    }

    reachability.set_is_reachable(0.into());

    for (current, node) in nodes.iter_kv() {
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

#[allow(unused_must_use)]
pub fn debug_graphviz(
    nodes: &HandleVec<NodeHandle, PegNode>,
    buf: &mut dyn Write,
    subgraph: &str,
    index_offset: usize,
    file: &crate::convert::ConvertedFile,
) {
    writeln!(buf, "subgraph cluster_{subgraph} {{");
    writeln!(buf, "    label={subgraph:?}");
    for (k, v) in nodes.iter_kv() {
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

pub fn debug_statements(
    nodes: &HandleVec<NodeHandle, PegNode>,
    buf: &mut dyn Write,
    file: &ConvertedFile,
) {
    let reachability = analyze_flow_targets(nodes);

    let mut previous_reachable = None;

    #[allow(unused_must_use)]
    for (current, node) in nodes.iter_kv() {
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
