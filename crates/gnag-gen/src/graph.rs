use std::{
    borrow::Cow,
    cell::RefCell,
    fmt::{Display, Formatter, Write},
};

use gnag::{
    ast::RuleKind,
    ctx::ErrorAccumulator,
    handle::{Bitset, HandleBitset, HandleCounter, HandleVec, SecondaryVec, TypedHandle},
    simple_handle, StrSpan,
};

use crate::{
    convert::{ConvertedFile, RuleHandle},
    expr::{ReturnResult, RuleExpr, Transition, TransitionEffects, VariableHandle},
};

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
    pub fn for_edges_transition(&self, mut fun: impl FnMut(NodeHandle, Option<&Transition>)) {
        if let Some(success) = self.success {
            fun(success, Some(&self.transition));
        }
        if let Some(fail) = self.fail {
            fun(fail, None);
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

pub struct GraphBuilder<'a> {
    nodes: HandleVec<NodeHandle, PegNode>,
    err: &'a ErrorAccumulator,
    // a sidechannel to give information to convert_expr for pratt conversion
    current_rule: Option<RuleHandle>,
    variables: HandleCounter<VariableHandle>,
}

impl<'a> GraphBuilder<'a> {
    pub fn new(err: &'a ErrorAccumulator) -> GraphBuilder {
        GraphBuilder {
            nodes: HandleVec::new(),
            err,
            current_rule: None,
            variables: HandleCounter::new(),
        }
    }
    pub fn convert_rule(
        &mut self,
        handle: RuleHandle,
        kind: RuleKind,
        expr: &RuleExpr,
        optimize: bool,
    ) -> NodeHandle {
        // good code right here
        self.current_rule = Some(handle);
        let mut result = self.convert_expr(expr, vec![]);
        self.current_rule = None;

        // TODO clean this up
        if let Some(_) = result.entry {
            if kind == RuleKind::Rules {
                if !matches!(expr, RuleExpr::Pratt(_)) {
                    let span =
                        self.single_transition(&result.success, Transition::CloseSpan(handle));
                    result.success = span.success;
                }

                self.single_transition(&result.success, Transition::Return(ReturnResult::RuleOk));
            }
        }

        let ret = match kind {
            RuleKind::Tokens => ReturnResult::TokenFail,
            RuleKind::Rules => ReturnResult::RuleFail,
        };
        let result2 = self.single_transition(&result.fail, Transition::Return(ret));

        let mut entry = result.entry.or(result2.entry).unwrap();

        if optimize {
            entry = self.optimize(entry).unwrap();
        }

        entry
    }
    pub fn finish(&mut self) -> HandleVec<NodeHandle, PegNode> {
        let nodes = self.get_nodes().clone();
        self.clear();
        nodes
    }
    /// Reorder the graph into a topological order which is suitable for lowering to code, Removes reduntand parser state resets.
    /// The new graph only contains nodes reachable from the entry.
    ///
    /// Returns the new handle to the entry.
    pub fn optimize(&mut self, mut entry: NodeHandle) -> Option<NodeHandle> {
        let mut deleted = HandleBitset::new();
        self.merge_state_resets(entry, &mut deleted);
        entry = self.apply_deletes(entry, &deleted)?;
        entry = self.reorder(entry);

        Some(entry)
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
        self.variables.reset();
    }
}

impl<'a> GraphBuilder<'a> {
    fn connect_backward_edges(&mut self, node: NodeHandle, incoming: &[IncomingEdge]) {
        for edge in incoming {
            assert!(edge.from >= node);
            self.nodes[edge.from].add_outgoing_edge(node, edge.is_fail);
        }
    }
    #[allow(dead_code)]
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
    fn new_variable(&mut self) -> VariableHandle {
        self.variables.next()
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
            RuleExpr::Commit => PegResult {
                entry: None,
                success: incoming,
                fail: vec![],
            },
            RuleExpr::Transition(transition) => {
                self.single_transition(&incoming, transition.clone())
            }
            RuleExpr::Sequence(vec) => {
                let mut vec = Cow::Borrowed(vec);
                if vec.len() > 1 {
                    vec.to_mut()
                        .push(RuleExpr::Transition(Transition::Dummy(true)));
                };

                let save_variable = self.new_variable();
                let save = self.single_transition(&incoming, Transition::SaveState(save_variable));

                let mut fail = Vec::new();
                let mut fail_reset = Vec::new();
                let mut success = save.success;

                let mut commit_index = vec.iter().position(|e| matches!(e, RuleExpr::Commit));

                let mut consumed_any = false;

                for (i, rule) in vec.iter().enumerate() {
                    let incoming = std::mem::take(&mut success);
                    let mut result = self.convert_expr(rule, incoming);

                    let can_commit = match rule {
                        RuleExpr::Transition(transition) => match transition {
                            Transition::CompareBindingPower(_) => false,
                            _ => true,
                        },
                        _ => true,
                    };

                    if result.entry.is_some() && can_commit {
                        consumed_any = true;
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

                if !fail_reset.is_empty() {
                    let mut restore = self
                        .single_transition(&fail_reset, Transition::RestoreState(save_variable));
                    fail.append(&mut restore.success);
                }

                PegResult {
                    entry: save.entry,
                    success,
                    fail,
                }
            }
            RuleExpr::Choice(vec) => {
                let mut fail = incoming;
                let mut success = Vec::new();

                let mut vec = Cow::Borrowed(vec);
                // makes more readable code
                // TODO improve this heuristic
                if vec.len() > 2 {
                    vec.to_mut()
                        .push(RuleExpr::Transition(Transition::Dummy(false)));
                }

                let peek = self.peek_next_node();
                for rule in vec.iter() {
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
                    expr.as_ref(),
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
            RuleExpr::Maybe(expr) => {
                let result = self.convert_expr(expr, incoming);
                PegResult {
                    entry: result.entry,
                    success: result.merged_edges(),
                    fail: vec![],
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

                self.connect_backward_edges(element.entry.unwrap(), &separator.success);

                let mut fail = element.fail;
                fail.append(&mut separator.fail);

                PegResult {
                    entry: element.entry,
                    success: fail,
                    fail: vec![],
                }
            }
            RuleExpr::Pratt(_)
            | RuleExpr::OneOrMore(_)
            | RuleExpr::InlineParameter(_)
            | RuleExpr::InlineCall(_)
            | RuleExpr::UnresolvedIdentifier { .. }
            | RuleExpr::UnresolvedLiteral { .. } => {
                unreachable!("These should have been eliminated during lowering")
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
        let effects = transition.effects();
        let node = self.new_node(transition, incoming);
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
    fn visit_edges_dfs_impl(
        nodes: &HandleVec<NodeHandle, PegNode>,
        parent: Option<NodeHandle>,
        child: NodeHandle,
        transition: Option<&Transition>,
        on_stack: &mut HandleBitset<NodeHandle>,
        fun: &mut dyn FnMut(Option<NodeHandle>, NodeHandle, Option<&Transition>, bool) -> bool,
    ) {
        let is_back_edge = on_stack.contains(child);
        let should_enter = fun(parent, child, transition, is_back_edge);

        if should_enter && !is_back_edge {
            on_stack.insert(child);

            nodes[child].for_edges_transition(|node, transition| {
                Self::visit_edges_dfs_impl(nodes, Some(child), node, transition, on_stack, fun);
            });

            on_stack.remove(child);
        }
    }
    pub(crate) fn visit_edges_once_dfs(
        nodes: &HandleVec<NodeHandle, PegNode>,
        entry: NodeHandle,
        //                           parent       child     transition           is_backward_edge
        mut fun: impl FnMut(Option<NodeHandle>, NodeHandle, Option<&Transition>, bool) -> bool,
    ) {
        // TODO allocate these in some bump allocator
        let mut explored = HandleBitset::with_capacity(nodes.len());
        let mut scratch = HandleBitset::with_capacity(nodes.len());

        Self::visit_edges_dfs_impl(
            nodes,
            None,
            entry,
            None,
            &mut scratch,
            &mut |parent, child, transition, is_back_edge| {
                let should_continue = fun(parent, child, transition, is_back_edge);
                let mut already_explored = false;
                if should_continue && !is_back_edge {
                    already_explored = explored.insert(child);
                }
                should_continue && !already_explored
            },
        );
    }
    pub(crate) fn visit_edges_dfs_then_topological(
        nodes: &HandleVec<NodeHandle, PegNode>,
        entry: NodeHandle,

        mut dfs: impl FnMut(Option<NodeHandle>, NodeHandle, Option<&Transition>, bool),
        mut topological: impl FnMut(Option<NodeHandle>, NodeHandle, Option<&Transition>),
    ) {
        // count the number of incoming forward edges
        //  A   B
        //   \ /
        // ┌─►C    C has 2 parents
        // └──┘
        let mut parent_count = nodes.map_fill(0);
        Self::visit_edges_once_dfs(
            nodes,
            entry,
            |parent, child, transition, is_backward_edge| {
                dfs(parent, child, transition, is_backward_edge);
                if !is_backward_edge {
                    parent_count[child] += 1;
                }
                true
            },
        );

        assert_eq!(parent_count[entry], 1);

        Self::visit_edges_once_dfs(
            nodes,
            entry,
            |parent, child, transition, is_backward_edge| {
                if !is_backward_edge {
                    topological(parent, child, transition);

                    let parents = &mut parent_count[child];
                    *parents -= 1;
                    if *parents == 0 {
                        return true;
                    }
                }
                false
            },
        );
    }
    pub(crate) fn visit_nodes_topological(
        nodes: &HandleVec<NodeHandle, PegNode>,
        entry: NodeHandle,

        mut topological: impl FnMut(NodeHandle),
    ) {
        let mut parent_count = nodes.map_fill(0);
        Self::visit_edges_once_dfs(nodes, entry, |_, child, _, is_backward_edge| {
            if !is_backward_edge {
                parent_count[child] += 1;
            }
            true
        });

        assert_eq!(parent_count[entry], 1);

        Self::visit_edges_once_dfs(nodes, entry, |_, child, _, is_backward_edge| {
            if !is_backward_edge {
                let parents = &mut parent_count[child];
                *parents -= 1;
                if *parents == 0 {
                    topological(child);
                    return true;
                }
            }
            false
        });
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
    fn merge_state_resets(&mut self, entry: NodeHandle, deleted: &mut HandleBitset<NodeHandle>) {
        #[derive(Clone, Copy, PartialEq, Eq)]
        struct ParserState {
            state: NodeHandle,
            variable: Option<VariableHandle>,
        }

        impl ParserState {
            fn original(this: NodeHandle) -> ParserState {
                Self {
                    state: this,
                    variable: None,
                }
            }
            fn is_equivalent(&self, other: &ParserState) -> bool {
                self.state == other.state
            }
            fn merge_with(&mut self, this: NodeHandle, other: &ParserState) {
                if self.is_equivalent(other) {
                    if self.variable != other.variable {
                        self.variable = None;
                    }
                } else {
                    *self = Self::original(this);
                }
            }
            fn set_variable(&mut self, variable: VariableHandle) {
                self.variable = Some(variable);
            }
        }

        let mut variables: SecondaryVec<VariableHandle, ParserState> =
            SecondaryVec::with_capacity(self.variables.len());
        let mut states = RefCell::new(SecondaryVec::with_capacity(self.nodes.len()));
        let mut used_variables = HandleBitset::with_capacity(self.variables.len());

        states.get_mut().insert(entry, ParserState::original(entry));

        Self::visit_edges_dfs_then_topological(
            &mut self.nodes,
            entry,
            |_, child, _, is_back_edge| {
                if is_back_edge {
                    // loops are hard to think about so we conservatively mark all loop entrances as original
                    states
                        .borrow_mut()
                        .insert(child, ParserState::original(child));
                }
            },
            |parent, child, transition| {
                let mut states = states.borrow_mut();
                if let Some(parent) = parent {
                    let mut parent_state = states[parent];

                    match transition {
                        Some(&Transition::SaveState(variable)) => {
                            // if the current state is already saved in some variable,
                            // we can reuse it and entirely remove this variable
                            if parent_state.variable.is_some() {
                                deleted.insert(parent);
                            }

                            let actual_variable = parent_state.variable.unwrap_or(variable);
                            parent_state.set_variable(actual_variable);

                            let prev = variables.insert(variable, parent_state);
                            assert!(prev.is_none(), "Variables can be set only once");
                        }
                        Some(&Transition::RestoreState(variable)) => {
                            let saved_state = variables[variable];
                            if saved_state.is_equivalent(&parent_state) {
                                deleted.insert(parent);
                            } else {
                                used_variables.insert(saved_state.variable.unwrap());
                                parent_state = saved_state;
                            }
                        }
                        _ => {
                            let advances_parser =
                                transition.map_or(false, Transition::advances_parser);

                            if advances_parser {
                                parent_state = ParserState::original(child);
                            }
                        }
                    }

                    match states.get_mut(child) {
                        Some(state) => state.merge_with(child, &parent_state),
                        None => _ = states.insert(child, parent_state),
                    }
                }
            },
        );

        for (handle, node) in self.nodes.iter_kv_mut() {
            match &mut node.transition {
                Transition::SaveState(variable) => {
                    if !used_variables.contains(*variable) {
                        deleted.insert(handle);
                    }
                }
                Transition::RestoreState(variable) => {
                    let state = variables[*variable];
                    // the variable's handle and the variable in its actual state may differ if
                    // it was determined that another variable hold the same state
                    *variable = state.variable.unwrap();
                }
                _ => (),
            }
        }
    }
    /// Modify the graph such that all deleted nodes become unreachable.
    /// This works by reattaching all edges going into deleted nodes to go into the success-edge children instead.
    /// Deleting whole cycles creates dangling edges.
    fn apply_deletes(
        &mut self,
        entry: NodeHandle,
        deleted: &HandleBitset<NodeHandle>,
    ) -> Option<NodeHandle> {
        fn find_non_deleted_node(
            handle: NodeHandle,
            deleted: &HandleBitset<NodeHandle>,
            nodes: &HandleVec<NodeHandle, PegNode>,
            memo: &mut SecondaryVec<NodeHandle, Option<NodeHandle>>,
            stack: &mut HandleBitset<NodeHandle>,
        ) -> Option<NodeHandle> {
            if let Some(present) = memo.get(handle) {
                return *present;
            }

            let node = &nodes[handle];
            let is_loop = stack.insert(handle);
            let is_deleted = deleted.contains(handle);

            let result = if is_deleted {
                if !is_loop {
                    node.success.and_then(|success| {
                        find_non_deleted_node(success, deleted, nodes, memo, stack)
                    })
                } else {
                    None
                }
            } else {
                // node is not deleted, we can keep it
                Some(handle)
            };

            // fill the entry for this node
            memo.insert(handle, result);

            if !is_loop {
                stack.remove(handle);
            }

            return result;
        }

        let mut memo = SecondaryVec::with_capacity_for(&self.nodes);
        let mut stack = HandleBitset::with_capacity(self.nodes.len());

        for handle in self.nodes.iter_keys() {
            find_non_deleted_node(handle, deleted, &self.nodes, &mut memo, &mut stack);
        }

        for node in self.nodes.iter_mut() {
            if let Some(child) = node.success {
                node.success = memo[child];
            }
            if let Some(child) = node.fail {
                node.fail = memo[child];
            }
        }

        memo[entry]
    }
    /// Reorder the nodes into a new topological order where success edge children are placed
    /// directly after their parents (Backward edges are preserved), which leads to more natural generated code.
    ///
    /// Also eliminates unreachable nodes.
    ///
    /// Returns the new handle to the entry.
    fn reorder(&mut self, entry: NodeHandle) -> NodeHandle {
        // old_node -> new_node
        let mut renames = SecondaryVec::with_capacity(self.nodes.len());
        // new_node -> old_node
        let mut collect = HandleVec::new();

        Self::visit_nodes_topological(&self.nodes, entry, |node| {
            let new_handle = collect.push(node);
            let previous = renames.insert(node, new_handle);
            assert!(previous.is_none());
        });

        // collect nodes in the new order
        let new_nodes = collect.map(|source| {
            let mut new = self.nodes[source].clone();
            new.for_edges_mut(|child| {
                *child = renames[*child];
            });
            new
        });

        self.nodes = new_nodes;
        return renames[entry];
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
        let capacity: u32 = capacity.try_into().unwrap();
        FlowTargets {
            set: Bitset::with_capacity(capacity * 2),
        }
    }
    pub fn set_is_reachable(&mut self, node: NodeHandle) {
        let index = node.index_u32() * 2;
        self.set.insert(index);
    }
    pub fn set_is_target(&mut self, node: NodeHandle) {
        let index = node.index_u32() * 2 + 1;
        self.set.insert(index);
    }
    pub fn is_reachable(&self, node: NodeHandle) -> bool {
        let index = node.index_u32() * 2;
        self.set.contains(index)
    }
    pub fn is_target(&self, node: NodeHandle) -> bool {
        let index = node.index_u32() * 2 + 1;
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
                Some(&v.transition),
                Some(style),
                index_offset,
                file,
            );
        } else {
            print_dot_edge(
                buf,
                k,
                v.success,
                Some(&v.transition),
                None,
                index_offset,
                file,
            );
            if effects == TransitionEffects::Fallible {
                print_dot_edge(buf, k, v.fail, None, Some("color=red"), index_offset, file);
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
    transition: Option<&Transition>,
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

    write!(buf, "    v{start} -> v{end}{suffix}[label=");
    if let Some(transition) = transition {
        transition.display_as_string(buf, file);
    } else {
        write!(buf, "\"Fail\"");
    }

    if let Some(style) = style {
        write!(buf, ",{style}");
    }
    write!(buf, "]\n");
}
