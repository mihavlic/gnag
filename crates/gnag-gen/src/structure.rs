use crate::convert::ConvertedFile;
use crate::expr::Transition;
use crate::expr::TransitionEffects;
use crate::graph::NodeHandle;
use crate::graph::PegNode;
use crate::scope_tree::ScopeKind;
use crate::scope_tree::ScopeNode;
use crate::scope_tree::ScopeNodeHandle;
use crate::scope_tree::ScopeVisit;
use gnag::handle::HandleBitset;
use gnag::handle::HandleCounter;
use gnag::handle::HandleVec;
use std::cmp::Ordering;
use std::fmt::Write;

#[derive(Clone, Default)]
struct StatementJumps {
    jump_forward: Option<ScopeNodeHandle>,
    back_edge: Option<ScopeNodeHandle>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct BlockCondition {
    pub(crate) condition: NodeHandle,
    pub(crate) negate: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BlockStatement {
    pub(crate) handle: ScopeNodeHandle,
    pub(crate) kind: ScopeKind,
    pub(crate) condition: Option<BlockCondition>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FlowAction {
    Break(ScopeNodeHandle),
    Continue(ScopeNodeHandle),
    Panic,
    None,
}

impl FlowAction {
    pub fn flow_target_scope_if_needed<'a>(
        self,
        current_scope: &BlockStatement,
    ) -> Option<ScopeNodeHandle> {
        if let FlowAction::Break(handle) | FlowAction::Continue(handle) = self {
            // you cannot break out of a normal block without it having a label
            if current_scope.kind == ScopeKind::Block || current_scope.handle != handle {
                return Some(handle);
            }
        }
        None
    }
}

#[derive(Clone)]
pub enum Statement {
    Open(BlockStatement),
    Close,
    Statement {
        condition: NodeHandle,
        success: FlowAction,
        fail: FlowAction,
    },
}

pub struct GraphStructuring {
    tree: ScopeNode,
    jump_table: HandleVec<NodeHandle, StatementJumps>,
}

impl GraphStructuring {
    pub fn new(nodes: &HandleVec<NodeHandle, PegNode>) -> GraphStructuring {
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
        let mut tree = ScopeNode::new(counter.next(), 0.into(), nodes.len().into());
        let mut jump_table = nodes.map_fill(StatementJumps::default());

        for node in nodes.iter_kv().rev() {
            for_back_edges(node, |from, to| {
                jump_table[to].back_edge.get_or_insert_with(|| {
                    tree.add_scope(&mut counter, to, from.next(), ScopeKind::Loop)
                });
            });
        }

        for node in nodes.iter_kv() {
            for_forward_jumps(node, |from, to| {
                jump_table[to].jump_forward.get_or_insert_with(|| {
                    tree.add_scope(&mut counter, from, to, ScopeKind::Block)
                });
            });
        }

        #[cfg(debug_assertions)]
        tree.validate(true);

        Self { tree, jump_table }
    }
    pub(crate) fn translate_jump(&self, jump: Option<NodeHandle>, next: NodeHandle) -> FlowAction {
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
    pub fn emit_code(
        &self,
        create_while: bool,
        create_if: bool,
        nodes: &HandleVec<NodeHandle, PegNode>,
    ) -> Vec<Statement> {
        struct StatementFixup {
            previous_statement: Option<usize>,
            outermost_scope: Option<ScopeNodeHandle>,
            innermost_loop: Option<ScopeNodeHandle>,
            outermost_loop: Option<ScopeNodeHandle>,
        }

        impl StatementFixup {
            fn new() -> StatementFixup {
                Self {
                    previous_statement: None,
                    outermost_scope: None,
                    innermost_loop: None,
                    outermost_loop: None,
                }
            }
            fn fixup_previous_statement(&mut self, statements: &mut [Statement]) {
                if let Some(previous) = self.previous_statement {
                    if let Some(innermost_loop) = self.innermost_loop {
                        let Statement::Statement {
                            condition: _,
                            success,
                            fail,
                        } = &mut statements[previous]
                        else {
                            unreachable!()
                        };

                        let Some(outermost_scope) = self.outermost_scope else {
                            unreachable!()
                        };

                        // before fixup, FlowAction::None is considered to mean "the next statement"
                        // we insert breaks if needed to preserve this behaviour
                        if let FlowAction::None = success {
                            *success = FlowAction::Break(outermost_scope);
                        }
                        if let FlowAction::None = fail {
                            *fail = FlowAction::Break(outermost_scope);
                        }
                        // if we're continuing in the last statement of the loop, we don't need to explicitly continue
                        if let FlowAction::Continue(scope) = success {
                            if *scope == innermost_loop {
                                *success = FlowAction::None;
                            }
                        }
                        if let FlowAction::Continue(scope) = fail {
                            if *scope == innermost_loop {
                                *fail = FlowAction::None;
                            }
                        }
                    }
                }
                self.previous_statement = None;
            }
            fn set_next_statement(&mut self, next_statement_index: usize) {
                self.previous_statement = Some(next_statement_index);
                self.outermost_scope = None;
                self.innermost_loop = None;
                self.outermost_loop = None;
            }
            fn on_close(&mut self, scope: &ScopeNode) {
                self.outermost_scope = Some(scope.handle);
                if scope.kind == ScopeKind::Loop {
                    self.innermost_loop.get_or_insert(scope.handle);
                    self.outermost_loop = Some(scope.handle);
                }
            }
        }

        let mut statements = Vec::new();

        let mut fixup = StatementFixup::new();

        self.tree.visit_dfs(|event| match event {
            ScopeVisit::Open(scope) => {
                statements.push(Statement::Open(BlockStatement {
                    handle: scope.handle,
                    kind: scope.kind,
                    condition: None,
                }));
            }
            ScopeVisit::Statement(handle) => {
                fixup.fixup_previous_statement(&mut statements);
                fixup.set_next_statement(statements.len());

                let node = &nodes[handle];
                let next = handle.next();

                statements.push(Statement::Statement {
                    condition: handle,
                    success: self.translate_jump(node.success, next),
                    fail: self.translate_jump(node.fail, next),
                });
            }
            ScopeVisit::Close(scope) => {
                fixup.on_close(scope);
                statements.push(Statement::Close);
            }
        });

        // finish off any remaining statement
        fixup.fixup_previous_statement(&mut statements);

        if !create_while && !create_if {
            return statements;
        }

        // we need to do this in a second pass because some ::Continue may be turned into ::None
        // after we've passed over them in the main loop
        let mut i = 0;
        while i < statements.len() {
            let open_index = i;
            i += 1;

            let next = statements.get(i).cloned();
            if let Statement::Open(block) = &mut statements[open_index] {
                if block.condition.is_some() {
                    continue;
                }

                match block.kind {
                    ScopeKind::Loop if !create_while => continue,
                    ScopeKind::Block if !create_if => continue,
                    _ => {}
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
                    (FlowAction::Break(scope), FlowAction::None) if scope == block.handle => {
                        Some(true)
                    }
                    (FlowAction::None, FlowAction::Break(scope)) if scope == block.handle => {
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
    pub fn debug_scopes(
        &self,
        buf: &mut dyn Write,
        nodes: &HandleVec<NodeHandle, PegNode>,
        file: &ConvertedFile,
    ) {
        self.tree.debug_display(buf, nodes, file);
    }
}

pub(crate) fn mark_used_labels<'a>(
    statements: &'a [Statement],
    stack: &mut Vec<&'a BlockStatement>,
) -> HandleBitset<ScopeNodeHandle> {
    let mut bitset = HandleBitset::new();
    for statement in statements {
        match statement {
            Statement::Open(block) => {
                stack.push(block);
            }
            Statement::Close => _ = stack.pop(),
            &Statement::Statement { success, fail, .. } => {
                let current_scope = *stack.last().unwrap();
                if let Some(handle) = success.flow_target_scope_if_needed(current_scope) {
                    bitset.insert(handle);
                }
                if let Some(handle) = fail.flow_target_scope_if_needed(current_scope) {
                    bitset.insert(handle);
                }
            }
        }
    }

    bitset
}

#[allow(unused_must_use)]
pub fn display_code(
    buf: &mut dyn Write,
    statements: &[Statement],
    nodes: &HandleVec<NodeHandle, PegNode>,
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
            Statement::Open(block) => {
                print_indent(buf, indent);

                let print_label = used_labels.contains(block.handle);
                if print_label && !(block.kind == ScopeKind::Block && block.condition.is_some()) {
                    write!(buf, "'b{}: ", block.handle);
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
                        nodes[condition.condition].transition.display(buf, file);

                        write!(buf, " {{");
                        if print_label && kind == ScopeKind::Block {
                            write!(buf, " 'b{}: {{", block.handle);
                        }
                    }
                }

                if let Some(Statement::Close) = statements.get(i) {
                    writeln!(buf, " }}");
                    i += 1;
                } else {
                    indent += 1;
                    stack.push(block);
                    writeln!(buf);
                }
            }
            &Statement::Statement {
                condition,
                success,
                mut fail,
            } => {
                print_indent(buf, indent);
                let transition = &nodes[condition].transition;
                let effects = transition.effects();

                fn print_action(
                    buf: &mut dyn Write,
                    action: FlowAction,
                    prefix: &str,
                    suffix: &str,
                    stack: &[&BlockStatement],
                ) {
                    write!(buf, "{prefix}");
                    match action {
                        FlowAction::Break(_) => _ = write!(buf, "break"),
                        FlowAction::Continue(_) => _ = write!(buf, "continue"),
                        FlowAction::Panic => _ = write!(buf, "panic!()"),
                        FlowAction::None => {}
                    }
                    if let FlowAction::Break(scope) | FlowAction::Continue(scope) = action {
                        let block = *stack.last().unwrap();
                        let force_label = block.kind == ScopeKind::Block;
                        if block.handle != scope || force_label {
                            write!(buf, " 'b{scope}");
                        }
                    }
                    writeln!(buf, "{suffix}");
                }

                if let Transition::Dummy(should_succeed) = transition {
                    writeln!(buf, "// dummy");
                    let action = match should_succeed {
                        true => success,
                        false => fail,
                    };
                    if action != FlowAction::None {
                        print_indent(buf, indent);
                        print_action(buf, action, "", ";", &stack);
                    }
                    continue;
                }

                if effects == TransitionEffects::Noreturn {
                    transition.display(buf, file);
                    writeln!(buf, ";");
                    continue;
                }

                if effects == TransitionEffects::Infallible {
                    // we set the fail branch to the same action to achieve the needed formatting
                    assert!(fail == FlowAction::Panic);
                    fail = success;
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
                    (success, fail) if success == fail => {
                        transition.display(buf, file);
                        writeln!(buf, ";");

                        print_indent(buf, indent);
                        print_action(buf, success, "", ";", &stack);
                    }
                    (success, fail) => {
                        write!(buf, "match ");
                        transition.display(buf, file);
                        writeln!(buf, " {{");

                        print_indent(buf, indent + 1);
                        print_action(buf, success, "true => ", ",", &stack);
                        print_indent(buf, indent + 1);
                        print_action(buf, fail, "false => ", ",", &stack);

                        print_indent(buf, indent);
                        writeln!(buf, "}}");
                    }
                }
            }
            Statement::Close => {
                indent -= 1;
                print_indent(buf, indent);

                let block = stack.pop().unwrap();
                if used_labels.contains(block.handle)
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
