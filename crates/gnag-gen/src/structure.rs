use crate::convert::ConvertedFile;
use crate::graph::NodeHandle;
use crate::graph::PegNode;
use crate::graph::Transition;
use crate::graph::TransitionEffects;
use crate::scope_tree::ScopeHandle;
use crate::scope_tree::ScopeKind;
use crate::scope_tree::ScopeNode;
use crate::scope_tree::ScopeVisit;
use gnag::handle::HandleBitset;
use gnag::handle::HandleCounter;
use gnag::handle::HandleVec;
use std::cmp::Ordering;
use std::fmt::Write;

#[derive(Clone, Default)]
struct StatementJumps {
    jump_forward: Option<ScopeHandle>,
    back_edge: Option<ScopeHandle>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct BlockCondition {
    pub(crate) condition: NodeHandle,
    pub(crate) negate: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BlockStatement {
    pub(crate) kind: ScopeKind,
    pub(crate) condition: Option<BlockCondition>,
}

impl From<ScopeKind> for BlockStatement {
    fn from(kind: ScopeKind) -> Self {
        BlockStatement {
            kind,
            condition: None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FlowAction {
    Break(ScopeHandle),
    Continue(ScopeHandle),
    Panic,
    None,
}

#[derive(Clone)]
pub enum Statement {
    Open(ScopeHandle, BlockStatement),
    Close(ScopeHandle),
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
        let mut statements = Vec::new();

        let mut last_statement = None;
        let mut last_scope = None;
        let mut first_loop = None;
        let mut last_loop = None;

        self.tree.visit_dfs(|event| match event {
            ScopeVisit::Open(scope) => {
                statements.push(Statement::Open(scope.handle, scope.kind.into()));
            }
            ScopeVisit::Statement(handle) => {
                let node = &nodes[handle];
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
            if let Statement::Open(scope_handle, block) = &mut statements[open_index] {
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
    stack: &mut Vec<(ScopeHandle, &'a BlockStatement)>,
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
                        nodes[condition.condition].transition.display(buf, file);

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
                mut fail,
            } => {
                print_indent(buf, indent);
                let transition = nodes[condition].transition;
                let effects = transition.effects();

                fn print_action(
                    buf: &mut dyn Write,
                    action: FlowAction,
                    prefix: &str,
                    suffix: &str,
                    stack: &[(ScopeHandle, &BlockStatement)],
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
