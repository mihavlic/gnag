use std::fmt::Display;

use cranelift_entity::{entity_impl, EntityRef, EntitySet, PrimaryMap, SecondaryMap};

use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition, TransitionEffects},
    backend::grammar::Grammar,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ScopeHandle(u32);
entity_impl!(ScopeHandle);

impl Display for ScopeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'b{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StatementHandle(u32);
entity_impl!(StatementHandle);

impl StatementHandle {
    pub fn next(self) -> StatementHandle {
        Self(self.0 + 1)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Flow {
    None,
    Continue(ScopeHandle),
    Break(ScopeHandle),
    Unreachable,
}

impl Display for Flow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Flow::Continue(a) => write!(f, "continue {a}"),
            Flow::Break(a) => write!(f, "break {a}"),
            Flow::Unreachable => write!(f, "unreachable!()"),
            Flow::None => Ok(()),
        }
    }
}

impl Flow {
    fn is_some(self) -> bool {
        !matches!(self, Flow::None)
    }
    fn or(self, other: Flow) -> Flow {
        match self {
            Flow::None => other,
            _ => self,
        }
    }
}

pub enum ScopeKind {
    Block,
    Loop,
}

pub struct Scope {
    /// index of the first step in this block
    pub start: StatementHandle,
    /// number of steps in this block and its child blocks
    pub end: StatementHandle,
}

impl Scope {
    pub fn is_empty(&self) -> bool {
        self.start != self.end
    }
}

#[derive(Clone)]
pub struct Step {
    pub transition: Transition,
    pub success: Flow,
    pub fail: Flow,
}

#[derive(Clone)]
pub enum Statement {
    Step(Step),
    Jump(Flow),
}

#[derive(Clone, Copy)]
pub enum TreeEvent {
    Open(ScopeHandle),
    Close(ScopeHandle),
    Statement(StatementHandle),
}

#[derive(Clone, Copy)]
pub enum TreeEventValue<'a> {
    Open(ScopeHandle, &'a Scope),
    Close(ScopeHandle, &'a Scope),
    Statement(StatementHandle, &'a Statement),
}

pub struct StructureBuilder {
    events: Vec<TreeEvent>,
    statements: Vec<Statement>,
    scopes: PrimaryMap<ScopeHandle, Scope>,
}

impl StructureBuilder {
    pub fn new() -> StructureBuilder {
        Self {
            events: Vec::new(),
            statements: Vec::new(),
            scopes: PrimaryMap::new(),
        }
    }
    pub fn scopes_len(&self) -> usize {
        self.scopes.len()
    }
    pub fn statements_len(&self) -> usize {
        self.statements.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = TreeEventValue> {
        self.events.iter().map(|event| match *event {
            TreeEvent::Open(i) => TreeEventValue::Open(i, self.get_scope(i)),
            TreeEvent::Close(i) => TreeEventValue::Close(i, self.get_scope(i)),
            TreeEvent::Statement(i) => TreeEventValue::Statement(i, self.get_statement(i)),
        })
    }
    #[track_caller]
    pub fn get_statement(&self, handle: StatementHandle) -> &Statement {
        &self.statements[handle.index()]
    }
    #[track_caller]
    pub fn get_scope(&self, handle: ScopeHandle) -> &Scope {
        &self.scopes[handle]
    }
    pub fn clear(&mut self) {
        self.events.clear();
        self.statements.clear();
        self.scopes.clear();
    }
    pub fn retain_statements(&mut self, retain: &EntitySet<StatementHandle>) {
        let mut new_keys = std::iter::repeat(StatementHandle::from_u32(0))
            .take(self.statements_len())
            .collect::<PrimaryMap<StatementHandle, StatementHandle>>();

        let mut src = StatementHandle::from_u32(0);
        let mut dst = src;

        self.statements.retain(|_| {
            new_keys[src] = dst;
            let retain = retain.contains(src);
            if retain {
                dst = dst.next();
            }
            src = src.next();
            retain
        });

        let end = StatementHandle::new(self.statements_len());
        let get_new = |handle: StatementHandle| new_keys.get(handle).copied().unwrap_or(end);

        for scope in self.scopes.values_mut() {
            scope.start = get_new(scope.start);
            scope.end = get_new(scope.end);
        }

        self.events.retain_mut(|event| {
            if let TreeEvent::Statement(handle) = event {
                let retained = retain.contains(*handle);
                if retained {
                    *handle = get_new(*handle);
                } else {
                    // remove not-retained statements
                    return false;
                }
            }
            return true;
        });
    }

    fn step(&mut self, step: Step) {
        let handle = StatementHandle::new(self.statements.len());
        self.statements.push(Statement::Step(step));
        self.events.push(TreeEvent::Statement(handle));
    }
    fn open_block(&mut self) -> ScopeHandle {
        let start = StatementHandle::new(self.statements.len());
        let handle = self.scopes.push(Scope { start, end: start });
        self.events.push(TreeEvent::Open(handle));
        handle
    }
    fn close_block(&mut self, handle: ScopeHandle) {
        let end = StatementHandle::new(self.statements.len());
        let block = &mut self.scopes[handle];
        block.end = end;

        self.events.push(TreeEvent::Close(handle));
    }
    fn jump(&mut self, action: Flow) {
        assert!(action.is_some(), "Jumping with Flow::None makes no sense");
        let handle = StatementHandle::new(self.statements.len());
        self.statements.push(Statement::Jump(action));
        self.events.push(TreeEvent::Statement(handle));
    }
}

pub struct PatternProperties {
    commit_after: bool,
}

pub fn lower_pattern(
    pattern: &Pattern,
    success: Flow,
    fail: Flow,

    grammar: &Grammar,
    builder: &mut StructureBuilder,
) -> PatternProperties {
    let children = pattern.children();

    match pattern.kind() {
        PatternKind::Transition(transition) => {
            builder.step(Step {
                transition: transition.clone(),
                success,
                fail,
            });
            PatternProperties {
                commit_after: transition.advances_parser(),
            }
        }
        PatternKind::Group(Group::Sequence { .. }) => {
            let reset_block = builder.open_block();
            builder.step(Step {
                transition: Transition::SaveState,
                success: Flow::None,
                fail: Flow::None,
            });

            let block = builder.open_block();

            let next_success = Flow::None;
            let mut next_fail = Flow::Break(block);

            let commit_index = children
                .iter()
                .position(|child| matches!(child.kind(), PatternKind::Commit));

            let mut commit_after = false;
            let mut commit = false;

            for (index, child) in children.iter().enumerate() {
                let child = lower_pattern(child, next_success, next_fail, grammar, builder);

                commit_after |= child.commit_after;

                if !commit {
                    if let Some(commit_index) = commit_index {
                        if commit_index == index {
                            commit = true;
                        }
                    } else {
                        // automatically commit sequence only if commit_index is none
                        commit |= child.commit_after;
                    }

                    if commit {
                        // committing means that failures are ignored
                        next_fail = Flow::None;
                    }
                }
            }

            // all children of sequence matched, success
            if success.is_some() {
                builder.jump(success);
            }
            builder.close_block(block);

            builder.step(Step {
                transition: Transition::RestoreState,
                success: Flow::None,
                fail: Flow::None,
            });
            if fail.is_some() {
                builder.jump(fail);
            }
            builder.close_block(reset_block);

            PatternProperties { commit_after }
        }
        PatternKind::Group(Group::Choice) => {
            let block = builder.open_block();

            let next_success = success.or(Flow::Break(block));
            let next_fail = Flow::None;

            let mut commit_after = true;

            for child in children {
                let child = lower_pattern(child, next_success, next_fail, grammar, builder);
                commit_after &= child.commit_after;
            }

            // no children of sequence matched, fail
            builder.jump(fail.or(Flow::Break(block)));
            builder.close_block(block);

            PatternProperties { commit_after }
        }
        PatternKind::Group(Group::Loop) => {
            let block = builder.open_block();

            let next_success = Flow::Continue(block);
            let next_fail = success.or(Flow::Break(block));

            for child in children {
                lower_pattern(child, next_success, next_fail, grammar, builder);
            }

            builder.close_block(block);

            PatternProperties {
                commit_after: false,
            }
        }
        PatternKind::Group(Group::Maybe) => {
            let next_success = success;
            let next_fail = success;

            for child in children {
                lower_pattern(child, next_success, next_fail, grammar, builder);
            }

            PatternProperties {
                commit_after: false,
            }
        }
        PatternKind::Commit => {
            // do nothing
            PatternProperties {
                commit_after: false,
            }
        }
        PatternKind::Group(Group::OneOrMore | Group::InlineCall { .. })
        | PatternKind::UnresolvedIdent(_)
        | PatternKind::UnresolvedLiteral(_)
        | PatternKind::InlineParameter(_)
        | PatternKind::Pratt(_) => panic!("Should have been lowered"),
    }
}

pub fn remove_unreachable(structure: &mut StructureBuilder) {
    let mut skipping_scopes: u32 = 0;
    let mut reachable_statements = EntitySet::with_capacity(structure.statements_len());
    // let mut statement_states = SecondaryMap::with_capacity(structure.statements_len());
    // let mut

    reachable_statements.insert(StatementHandle::from_u32(0));

    for event in structure.iter() {
        match event {
            TreeEventValue::Open(_, scope) => {
                let scope_reachable = reachable_statements.contains(scope.start);
                if !scope_reachable || skipping_scopes > 0 {
                    skipping_scopes += 1;
                }
            }
            TreeEventValue::Close(_, scope) => {
                skipping_scopes = skipping_scopes.saturating_sub(1);
                if skipping_scopes == 0 {
                    // start skipping if no control flow points to the next statement
                    let statement_reachable = reachable_statements.contains(scope.end);
                    if !statement_reachable {
                        skipping_scopes = 1;
                        continue;
                    }
                }
            }
            TreeEventValue::Statement(handle, statement) => {
                if skipping_scopes > 0 {
                    continue;
                }

                let mut handle_flow = |flow: Flow| {
                    let next = match flow {
                        Flow::None => handle.next(),
                        Flow::Continue(s) => structure.get_scope(s).start,
                        Flow::Break(s) => structure.get_scope(s).end,
                        Flow::Unreachable => return,
                    };
                    reachable_statements.insert(next);
                };

                match statement {
                    Statement::Step(a) => {
                        let effects = a.transition.effects();
                        if effects == TransitionEffects::Noreturn {
                            skipping_scopes = 1;
                            continue;
                        }
                        if effects.can_succeed() {
                            handle_flow(a.success);
                        }
                        if effects.can_fail() {
                            handle_flow(a.fail);
                        }
                    }
                    Statement::Jump(a) => {
                        handle_flow(*a);
                        // skip the rest of this block if this flow breaks from it
                        if a.is_some() {
                            skipping_scopes = 1;
                        }
                    }
                }
            }
        }
    }

    structure.retain_statements(&reachable_statements);
}

pub fn optimize(_builder: &mut StructureBuilder) {
    // let mut stack = Vec::new();

    // structure.events.retain(|event| match event {
    //     TreeEvent::Open(_) => todo!(),
    //     TreeEvent::Close(_) => todo!(),
    //     TreeEvent::Statement(_) => todo!(),
    //     TreeEvent::Jump(_) => todo!(),
    // });

    // TODO
}
