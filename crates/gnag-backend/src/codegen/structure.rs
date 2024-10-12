use std::fmt::Display;

use code_render::{render, render_into, Fragments, RenderCx};
use cranelift_entity::{entity_impl, EntitySet, PrimaryMap};

use crate::{
    ast::{
        display::{ByteExt, ByteSliceExt},
        pattern::{
            AnyPattern, ComparisonKind, ConsumeUntil, Group, NotPattern, Pattern, PatternKind,
            Transition, TransitionEffects,
        },
    },
    backend::grammar::Grammar,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ScopeHandle(u32);
entity_impl!(ScopeHandle);

impl Display for ScopeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'b{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StatementHandle(u32);
entity_impl!(StatementHandle);

#[derive(Clone, Copy, PartialEq, Eq)]
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
    pub len: u32,
}

pub struct Step {
    pub transition: Transition,
    pub success: Flow,
    pub fail: Flow,
}

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
    statements: PrimaryMap<StatementHandle, Statement>,
    blocks: PrimaryMap<ScopeHandle, Scope>,
}

impl StructureBuilder {
    pub fn new() -> StructureBuilder {
        Self {
            events: Vec::new(),
            statements: PrimaryMap::new(),
            blocks: PrimaryMap::new(),
        }
    }
    pub fn scopes_len(&self) -> usize {
        self.blocks.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = TreeEventValue> {
        self.events.iter().map(|event| match *event {
            TreeEvent::Open(i) => TreeEventValue::Open(i, &self.blocks[i]),
            TreeEvent::Close(i) => TreeEventValue::Close(i, &self.blocks[i]),
            TreeEvent::Statement(i) => TreeEventValue::Statement(i, &self.statements[i]),
        })
    }
    pub fn clear(&mut self) {
        self.events.clear();
        self.statements.clear();
        self.blocks.clear();
    }

    fn step(&mut self, step: Step) -> StatementHandle {
        let handle = self.statements.push(Statement::Step(step));
        self.events.push(TreeEvent::Statement(handle));
        handle
    }
    fn open_block(&mut self) -> ScopeHandle {
        let start = self.statements.next_key();
        let handle = self.blocks.push(Scope { start, len: 0 });
        self.events.push(TreeEvent::Open(handle));
        handle
    }
    fn close_block(&mut self, handle: ScopeHandle) {
        let end = self.statements.next_key();
        let block = &mut self.blocks[handle];
        block.len = end.as_u32() - block.start.as_u32();

        self.events.push(TreeEvent::Close(handle));
    }
    fn jump(&mut self, action: Flow) -> StatementHandle {
        assert!(action.is_some());
        self.statements.push(Statement::Jump(action))
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
            let block = builder.open_block();

            let next_success = Flow::None;
            let mut next_fail = fail;

            let commit_index = children
                .iter()
                .position(|child| matches!(child.kind(), PatternKind::Commit));

            let mut commit_after = false;
            let mut commit = false;

            for (index, child) in pattern.children().iter().enumerate() {
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
            builder.jump(success.or(Flow::Break(block)));
            builder.close_block(block);

            PatternProperties { commit_after }
        }
        PatternKind::Group(Group::Choice) => {
            let block = builder.open_block();

            let next_success = success.or(Flow::Break(block));
            let next_fail = Flow::None;

            let mut commit_after = true;

            for child in pattern.children() {
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

            let next_success = Flow::None;
            let next_fail = success.or(Flow::Break(block));

            for child in pattern.children() {
                lower_pattern(child, next_success, next_fail, grammar, builder);
            }

            builder.jump(fail.or(Flow::Continue(block)));
            builder.close_block(block);

            PatternProperties {
                commit_after: false,
            }
        }
        PatternKind::Group(Group::Maybe) => {
            let next_success = Flow::None;
            let next_fail = Flow::None;

            for child in pattern.children() {
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

pub fn optimize(structure: &mut StructureBuilder) {
    // let mut stack = Vec::new();

    // structure.events.retain(|event| match event {
    //     TreeEvent::Open(_) => todo!(),
    //     TreeEvent::Close(_) => todo!(),
    //     TreeEvent::Statement(_) => todo!(),
    //     TreeEvent::Jump(_) => todo!(),
    // });

    // TODO
}
