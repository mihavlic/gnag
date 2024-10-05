use cranelift_entity::{entity_impl, PrimaryMap};
use gnag_runtime::NodeKind;

use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition},
    backend::grammar::{Grammar, RuleHandle},
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ScopeHandle(u32);

entity_impl!(ScopeHandle);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StepHandle(u32);

entity_impl!(StepHandle);

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Flow {
    Continue(ScopeHandle),
    Break(ScopeHandle),
    Unreachable,
}

pub enum ScopeKind {
    Block,
    Loop,
}

pub struct Scope {
    /// index of the first step in this block
    start: StepHandle,
    /// number of steps in this block and its child blocks
    len: u32,
}

pub struct Step {
    transition: Transition,
    success: Option<Flow>,
    fail: Option<Flow>,
}

pub enum Statement {
    Step(Step),
    Jump(Flow),
}

pub enum TreeEvent {
    Open(ScopeHandle),
    Close(ScopeHandle),
    Statement(StepHandle),
}

pub struct StructureBuilder {
    events: Vec<TreeEvent>,
    statements: PrimaryMap<StepHandle, Statement>,
    blocks: PrimaryMap<ScopeHandle, Scope>,
}

impl StructureBuilder {
    pub fn step(&mut self, step: Step) -> StepHandle {
        let handle = self.statements.push(Statement::Step(step));
        self.events.push(TreeEvent::Statement(handle));
        handle
    }
    pub fn open_block(&mut self) -> ScopeHandle {
        let start = self.statements.next_key();
        let handle = self.blocks.push(Scope { start, len: 0 });
        self.events.push(TreeEvent::Open(handle));
        handle
    }
    pub fn close_block(&mut self, handle: ScopeHandle) {
        let end = self.statements.next_key();
        let block = &mut self.blocks[handle];
        block.len = end.as_u32() - block.start.as_u32();

        self.events.push(TreeEvent::Close(handle));
    }
    pub fn jump(&mut self, action: Flow) -> StepHandle {
        self.statements.push(Statement::Jump(action))
    }
}

// enum Action {
//     LexerReturn(RuleHandle),
//     Return(bool),
//     None
// }

// struct ResultAction {
//     action: Action,
//     flow: Option<Flow>
// }

pub struct PatternProperties {
    commit_after: bool,
}

fn lower_pattern(
    pattern: &Pattern,
    success: Option<Flow>,
    fail: Option<Flow>,

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
        PatternKind::Group(group) => {
            let block = builder.open_block();

            let is_choice = matches!(group, Group::Choice);

            let (next_success, mut next_fail) = match group {
                Group::Choice => (Some(Flow::Break(block)), None),
                Group::Sequence { .. } => (None, fail),
                Group::Loop => (Some(Flow::Continue(block)), Some(Flow::Break(block))),
                Group::Maybe => (Some(Flow::Break(block)), Some(Flow::Break(block))),
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!("Should have been lowered")
                }
            };

            let commit_index = children
                .iter()
                .position(|child| matches!(child.kind(), PatternKind::Commit));

            let mut commit_after = false;
            let mut commit = false;

            for (index, child) in pattern.children().iter().enumerate() {
                let child = lower_pattern(child, next_success, next_fail, grammar, builder);

                commit_after |= child.commit_after;

                // TODO resets for backtracking

                // handle sequence committing behaviour
                if !is_choice && !commit {
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
                        next_fail = None;
                    }
                }
            }

            // if control flow reaches the end of this block
            // a choice has exhausted all options and fails,
            // a sequence has matched all its subpatterns and succeeds
            let action = match is_choice {
                true => fail,
                false => success,
            };
            builder.jump(action);

            builder.close_block(block);

            PatternProperties { commit_after }
        }
        PatternKind::Commit => {
            // do nothing
            PatternProperties {
                commit_after: false,
            }
        }
        PatternKind::UnresolvedIdent(_)
        | PatternKind::UnresolvedLiteral(_)
        | PatternKind::InlineParameter(_)
        | PatternKind::Pratt(_) => unreachable!("Should have been lowered"),
    }
}

pub fn optimize(structure: &mut StructureBuilder) {
    let mut stack = Vec::new();

    structure.events.retain(|event| match event {
        TreeEvent::Open(_) => todo!(),
        TreeEvent::Close(_) => todo!(),
        TreeEvent::Statement(_) => todo!(),
        TreeEvent::Jump(_) => todo!(),
    });
}

// fn transition(transition: &Transition, rcx: &RenderCx, grammar: &Grammar) -> Fragment {
//     match *transition {
//         Transition::Error => render!(rcx, panic!("Error")),
//         Transition::Rule(handle) => {
//             let rule = grammar.get_rule(handle).unwrap();
//             let name = &rule.name;

//             if rule.kind.is_lexer() {
//                 render!(rcx, l.token(nodeKind::#name))
//             } else {
//                 render!(rcx, #name (p))
//             }
//         }
//         Transition::Not(ref a) => match *a {
//             NotPattern::Byte(a) => render!(rcx, l.not_byte(#{a.display()})),
//             NotPattern::Unicode(a) => render!(rcx, l.not_utf8(#a)),
//             NotPattern::ByteSet(ref a) => render!(rcx, l.not_byte_set(#a)),
//             NotPattern::CharacterClass { class: _, unicode } => match unicode {
//                 true => render!(rcx, l.not_utf8_class(CharacterClass::TODO)),
//                 false => render!(rcx, l.not_ascii_class(CharacterClass::TODO)),
//             },
//             NotPattern::Token(a) => render!(rcx, p.not(NodeKind::#{a.name(grammar)})),
//         },
//         Transition::Any(ref a) => match a {
//             AnyPattern::Byte => render!(rcx, p.any_byte()),
//             AnyPattern::Unicode => render!(rcx, p.any_utf8()),
//             AnyPattern::Token => render!(rcx, p.any()),
//         },
//         Transition::ByteSet(ref a) => render!(rcx, l.byte_set(#a)),
//         Transition::Bytes(ref a) => render!(rcx, l.bytes(#{a.display()})),
//         Transition::CharacterClass { class: _, unicode } => match unicode {
//             true => render!(rcx, l.utf8_class(CharacterClass::TODO)),
//             false => render!(rcx, l.ascii_class(CharacterClass::TODO)),
//         },
//         Transition::StringLike { delimiter } => render!(rcx, l.string_like(#{delimiter.display()})),
//         Transition::ConsumeUntil {
//             ref until,
//             inclusive,
//         } => match until {
//             ConsumeUntil::Byte(a) => render!(rcx,
//                 l.consume_until_byte(#{a.display()}, #inclusive)
//             ),
//             ConsumeUntil::Sequence(a) => render!(rcx,
//                 l.consume_until_sequence(#{a.display()}, #inclusive)
//             ),
//         },
//         Transition::Keyword(ref a) => render!(rcx, l.keyword(#{a.display()})),
//         Transition::PrattRule(handle, precedence) => {
//             let name = handle.name(grammar);
//             render!(rcx, #name (p, #precedence) )
//         }
//         Transition::CompareBindingPower(comparison, max_precedence) => match comparison {
//             ComparisonKind::Lower => render!(rcx, precedence < #max_precedence),
//             ComparisonKind::LowerEqual => render!(rcx, precedence <= #max_precedence),
//         },
//         Transition::SaveState => render!(rcx, let checkpoint = p.save_state()),
//         Transition::RestoreState => render!(rcx, p.restore_state(checkpoint)),
//         Transition::CloseSpan(a) => render!(rcx, p.close_span(NodeKind::#{a.name(grammar)})),
//         Transition::Return(a) => render!(rcx, return #a),
//         Transition::LexerReturn(a) => match a {
//             Some(a) => render!(rcx, return Some(NodeKind::#{a.name(grammar)})),
//             None => render!(rcx, return None),
//         },
//     }
// }
