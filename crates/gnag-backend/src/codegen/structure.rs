use cranelift_entity::{entity_impl, PrimaryMap};

use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition},
    backend::grammar::Grammar,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ScopeHandle(u32);

entity_impl!(ScopeHandle);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StepHandle(u32);

entity_impl!(StepHandle);

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FlowAction {
    Continue(ScopeHandle),
    Break(ScopeHandle),
    Unreachable,
    None,
}

pub enum BlockKind {
    Block,
    Loop,
}

pub struct Block {
    kind: BlockKind,
}

pub struct Step {
    transition: Transition,
    success: FlowAction,
    fail: FlowAction,
}

pub enum TreeEvent {
    Open(ScopeHandle),
    Close(ScopeHandle),
    Step(StepHandle),
    Jump(FlowAction),
}

pub struct StructureBuilder {
    events: Vec<TreeEvent>,
    steps: PrimaryMap<StepHandle, Step>,
    blocks: PrimaryMap<ScopeHandle, Block>,
}

impl StructureBuilder {
    pub fn step(&mut self, step: Step) -> StepHandle {
        let handle = self.steps.push(step);
        self.events.push(TreeEvent::Step(handle));
        handle
    }
    pub fn open_block(&mut self, block: Block) -> ScopeHandle {
        let handle = self.blocks.push(block);
        self.events.push(TreeEvent::Open(handle));
        handle
    }
    pub fn close_block(&mut self, handle: ScopeHandle) {
        self.events.push(TreeEvent::Close(handle));
    }
    pub fn jump(&mut self, action: FlowAction) {
        if action != FlowAction::None {
            self.events.push(TreeEvent::Jump(action));
        }
    }
}

pub struct PatternProperties {
    commit_after: bool,
}

fn lower_pattern(
    pattern: &Pattern,
    success: FlowAction,
    fail: FlowAction,

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
            let kind = match group {
                Group::Sequence { .. } | Group::Choice | Group::Maybe => BlockKind::Block,
                Group::Loop => BlockKind::Loop,
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!("Should have been lowered")
                }
            };
            let block = builder.open_block(Block { kind });

            let is_choice = matches!(group, Group::Choice);

            let (next_success, mut next_fail) = match group {
                Group::Choice => (FlowAction::Break(block), FlowAction::None),
                Group::Sequence { .. } => (FlowAction::None, fail),
                Group::Loop => (FlowAction::Continue(block), FlowAction::Break(block)),
                Group::Maybe => (FlowAction::Break(block), FlowAction::Break(block)),
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!()
                }
            };

            // choices start out committed until a child doesn't have a commit_after
            // sequences need any of their children to be commit_after
            let mut commit_after = is_choice;

            // is sequence commited?
            let mut commit = false;
            let commit_index = children
                .iter()
                .position(|child| matches!(child.kind(), PatternKind::Commit));

            for (index, child) in pattern.children().iter().enumerate() {
                let child = lower_pattern(child, next_success, next_fail, grammar, builder);

                if is_choice {
                    commit_after &= child.commit_after;
                } else {
                    commit_after |= child.commit_after;
                }

                // handle sequence committing behaviour
                if !is_choice && !commit {
                    if let Some(commit_index) = commit_index {
                        if commit_index == index {
                            commit = true;
                        }
                    } else {
                        // automatically commit sequence only if commit_index is none (no forced commit)
                        commit |= child.commit_after;
                    }

                    if commit {
                        // committing means that failures act as successes
                        next_fail = next_success;
                    }
                }
            }

            // if control flow reaches the end of this block
            // a choice has exhausted all options and fails,
            // a sequence has matched all its subpatterns and succeeds
            builder.jump(match is_choice {
                true => fail,
                false => success,
            });

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
