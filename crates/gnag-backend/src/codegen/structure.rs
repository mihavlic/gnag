use std::fmt::Display;

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
}

pub enum ScopeKind {
    Block,
    Loop,
}

pub struct Scope {
    kind: ScopeKind,
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
    scopes: PrimaryMap<ScopeHandle, Scope>,
}

impl StructureBuilder {
    pub fn step(&mut self, step: Step) -> StepHandle {
        let handle = self.steps.push(step);
        self.events.push(TreeEvent::Step(handle));
        handle
    }
    pub fn scope(
        &mut self,
        scope: Scope,
        mut fun: impl FnMut(&mut StructureBuilder),
    ) -> ScopeHandle {
        let handle = self.scopes.push(scope);
        self.events.push(TreeEvent::Open(handle));
        fun(self);
        self.events.push(TreeEvent::Close(handle));
        handle
    }
    pub fn jump(&mut self, action: FlowAction) {
        self.events.push(TreeEvent::Jump(action));
    }
}

fn pattern(
    pattern: &Pattern,
    success: FlowAction,
    fail: Option<FlowAction>,

    grammar: &Grammar,
    builder: &mut StructureBuilder,
) {
    let children = pattern.children();

    match pattern.kind() {
        PatternKind::Transition(transition) => {
            builder.step(Step {
                transition: transition.clone(),
                success,
                fail,
            });
        }
        PatternKind::Group(group) => {
            let (next_success, next_fail) = match group {
                Group::Choice => (FlowAction::Break(block), None),
                Group::Sequence { .. } => (FlowAction::FallThrough, Some(fail)),
                Group::Loop => (FlowAction::Continue(block), Some(FlowAction::Break(block))),
                Group::Maybe => (FlowAction::Break(block), Some(FlowAction::Break(block))),
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!("Should have been lowered")
                }
            };

            builder.scope(Scope { handle: , kind:  }, |builder| {
                for child in pattern.children() {
                    pattern(child, next_success, next_fail, rcx, grammar, builder);
                }

                match group {
                    Group::Choice => {
                        builder.jump(fail);
                    }
                    Group::Sequence { .. } | Group::Loop | Group::Maybe => {
                        builder.jump(success);
                    }
                    Group::OneOrMore | Group::InlineCall { .. } => {
                        unreachable!("Should have been lowered")
                    }
                }
            });
        }
        PatternKind::Commit => {
            render!(rcx,
                unreachable!("TODO remove commit");
            )
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
