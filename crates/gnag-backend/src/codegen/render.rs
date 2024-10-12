use code_render::{render, render_into, Fragments, RenderCx};
use cranelift_entity::EntitySet;

use crate::{
    ast::{
        display::{ByteExt, ByteSliceExt},
        pattern::{
            AnyPattern, ComparisonKind, ConsumeUntil, NotPattern, Transition, TransitionEffects,
        },
    },
    backend::grammar::Grammar,
};

use super::structure::{Flow, Statement, StructureBuilder, TreeEventValue};

pub fn render_expression(
    builder: &StructureBuilder,
    rcx: &RenderCx,
    grammar: &Grammar,
) -> Fragments {
    let mut is_loop = EntitySet::with_capacity(builder.scopes_len());

    for child in builder.iter() {
        if let TreeEventValue::Statement(_, Statement::Jump(Flow::Continue(scope))) = child {
            is_loop.insert(*scope);
        }
    }

    rcx.scope(|| {
        for child in builder.iter() {
            match child {
                TreeEventValue::Open(handle, _) => {
                    let maybe_loop = match is_loop.contains(handle) {
                        true => "loop",
                        false => "",
                    };
                    render_into!(rcx, #handle: #maybe_loop #"{");
                }
                TreeEventValue::Close(_, _) => render_into!(rcx, #"}"),
                TreeEventValue::Statement(_, statement) => match statement {
                    Statement::Step(step) => {
                        let body = render_transition(&step.transition, rcx, grammar);

                        let effects = step.transition.effects();
                        let success = step.success;
                        let fail = step.fail;

                        match effects {
                            TransitionEffects::Fallible => match (success, fail) {
                                (Flow::None, Flow::None) => {
                                    render_into!(rcx,
                                        #body;
                                    )
                                }
                                (_, Flow::None) => {
                                    render_into!(rcx,
                                        if #body {
                                            #success;
                                        }
                                    )
                                }
                                (Flow::None, _) => {
                                    render_into!(rcx,
                                        if !#body {
                                            #fail;
                                        }
                                    )
                                }
                                _ if success == fail => {
                                    render_into!(rcx,
                                        #body;
                                        #success;
                                    )
                                }
                                _ => {
                                    render_into!(rcx,
                                        match #body {
                                            true => #success,
                                            false => #fail,
                                        }
                                    )
                                }
                            },
                            TransitionEffects::Infallible | TransitionEffects::Noreturn => {
                                render_into!(rcx,
                                    #body;
                                )
                            }
                        }
                    }
                    Statement::Jump(flow) => match flow {
                        Flow::None => {}
                        Flow::Continue(scope) => render_into!(rcx, continue #scope),
                        Flow::Break(scope) => render_into!(rcx, break #scope),
                        Flow::Unreachable => {
                            render_into!(rcx, unreachable!("Flow::Unreachable"))
                        }
                    },
                },
            }
        }
    })
}

fn render_transition(transition: &Transition, rcx: &RenderCx, grammar: &Grammar) -> Fragments {
    match *transition {
        Transition::Error => render!(rcx, panic!("Error")),
        Transition::Rule(handle) => {
            let rule = grammar.get_rule(handle).unwrap();
            let name = &rule.name;

            if rule.kind.is_lexer() {
                render!(rcx, l.token(nodeKind::#name))
            } else {
                render!(rcx, #name (p))
            }
        }
        Transition::Not(ref a) => match *a {
            NotPattern::Byte(a) => render!(rcx, l.not_byte(#{a.display()})),
            NotPattern::Unicode(a) => render!(rcx, l.not_utf8(#a)),
            NotPattern::ByteSet(ref a) => render!(rcx, l.not_byte_set(#a)),
            NotPattern::CharacterClass { class: _, unicode } => match unicode {
                true => render!(rcx, l.not_utf8_class(CharacterClass::TODO)),
                false => render!(rcx, l.not_ascii_class(CharacterClass::TODO)),
            },
            NotPattern::Token(a) => render!(rcx, p.not(NodeKind::#{a.name(grammar)})),
        },
        Transition::Any(ref a) => match a {
            AnyPattern::Byte => render!(rcx, p.any_byte()),
            AnyPattern::Unicode => render!(rcx, p.any_utf8()),
            AnyPattern::Token => render!(rcx, p.any()),
        },
        Transition::ByteSet(ref a) => render!(rcx, l.byte_set(#a)),
        Transition::Bytes(ref a) => render!(rcx, l.bytes(#{a.display()})),
        Transition::CharacterClass { class: _, unicode } => match unicode {
            true => render!(rcx, l.utf8_class(CharacterClass::TODO)),
            false => render!(rcx, l.ascii_class(CharacterClass::TODO)),
        },
        Transition::StringLike { delimiter } => render!(rcx, l.string_like(#{delimiter.display()})),
        Transition::ConsumeUntil {
            ref until,
            inclusive,
        } => match until {
            ConsumeUntil::Byte(a) => render!(rcx,
                l.consume_until_byte(#{a.display()}, #inclusive)
            ),
            ConsumeUntil::Sequence(a) => render!(rcx,
                l.consume_until_sequence(#{a.display()}, #inclusive)
            ),
        },
        Transition::Keyword(ref a) => render!(rcx, l.keyword(#{a.display()})),
        Transition::PrattRule(handle, precedence) => {
            let name = handle.name(grammar);
            render!(rcx, #name (p, #precedence) )
        }
        Transition::CompareBindingPower(comparison, max_precedence) => match comparison {
            ComparisonKind::Lower => render!(rcx, precedence < #max_precedence),
            ComparisonKind::LowerEqual => render!(rcx, precedence <= #max_precedence),
        },
        Transition::SaveState => render!(rcx, let checkpoint = p.save_state()),
        Transition::RestoreState => render!(rcx, p.restore_state(checkpoint)),
        Transition::CloseSpan(a) => render!(rcx, p.close_span(NodeKind::#{a.name(grammar)})),
        Transition::Return(a) => render!(rcx, return #a),
        Transition::LexerReturn(a) => match a {
            Some(a) => render!(rcx, return Some(NodeKind::#{a.name(grammar)})),
            None => render!(rcx, return None),
        },
    }
}
