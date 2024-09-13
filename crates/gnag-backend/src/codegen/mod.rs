#![allow(dead_code)]

pub mod structure;

use std::{cell::Cell, fmt::Display};

use code_render::{render, CollectFragments, Fragment, RenderCx};

use crate::{
    ast::{
        display::{ByteExt, ByteSliceExt},
        pattern::{
            AnyPattern, ComparisonKind, ConsumeUntil, Group, NotPattern, Pattern, PatternKind,
            Transition, TransitionEffects,
        },
    },
    backend::{grammar::Grammar, LexerKind, ParserKind, Rule, RuleKind},
};

#[derive(Display)]
struct MaybeUsed {
    used: Cell<bool>,
}

impl MaybeUsed {
    fn new() -> MaybeUsed {
        MaybeUsed {
            used: Cell::new(false),
        }
    }
    fn set_used(&self) {
        self.used.set(true);
    }
    fn is_used(&self) -> bool {
        self.used.get()
    }
}

impl Display for FlowAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FlowAction::Continue(a) => write!(f, "continue {a}"),
            FlowAction::Break(a) => write!(f, "break {a}"),
            FlowAction::FallThrough => write!(f, "{{}}"),
            FlowAction::Unreachable => write!(f, "unreachable!()"),
            FlowAction::Never => Ok(()),
        }
    }
}

fn display_pattern(
    pattern: &Pattern,

    success: FlowAction,
    fail: FlowAction,

    block: BlockLabel,
    rcx: &RenderCx,
    grammar: &Grammar,
) -> Fragment {
    let children = pattern.children();

    match pattern.kind() {
        PatternKind::Transition(transition) => {
            let body = display_transition(transition, rcx, grammar);

            let effects = transition.effects();

            match effects {
                TransitionEffects::Fallible => match (success, fail) {
                    (FlowAction::FallThrough, FlowAction::FallThrough) => {
                        render!(rcx,
                            #body;
                        )
                    }
                    (_, FlowAction::FallThrough) => {
                        render!(rcx,
                            if #body {
                                #success;
                            }
                        )
                    }
                    (FlowAction::FallThrough, _) => {
                        render!(rcx,
                            if !#body {
                                #fail;
                            }
                        )
                    }
                    _ if success == fail => {
                        render!(rcx,
                            #body;
                            #success;
                        )
                    }
                    _ => {
                        render!(rcx,
                            match #body {
                                true => #success,
                                false => #fail,
                            }
                        )
                    }
                },
                TransitionEffects::Infallible | TransitionEffects::Noreturn => {
                    render!(rcx,
                        #body;
                    )
                }
            }
        }
        PatternKind::Group(group) => {
            let (next_success, next_fail) = match group {
                Group::Choice => (FlowAction::Break(block), FlowAction::FallThrough),
                Group::Sequence { .. } => (FlowAction::FallThrough, fail),
                Group::Loop => (FlowAction::Continue(block), FlowAction::Break(block)),
                Group::Maybe => (FlowAction::Break(block), FlowAction::Break(block)),
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!("Should have been lowered")
                }
            };

            let statements = children
                .iter()
                .map(|child| {
                    display_pattern(child, next_success, next_fail, block.next(), rcx, grammar)
                })
                .collect_fragments(rcx);

            match group {
                Group::Choice => {
                    render!(rcx,
                        #block: {
                            #{statements}*
                            #fail
                        }
                    )
                }
                Group::Sequence { .. } => {
                    render!(rcx,
                        #block: {
                            #{statements}*
                            #success
                        }
                    )
                }
                Group::Loop => {
                    render!(rcx,
                        #block: loop {
                            #{statements}*
                        }
                        #success
                    )
                }
                Group::Maybe => {
                    render!(rcx,
                        #{statements}*
                        #success
                    )
                }
                Group::OneOrMore | Group::InlineCall { .. } => {
                    unreachable!("Should have been lowered")
                }
            }
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

fn display_transition(transition: &Transition, rcx: &RenderCx, grammar: &Grammar) -> Fragment {
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

fn display_rule(rule: &Rule, grammar: &Grammar, rcx: &RenderCx) -> Fragment {
    let body = display_pattern(
        &rule.pattern,
        FlowAction::Return(true),
        FlowAction::Return(false),
        BlockLabel::default(),
        rcx,
        grammar,
    );

    render!(rcx,
        pub fn #{rule.name}(p: &mut Parser) -> bool {
            #body
        }
    )
}

pub fn display_file(grammar: &Grammar, rcx: &RenderCx) -> Fragment {
    let functions = grammar
        .iter()
        .filter(|(_, rule, _)| match rule.kind {
            RuleKind::Lexer(LexerKind::Lexer) => true,
            RuleKind::Parser(ParserKind::Pratt | ParserKind::Rule) => true,
            _ => false,
        })
        .map(|(_, rule, _)| {
            render!(rcx,
                #{display_rule(rule, grammar, rcx)}
                #"\n\n"
            )
        });

    render!(rcx,
        use gnag_runtime::lexer::*;
        use gnag_runtime::parser::*;
        use gnag_runtime::*;

        #{functions}*
    )
}

fn a() {
    // RuleGroup =
    // Sequence
    //     Choice
    //       Rule(LexerKeyword)
    //       Rule(ParserKeyword)
    //     Sequence
    //         Loop
    //             Rule(Newline)
    //         Rule(LCurly)
    //         Loop
    //             Choice
    //                 Rule(Newline)
    //                 Rule(Rule)
    //         Rule(RCurly)

    // {
    //     'b1: {
    //         if l.token(nodeKind::LexerKeyword) {
    //             break 'b1;
    //         }
    //         if l.token(nodeKind::ParserKeyword) {
    //             break 'b1;
    //         }
    //         return false;
    //     }
    //     loop {
    //         if !l.token(nodeKind::Newline) {
    //             break;
    //         }
    //     }
    //     if !l.token(nodeKind::LCurly) {
    //         return false;
    //     }
    //     'b2: loop {
    //         'b3: {
    //             if l.token(nodeKind::Newline) {
    //                 break 'b3;
    //             }
    //             if Rule(p) {
    //                 break 'b3;
    //             }
    //             break 'b2;
    //         }
    //     }
    //     {}
    //     if !l.token(nodeKind::RCurly) {
    //         return false;
    //     }
    // }
}
