use gnag_runtime::lexer::CharacterClass;

use crate::{
    ast::{
        pattern::{AnyPattern, ConsumeUntil, Group, NotPattern, Pattern, PatternKind, Transition},
        Ident,
    },
    span::Span,
};

use super::lower::LowerCx;

pub fn lower_builtin(pattern: &mut Pattern, name: &Ident, cx: &LowerCx) -> Pattern {
    let span = pattern.span();
    let parameters = pattern.children_vec_mut();

    let error = || -> Pattern { Transition::Error.to_pattern(span) };

    let mut expect_count = |c: usize, ok: &dyn Fn(&mut Vec<Pattern>) -> Pattern| {
        if parameters.len() != c {
            cx.err
                .error(name.span, format_args!("Expected {c} arguments"));
            error()
        } else {
            ok(parameters)
        }
    };

    match &*name.value {
        "commit" => expect_count(0, &|_| PatternKind::Commit.to_pattern(span)),
        "not" => expect_count(1, &|args| {
            let argument = &args.first().unwrap();

            'block: {
                if let PatternKind::Transition(transition) = argument.kind() {
                    let pattern = match transition {
                        Transition::Bytes(bytes) => {
                            if let Ok(str) = std::str::from_utf8(&**bytes) {
                                let mut chars = str.chars();
                                let first = chars.next();
                                let second = chars.next();

                                if let (Some(first), None) = (first, second) {
                                    if first.is_ascii() {
                                        NotPattern::Byte(first as u8)
                                    } else {
                                        NotPattern::Unicode(first)
                                    }
                                } else {
                                    cx.err.error_static(
                                        argument.span(),
                                        "Expected a single character",
                                    );
                                    return error();
                                }
                            } else {
                                if let &[byte] = &**bytes {
                                    NotPattern::Byte(byte)
                                } else {
                                    cx.err
                                        .error_static(argument.span(), "Expected a single byte");
                                    return error();
                                }
                            }
                        }
                        Transition::ByteSet(set) => NotPattern::ByteSet(set.clone()),
                        &Transition::CharacterClass { class, unicode } => {
                            NotPattern::CharacterClass { class, unicode }
                        }
                        &Transition::Rule(handle) => NotPattern::Token(handle),
                        _ => break 'block,
                    };

                    return Transition::Not(pattern).to_pattern(span);
                }
            }

            cx.err
                .error(argument.span(), "Unexpected argument for <not>");
            error()
        }),
        "separated_list" => expect_count(2, &|args| {
            args.push(PatternKind::Commit.to_pattern(Span::empty()));

            let sequence =
                Group::Sequence { explicit: true }.to_pattern(std::mem::take(args), span);
            Group::Loop.to_pattern(vec![sequence], span)
        }),
        "consume_until" => expect_count(1, &|args| {
            let argument = &args[0];
            if let PatternKind::Transition(Transition::Bytes(bytes)) = argument.kind() {
                let until = match bytes.len() {
                    1 => ConsumeUntil::Byte(bytes[0]),
                    _ => ConsumeUntil::Sequence(bytes.clone()),
                };
                Transition::ConsumeUntil {
                    until,
                    inclusive: false,
                }
                .to_pattern(span)
            } else {
                cx.err.error(argument.span(), "Expected literal");
                error()
            }
        }),
        "string_like" => expect_count(1, &|args| {
            let argument = &args[0];
            if let PatternKind::Transition(Transition::Bytes(bytes)) = argument.kind() {
                match bytes.len() {
                    1 => {
                        return Transition::StringLike {
                            delimiter: bytes[0],
                        }
                        .to_pattern(span);
                    }
                    _ => {
                        cx.err
                            .error(argument.span(), "Argument must be a single byte");
                        error()
                    }
                }
            } else {
                cx.err.error(argument.span(), "Expected literal");
                error()
            }
        }),
        _ => {
            let transition = match_transition(name);
            if let Some(transition) = transition {
                if pattern.children().is_empty() {
                    transition.to_pattern(span)
                } else {
                    cx.err.error_static(name.span, "Expected 0 arguments");
                    error()
                }
            } else {
                cx.err.error_static(name.span, "Expected inline or builtin");
                error()
            }
        }
    }
}

fn match_transition(name: &Ident) -> Option<Transition> {
    let transition = match &*name.value {
        "any" => Transition::Any(AnyPattern::Token),
        "any_byte" => Transition::Any(AnyPattern::Byte),
        "any_utf8" => Transition::Any(AnyPattern::Unicode),
        "ascii_identifier_start" => Transition::CharacterClass {
            class: CharacterClass::IdentifierStart,
            unicode: false,
        },
        "ascii_identifier_continue" => Transition::CharacterClass {
            class: CharacterClass::IdentifierContinue,
            unicode: false,
        },
        "ascii_alphabetic" => Transition::CharacterClass {
            class: CharacterClass::Alphabetic,
            unicode: false,
        },
        "ascii_lowercase" => Transition::CharacterClass {
            class: CharacterClass::Lowercase,
            unicode: false,
        },
        "ascii_uppercase" => Transition::CharacterClass {
            class: CharacterClass::Uppercase,
            unicode: false,
        },
        "ascii_digit" => Transition::CharacterClass {
            class: CharacterClass::Digit,
            unicode: false,
        },
        "ascii_hexdigit" => Transition::CharacterClass {
            class: CharacterClass::Hexdigit,
            unicode: false,
        },
        "ascii_alphanumeric" => Transition::CharacterClass {
            class: CharacterClass::Alphanumeric,
            unicode: false,
        },
        "ascii_punctuation" => Transition::CharacterClass {
            class: CharacterClass::Punctuation,
            unicode: false,
        },
        "ascii_whitespace" => Transition::CharacterClass {
            class: CharacterClass::Whitespace,
            unicode: false,
        },
        "unicode_identifier_start" => Transition::CharacterClass {
            class: CharacterClass::IdentifierStart,
            unicode: true,
        },
        "unicode_identifier_continue" => Transition::CharacterClass {
            class: CharacterClass::IdentifierContinue,
            unicode: true,
        },
        "unicode_alphabetic" => Transition::CharacterClass {
            class: CharacterClass::Alphabetic,
            unicode: true,
        },
        "unicode_lowercase" => Transition::CharacterClass {
            class: CharacterClass::Lowercase,
            unicode: true,
        },
        "unicode_uppercase" => Transition::CharacterClass {
            class: CharacterClass::Uppercase,
            unicode: true,
        },
        "unicode_digit" => Transition::CharacterClass {
            class: CharacterClass::Digit,
            unicode: true,
        },
        "unicode_hexdigit" => Transition::CharacterClass {
            class: CharacterClass::Hexdigit,
            unicode: true,
        },
        "unicode_alphanumeric" => Transition::CharacterClass {
            class: CharacterClass::Alphanumeric,
            unicode: true,
        },
        "unicode_punctuation" => Transition::CharacterClass {
            class: CharacterClass::Punctuation,
            unicode: true,
        },
        "unicode_whitespace" => Transition::CharacterClass {
            class: CharacterClass::Whitespace,
            unicode: true,
        },
        _ => return None,
    };
    Some(transition)
}
