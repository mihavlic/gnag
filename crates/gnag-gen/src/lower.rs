use std::{
    borrow::Borrow,
    collections::{hash_map::Entry, HashMap},
    rc::Rc,
};

use crate::{
    convert::{ConvertedFile, InlineHandle, ItemKind, RuleBody, RuleHandle},
    expr::{CallExpr, CharacterClass, NotPattern, RuleExpr, Transition},
    pratt::{Associativity, PrattExprKind},
};
use gnag::{
    ast::RuleKind,
    ctx::ErrorAccumulator,
    handle::{HandleVec, SecondaryVec},
    StrSpan,
};

struct LoweringCx<'a, 'b, 'c> {
    src: &'a str,
    err: &'b ErrorAccumulator,
    file: &'c ConvertedFile,
    name_to_item: HashMap<&'c str, ItemKind>,
    literal_to_token: HashMap<&'c [u8], RuleHandle>,
    inlined_inlines: SecondaryVec<InlineHandle, RuleExpr>,
    stack: Vec<InlineHandle>,
}

impl<'a, 'b, 'c> Borrow<str> for LoweringCx<'a, 'b, 'c> {
    fn borrow(&self) -> &str {
        self.src
    }
}

impl<'a, 'b, 'c> LoweringCx<'a, 'b, 'c> {
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.err.error(span, err)
    }
}

impl<'a, 'b, 'c> LoweringCx<'a, 'b, 'c> {
    fn new(src: &'a str, err: &'b ErrorAccumulator, file: &'c ConvertedFile) -> Self {
        Self {
            src,
            err,
            file,
            name_to_item: HashMap::new(),
            literal_to_token: HashMap::new(),
            inlined_inlines: SecondaryVec::with_capacity(file.inlines.len()),
            stack: Vec::new(),
        }
    }

    fn add_item(&mut self, body: &'c RuleBody, handle: ItemKind) {
        match self.name_to_item.entry(&body.name) {
            Entry::Occupied(_) => {
                self.error(body.name_span, "Duplicate item name");
            }
            Entry::Vacant(v) => {
                v.insert(handle);
            }
        }
    }

    fn add_literal(&mut self, value: &'c [u8], handle: RuleHandle) {
        match self.literal_to_token.entry(value) {
            Entry::Occupied(_) => {
                // Do nothing, duplicate token expressions are not an error
            }
            Entry::Vacant(v) => {
                v.insert(handle);
            }
        }
    }

    fn populate_hashmaps(&mut self) {
        for (handle, rule) in self.file.rules.iter_kv() {
            self.add_item(&rule.body, ItemKind::Rule(handle));
            if rule.kind == RuleKind::Tokens {
                if let RuleExpr::UnresolvedLiteral { bytes, .. } = &rule.body.expr {
                    self.add_literal(bytes, handle);
                }
            }
        }
        for (handle, rule) in self.file.inlines.iter_kv() {
            self.add_item(&rule.body, ItemKind::Inline(handle));
        }
    }

    fn populate_inlines(&mut self) {
        for handle in self.file.inlines.iter_keys() {
            _ = self.get_inline(handle);
        }
    }

    fn get_inline(&mut self, handle: InlineHandle) -> &RuleExpr {
        // NLL issue workaround https://github.com/rust-lang/rust/issues/54663#issuecomment-973936708
        if self.inlined_inlines.get(handle).is_some() {
            return self.inlined_inlines.get(handle).unwrap();
        }

        let ir = &self.file.inlines[handle];

        if self.stack.contains(&handle) {
            let prev = *self.stack.last().unwrap();
            let prev_name = &self.file.inlines[prev].body.name;
            let prev_span = self.file.inlines[prev].body.span;

            self.error(
                prev_span,
                format_args!(
                    "Rule {} recursively includes itself through {}",
                    prev_name, ir.body.name
                ),
            );
        }

        let mut expr = ir.body.expr.clone();

        self.stack.push(handle);
        expr.visit_nodes_bottom_up_mut(|node| match node {
            RuleExpr::InlineCall(call) => {
                *node = lower_call(call, self);
            }
            _ => (),
        });
        self.stack.pop();

        self.inlined_inlines.entry(handle).insert(expr)
    }
}

fn lower_builtin(call: &CallExpr, cx: &mut LoweringCx) -> RuleExpr {
    let CallExpr {
        name,
        name_span,
        parameters,
        ..
    } = call;

    let expect_count = |c: usize, ok: &dyn Fn(&[RuleExpr]) -> RuleExpr| -> RuleExpr {
        if parameters.len() != c {
            cx.error(*name_span, format_args!("expected {c} arguments"));
            RuleExpr::error()
        } else {
            ok(parameters)
        }
    };

    match name.as_str() {
        "any_byte" => expect_count(0, &|_| RuleExpr::Transition(Transition::AnyByte)),
        "any_utf8" => expect_count(0, &|_| RuleExpr::Transition(Transition::AnyUtf8)),
        "any" => expect_count(0, &|_| RuleExpr::Transition(Transition::AnyToken)),
        "commit" => expect_count(0, &|_| RuleExpr::Commit),
        "not" => expect_count(1, &|args| {
            'block: {
                if let RuleExpr::Transition(transition) = args.first().unwrap() {
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
                                    cx.error(*name_span, "Expected a single character");
                                    return RuleExpr::error();
                                }
                            } else {
                                if let &[byte] = &**bytes {
                                    NotPattern::Byte(byte)
                                } else {
                                    cx.error(*name_span, "Expected a single byte");
                                    return RuleExpr::error();
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

                    return RuleExpr::Transition(Transition::Not(pattern));
                }
            }

            cx.error(*name_span, "Unexpected argument for <not>");
            RuleExpr::error()
        }),
        "separated_list" => expect_count(2, &|args| RuleExpr::SeparatedList {
            separator: Box::new(args[0].clone()),
            element: Box::new(args[1].clone()),
        }),
        "consume_until" => expect_count(1, &|args| {
            if let RuleExpr::Transition(Transition::Bytes(bytes)) = &args[0] {
                match bytes.len() {
                    1 => RuleExpr::Transition(Transition::ConsumeUntilByte {
                        byte: bytes[0],
                        inclusive: false,
                    }),
                    _ => RuleExpr::Transition(Transition::ConsumeUntilSequence {
                        sequence: bytes.clone(),
                        inclusive: false,
                    }),
                }
            } else {
                cx.error(*name_span, "Unexpected argument for <consume_until>");
                RuleExpr::error()
            }
        }),
        "string_like" => expect_count(1, &|args| {
            if let RuleExpr::Transition(Transition::Bytes(bytes)) = &args[0] {
                match bytes.len() {
                    1 => RuleExpr::Transition(Transition::StringLike {
                        delimiter: bytes[0],
                    }),
                    _ => {
                        cx.error(*name_span, "<string_like> argument must be a single byte");
                        RuleExpr::error()
                    }
                }
            } else {
                cx.error(*name_span, "Unexpected argument for <string_like>");
                RuleExpr::error()
            }
        }),
        "ascii_identifier_start" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::IdentifierStart,
            unicode: false,
        }),
        "ascii_identifier_continue" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::IdentifierContinue,
            unicode: false,
        }),
        "ascii_alphabetic" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Alphabetic,
            unicode: false,
        }),
        "ascii_lowercase" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Lowercase,
            unicode: false,
        }),
        "ascii_uppercase" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Uppercase,
            unicode: false,
        }),
        "ascii_digit" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Digit,
            unicode: false,
        }),
        "ascii_hexdigit" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Hexdigit,
            unicode: false,
        }),
        "ascii_alphanumeric" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Alphanumeric,
            unicode: false,
        }),
        "ascii_punctuation" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Punctuation,
            unicode: false,
        }),
        "ascii_whitespace" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Whitespace,
            unicode: false,
        }),
        "unicode_identifier_start" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::IdentifierStart,
            unicode: true,
        }),
        "unicode_identifier_continue" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::IdentifierContinue,
            unicode: true,
        }),
        "unicode_alphabetic" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Alphabetic,
            unicode: true,
        }),
        "unicode_lowercase" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Lowercase,
            unicode: true,
        }),
        "unicode_uppercase" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Uppercase,
            unicode: true,
        }),
        "unicode_digit" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Digit,
            unicode: true,
        }),
        "unicode_hexdigit" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Hexdigit,
            unicode: true,
        }),
        "unicode_alphanumeric" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Alphanumeric,
            unicode: true,
        }),
        "unicode_punctuation" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Punctuation,
            unicode: true,
        }),
        "unicode_whitespace" => RuleExpr::Transition(Transition::CharacterClass {
            class: CharacterClass::Whitespace,
            unicode: true,
        }),
        _ => {
            cx.error(*name_span, format_args!("Expected inline or builtin"));
            RuleExpr::error()
        }
    }
}

fn lower_call(call: &CallExpr, cx: &mut LoweringCx) -> RuleExpr {
    let CallExpr {
        ref name,
        name_span,
        ref parameters,
        span,
    } = *call;

    let handle = match cx.name_to_item.get(&**name).cloned() {
        Some(ItemKind::Inline(a)) => a,
        Some(ItemKind::Rule(_)) => {
            cx.error(name_span, "Expected inline");
            return RuleExpr::error();
        }
        None => return lower_builtin(call, cx),
    };

    // try to get the expanded body first because doing so can generate errors
    let mut expanded = cx.get_inline(handle).clone();

    let rule_ir = &cx.file.inlines[handle];

    let expected_len = rule_ir.parameters.len();
    let provided_len = parameters.len();
    if expected_len != provided_len {
        cx.error(
            span,
            format_args!("Expected {expected_len} arguments, got {provided_len}"),
        );
        RuleExpr::error()
    } else {
        if !parameters.is_empty() {
            expanded.visit_nodes_bottom_up_mut(|node| {
                if let &mut RuleExpr::InlineParameter(pos) = node {
                    *node = parameters
                        .get(pos)
                        .expect("InlineParameter out of bounds??")
                        .clone();
                }
            });
        }
        expanded
    }
}

pub fn visit_affix_leaves(
    expr: &mut RuleExpr,
    prefix: bool,
    on_leaf: &mut dyn FnMut(&mut RuleExpr) -> bool,
) -> Option<bool> {
    match expr {
        RuleExpr::Transition(_) => Some(on_leaf(expr)),
        RuleExpr::Sequence(vec) => {
            let expr = match prefix {
                true => vec.first_mut(),
                false => vec.last_mut(),
            };
            expr.and_then(|e| visit_affix_leaves(e, prefix, on_leaf))
        }
        RuleExpr::Choice(vec) => {
            let mut contains_true = false;
            let mut contains_false = false;

            for expr in vec {
                match visit_affix_leaves(expr, prefix, on_leaf) {
                    Some(true) => contains_true = true,
                    Some(false) => contains_false = true,
                    None => return None,
                }
            }

            // children must all be true or all false, otherwise return None
            match (contains_true, contains_false) {
                (true, false) => Some(true),
                (false, true) => Some(false),
                _ => None,
            }
        }
        RuleExpr::Loop(a) | RuleExpr::Maybe(a) => {
            // these constructs are fine if they do not contain a recursive affix
            match visit_affix_leaves(a, prefix, on_leaf) {
                Some(false) => Some(false),
                _ => None,
            }
        }
        RuleExpr::SeparatedList {
            element,
            separator: _,
        } => {
            if prefix {
                match visit_affix_leaves(element, prefix, on_leaf) {
                    Some(false) => Some(false),
                    _ => None,
                }
            } else {
                None
            }
        }
        RuleExpr::OneOrMore(_)
        | RuleExpr::InlineParameter(_)
        | RuleExpr::InlineCall(_)
        | RuleExpr::UnresolvedIdentifier { .. }
        | RuleExpr::UnresolvedLiteral { .. } => {
            unreachable!("These should have been eliminated during lowering")
        }
        RuleExpr::Commit | RuleExpr::Pratt(_) => None,
    }
}

fn lower_pratt(
    parent: RuleHandle,
    children: &[RuleHandle],
    lowered_rules: &HandleVec<RuleHandle, RuleExpr>,
    cx: &mut LoweringCx,
) -> RuleExpr {
    let parent = Some(parent).filter(|handle| {
        let converted = &cx.file.rules[*handle];
        converted.kind == RuleKind::Rules
    });

    let Some(current_rule) = parent else {
        cx.error(
            StrSpan::empty(),
            "(TODO span) pratt expressions can only be in Rules",
        );
        return RuleExpr::error();
    };

    let handle_expr = |expr: &mut RuleExpr, prefix: bool| {
        if let RuleExpr::Transition(Transition::Rule(rule)) = expr {
            if *rule == current_rule {
                *expr = match prefix {
                    // binding power will be added later
                    true => RuleExpr::Transition(Transition::CompareBindingPower(0)),
                    false => RuleExpr::Transition(Transition::PrattRule(*rule, 0)),
                };
                return true;
            }
        }
        false
    };

    let mut atoms = Vec::new();
    let mut suffixes = Vec::new();
    let mut bp_offset = 1;
    for &handle in children {
        let rule = &cx.file.rules[handle];
        let mut expr = lowered_rules[handle].clone();

        let has_prefix = visit_affix_leaves(&mut expr, true, &mut |expr| handle_expr(expr, true));
        let has_suffix = visit_affix_leaves(&mut expr, false, &mut |expr| handle_expr(expr, false));

        let kind = match has_prefix {
            Some(true) => {
                if has_suffix == Some(true) {
                    let assoc = match rule.body.attributes.right_assoc {
                        true => Associativity::Right,
                        false => Associativity::Left,
                    };
                    PrattExprKind::Binary(assoc)
                } else {
                    PrattExprKind::Suffix
                }
            }
            Some(false) => {
                if has_suffix != Some(true) || rule.body.attributes.atom {
                    PrattExprKind::Atom
                } else {
                    PrattExprKind::Prefix
                }
            }
            None => {
                // TODO report error
                expr = RuleExpr::error();
                PrattExprKind::Atom
            }
        };

        let (l_bp, r_bp) = kind.get_binding_power(&mut bp_offset);

        if let Some(bp) = l_bp {
            visit_affix_leaves(&mut expr, true, &mut |expr| {
                if let RuleExpr::Transition(Transition::CompareBindingPower(power)) = expr {
                    *power = bp
                }
                true
            });
        }

        if let Some(bp) = r_bp {
            visit_affix_leaves(&mut expr, false, &mut |expr| {
                if let RuleExpr::Transition(Transition::PrattRule(_, power)) = expr {
                    *power = bp
                }
                true
            });
        }

        expr.to_sequence()
            .push(RuleExpr::Transition(Transition::CloseSpan(handle)));

        let dest = match kind {
            PrattExprKind::Atom | PrattExprKind::Prefix => &mut atoms,
            PrattExprKind::Suffix | PrattExprKind::Binary(_) => &mut suffixes,
        };
        dest.push(expr);
    }

    let mangled = if suffixes.is_empty() {
        RuleExpr::Choice(atoms)
    } else {
        RuleExpr::Sequence(vec![
            RuleExpr::Choice(atoms),
            RuleExpr::Loop(Box::new(RuleExpr::Choice(suffixes))),
        ])
    };

    mangled
}

fn lower_reference(name: &str, name_span: StrSpan, cx: &mut LoweringCx) -> RuleExpr {
    let handle = cx.name_to_item.get(name).cloned();
    match handle {
        Some(ItemKind::Inline(_)) => {
            cx.error(name_span, "Use <> syntax for inlines");
            RuleExpr::error()
        }
        Some(ItemKind::Rule(a)) => RuleExpr::rule(a),
        None => {
            cx.error(name_span, "Unknown item");
            RuleExpr::error()
        }
    }
}

fn lower_expr(
    parent: RuleHandle,
    expr: &mut RuleExpr,
    lowered_rules: &HandleVec<RuleHandle, RuleExpr>,
    cx: &mut LoweringCx,
) {
    expr.visit_nodes_bottom_up_mut(|node| match node {
        RuleExpr::Pratt(vec) => *node = lower_pratt(parent, vec, lowered_rules, cx),
        RuleExpr::InlineCall(call) => {
            *node = lower_call(call, cx);
            // we need to recurse like this, because lowering UnresolvedLiteral
            // depends on where the call is inlined
            lower_expr(parent, node, lowered_rules, cx);
        }
        // it is currently correct to resolve references in the same traversal as other lowering because we're going bottom-up
        // the only lowering which touches other rules is pratt, where children are inserted before their parents before conversion
        RuleExpr::UnresolvedIdentifier { name, name_span } => {
            *node = lower_reference(name, *name_span, cx);
        }
        RuleExpr::UnresolvedLiteral { bytes, span } => {
            *node = lower_literal(parent, bytes, *span, cx);
        }
        RuleExpr::OneOrMore(expr) => {
            let expr = expr.take();
            *node = RuleExpr::Sequence(vec![expr.clone(), RuleExpr::Loop(Box::new(expr))]);
        }
        // RuleExpr::Sequence(vec) => {
        //     if vec.len() == 1 {
        //         *node = vec.pop().unwrap();
        //     }
        // }
        // RuleExpr::Choice(vec) => {
        //     let mut needs_cleanup = false;
        //     for expr in vec.iter() {
        //         if let RuleExpr::Choice(_) = expr {
        //             needs_cleanup = true;
        //             break;
        //         }
        //     }

        //     if needs_cleanup {
        //         let mut new_vec = Vec::with_capacity(vec.len());
        //         for expr in vec.iter_mut() {
        //             if let RuleExpr::Choice(child_vec) = expr {
        //                 new_vec.append(child_vec);
        //             } else {
        //                 new_vec.push(expr.take());
        //             }
        //         }
        //         *vec = new_vec;
        //     }
        // }
        _ => (),
    });
}

fn lower_literal(
    parent: RuleHandle,
    bytes: &Rc<[u8]>,
    span: StrSpan,
    cx: &mut LoweringCx,
) -> RuleExpr {
    let converted = &cx.file.rules[parent];
    if converted.kind == RuleKind::Rules {
        match cx.literal_to_token.get(&**bytes) {
            Some(a) => RuleExpr::rule(*a),
            None => {
                cx.error(span, "(TODO span) No matching token");
                RuleExpr::error()
            }
        }
    } else {
        RuleExpr::bytes(bytes.clone())
    }
}

pub struct LoweredFile {
    pub rules: HandleVec<RuleHandle, RuleExpr>,
}

impl LoweredFile {
    pub fn new(src: &str, err: &ErrorAccumulator, file: &ConvertedFile) -> LoweredFile {
        let mut cx = LoweringCx::new(src, err, file);
        cx.populate_hashmaps();
        cx.populate_inlines();

        let mut rules = file.rules.map_ref(|rule| rule.body.expr.clone());

        for handle in rules.iter_keys() {
            let mut expr = rules[handle].take();
            // borrowchecker crimes because pratt lowering needs to look at its children
            // which are thankfully ordered such that they always get lowered before their parent
            lower_expr(handle, &mut expr, &mut rules, &mut cx);
            _ = std::mem::replace(&mut rules[handle], expr);
        }

        LoweredFile { rules }
    }
}
