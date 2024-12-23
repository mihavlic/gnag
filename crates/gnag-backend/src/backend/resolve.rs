//! Resolve all UnresolvedIdent and UnresolvedLiteral into references. There is are no scopes nor
//! shadowing, templates can be used regardless of which kind of RuleGroup defined them.

use std::collections::{hash_map::Entry, HashMap};

use crate::{
    ast::{
        pattern::{Group, Pattern, PatternKind, Transition},
        RcBytes, RcString,
    },
    error::ErrorAccumulator,
    span::Span,
};

use super::{grammar::Grammar, grammar::RuleHandle, RuleKind};

pub struct ResolveCx<'a> {
    pub err: &'a ErrorAccumulator,
    pub name_to_rule: HashMap<RcString, RuleHandle>,
    pub literal_to_rule: HashMap<RcBytes, RuleHandle>,
}

impl<'a> ResolveCx<'a> {
    pub fn new(grammar: &Grammar, err: &'a ErrorAccumulator) -> ResolveCx<'a> {
        let mut this = ResolveCx {
            err,
            name_to_rule: HashMap::new(),
            literal_to_rule: HashMap::new(),
        };
        this.populate(grammar);
        this
    }

    fn populate(&mut self, grammar: &Grammar) {
        for (handle, rule) in grammar.rules.iter() {
            let entry = self.name_to_rule.entry(rule.name.clone());
            match entry {
                Entry::Occupied(_) => {
                    let ast = grammar.get_ast(handle).unwrap();
                    self.err.error_static(ast.name.span, "Duplicate item name")
                }
                Entry::Vacant(v) => {
                    v.insert(handle);
                }
            }

            if rule.kind.is_lexer() {
                if let PatternKind::UnresolvedLiteral(literal) = rule.pattern.kind() {
                    // duplicates are allowed, we insert the first occurence
                    self.literal_to_rule
                        .entry(literal.clone())
                        .or_insert(handle);
                }
            }
        }
    }
}

pub fn resolve(grammar: &mut Grammar, cx: &ResolveCx) {
    resolve_template_parameters(grammar);
    inline_templates(grammar, cx);
    resolve_identifiers(grammar, cx);
}

fn resolve_template_parameters(grammar: &mut Grammar) {
    for (_, rule, ast) in grammar.modname::iter_mut() {
        if rule.kind == RuleKind::Template {
            let Some(parameters) = &ast.unwrap().parameters else {
                continue;
            };

            rule.pattern.visit_mut(|pattern| {
                if let PatternKind::UnresolvedIdent(ident) = pattern.kind() {
                    if let Some(index) = parameters.iter().position(|p| p.value == *ident) {
                        let index = u32::try_from(index).unwrap();
                        pattern.set_kind(PatternKind::InlineParameter(index));
                    }
                }
            })
        }
    }
}

fn inline_templates(grammar: &mut Grammar, cx: &ResolveCx) {
    let mut call_stack = Vec::<RuleHandle>::new();

    for handle in grammar.keys() {
        // we call the inlining function for every rule, if it contains no inlines, the rule is unchanged
        _ = inline_rule_recursive(handle, grammar, cx, &mut call_stack);
    }
}

fn inline_rule_recursive<'a>(
    handle: RuleHandle,
    grammar: &'a mut Grammar,
    cx: &ResolveCx,
    stack: &mut Vec<RuleHandle>,
) -> Result<&'a Pattern, ()> {
    // TODO the previous implementation was able to detect when a template had been processed by
    // this function and returned immediately instead of again calling visit_mut, which for
    // subsequent invocations of this function shouldn't contain any relevant InlineCalls

    if stack.contains(&handle) {
        let prev = *stack.last().unwrap();
        let prev = grammar.get_ast(prev).unwrap();

        let current = grammar.get_ast(handle).unwrap();

        cx.err.error(
            prev.name.span,
            format_args!(
                "Rule recursively includes itself through {}",
                current.name.value
            ),
        );

        return Err(());
    }

    let pattern = grammar.get_pattern_mut(handle).unwrap();
    // borrow checker doesn't let us hold a mutable reference into Grammar while recursing
    // so we do the good ol' trick of moving it onto the stack and then putting it back
    let mut owned = std::mem::replace(pattern, Pattern::error(Span::empty()));

    stack.push(handle);
    owned.visit_mut(|pattern| {
        if let PatternKind::Group(Group::InlineCall { name }) = pattern.kind() {
            if let Some(&handle) = cx.name_to_rule.get(&name.value) {
                let result = inline_rule_recursive(handle, grammar, cx, stack);
                match result {
                    Ok(inlined) => {
                        let mut inlined = inlined.clone();
                        inline_call(&mut inlined, pattern.children());
                        *pattern = inlined;
                    }
                    Err(()) => {
                        pattern.set_kind(Transition::Error.to_kind());
                    }
                }
            }
        }
    });
    stack.pop();

    let pattern = grammar.get_pattern_mut(handle).unwrap();
    std::mem::swap(pattern, &mut owned);

    Ok(pattern)
}

fn inline_call(pattern: &mut Pattern, arguments: &[Pattern]) {
    pattern.visit_mut(|pattern| {
        if let PatternKind::InlineParameter(index) = *pattern.kind() {
            *pattern = arguments[index as usize].clone();
        }
    });
}

fn resolve_identifiers(grammar: &mut Grammar, cx: &ResolveCx) {
    for (_, rule) in grammar.rules.iter_mut() {
        rule.pattern.visit_mut(|pattern| {
            let span = pattern.span();
            let transition = match pattern.kind() {
                PatternKind::UnresolvedIdent(ident) => {
                    if let Some(&handle) = cx.name_to_rule.get(ident) {
                        Transition::Rule(handle)
                    } else {
                        cx.err.error_static(span, "Unknown item");
                        Transition::Error
                    }
                }
                PatternKind::UnresolvedLiteral(literal) => {
                    match rule.kind {
                        RuleKind::Lexer(_) => Transition::Bytes(literal.clone()),
                        RuleKind::Parser(_) => {
                            if let Some(&handle) = cx.literal_to_rule.get(literal) {
                                Transition::Rule(handle)
                            } else {
                                cx.err.error_static(span, "No corresponding token rule");
                                Transition::Error
                            }
                        }
                        // Resolving literals needs to be done in Lexer/Parser rules only, Templates should have been inlined
                        RuleKind::Template => return,
                    }
                }
                _ => return,
            };
            *pattern = transition.to_pattern(span);
        });
    }
}
