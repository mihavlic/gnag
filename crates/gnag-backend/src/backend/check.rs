use std::collections::HashMap;

use cranelift_entity::{EntitySet, SecondaryMap};

use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition},
    error::ErrorAccumulator,
    span::Span,
};

use super::grammar::{Grammar, RuleHandle};

pub fn check_left_recursion(grammar: &Grammar, err: &ErrorAccumulator) {
    let mut prefix_rules = SecondaryMap::new();

    for (handle, rule, _) in grammar.iter() {
        let mut set = HashMap::new();
        collect_prefix_rules(&rule.pattern, &mut set);
        prefix_rules[handle] = set;
    }

    let mut visited = EntitySet::new();
    let mut stack = Vec::new();
    for (handle, ..) in grammar.iter() {
        for (&handle, &span) in &prefix_rules[handle] {
            find_prefix_cycles(
                handle,
                span,
                &prefix_rules,
                &mut visited,
                &mut stack,
                grammar,
                err,
            );
        }
    }
}

fn collect_prefix_rules(pattern: &Pattern, rules: &mut HashMap<RuleHandle, Span>) -> bool {
    match pattern.kind() {
        PatternKind::Group(g) => {
            let children = pattern.children();
            match g {
                Group::Sequence { explicit: _ } => {
                    for child in children {
                        // TODO handle commit behaviour - we should visit every rule after commit if the preceding do not end the loop before that
                        if collect_prefix_rules(child, rules) {
                            return true;
                        }
                    }
                    false
                }
                Group::Choice => {
                    let mut all_true = true;
                    for child in children {
                        all_true &= collect_prefix_rules(child, rules);
                    }
                    all_true
                }
                Group::Loop | Group::Maybe => {
                    let child = children.first().unwrap();
                    collect_prefix_rules(child, rules);
                    false
                }
                Group::OneOrMore | Group::InlineCall { name: _ } => {
                    unreachable!("Should have been lowered")
                }
            }
        }
        PatternKind::Transition(transition) => {
            if let Transition::Rule(handle) = transition {
                rules.entry(*handle).or_insert(pattern.span());
            }
            transition.advances_parser()
        }
        PatternKind::UnresolvedIdent(_)
        | PatternKind::UnresolvedLiteral(_)
        | PatternKind::InlineParameter(_)
        | PatternKind::Pratt(_) => unreachable!("Should have been lowered"),
        PatternKind::Commit => false,
    }
}

fn find_prefix_cycles(
    handle: RuleHandle,
    span: Span,

    prefix_rules: &SecondaryMap<RuleHandle, HashMap<RuleHandle, Span>>,
    visited: &mut EntitySet<RuleHandle>,
    stack: &mut Vec<(RuleHandle, Span)>,

    grammar: &Grammar,
    err: &ErrorAccumulator,
) {
    if let Some((_, span)) = stack.iter().find(|(rule, _)| *rule == handle) {
        //      /pos
        // A -> B -> C -> D
        //      ↑________|
        err.error(*span, "Detected left recursion");
        return;
    }

    if visited.insert(handle) {
        return;
    }

    stack.push((handle, span));
    for (&handle, &span) in &prefix_rules[handle] {
        find_prefix_cycles(handle, span, prefix_rules, visited, stack, grammar, err);
    }
    stack.pop();
}
