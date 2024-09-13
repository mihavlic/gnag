use crate::ast::pattern::{ComparisonKind, Group, Pattern, PatternKind, Transition};

use super::{
    grammar::{Grammar, RuleHandle},
    lower::LowerCx,
};

pub fn visit_prefix_leaves(
    pattern: &mut Pattern,
    cx: &LowerCx,
    on_leaf: &mut dyn FnMut(&mut Pattern) -> bool,
) -> Option<bool> {
    match pattern.kind() {
        PatternKind::Transition(_) => Some(on_leaf(pattern)),
        PatternKind::Group(g) => match g {
            Group::Sequence { explicit: _ } => {
                let vec = pattern.children_mut();
                vec.first_mut()
                    .and_then(|e| visit_prefix_leaves(e, cx, on_leaf))
            }
            Group::Choice => {
                let mut contains_true = false;
                let mut contains_false = false;

                let vec = pattern.children_mut();
                for expr in vec {
                    match visit_prefix_leaves(expr, cx, on_leaf) {
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
            Group::Loop | Group::Maybe => {
                let g = g.clone();
                let span = pattern.span();
                let vec = pattern.children_mut();
                let expr = vec.first_mut().unwrap();

                match visit_prefix_leaves(expr, cx, on_leaf) {
                    Some(false) => Some(false),
                    Some(true) => {
                        cx.err
                            .error(span, format!("{g:?} pattern contains left recursion"));
                        pattern.set_kind(Transition::Error.to_kind());
                        Some(false)
                    }
                    None => None,
                }
            }
            Group::OneOrMore | Group::InlineCall { .. } => unreachable!("Should have been lowered"),
        },
        PatternKind::UnresolvedIdent(_)
        | PatternKind::UnresolvedLiteral(_)
        | PatternKind::InlineParameter(_) => unreachable!("Should have been lowered"),
        PatternKind::Pratt(_) | PatternKind::Commit => None,
    }
}

pub(crate) fn create_pratt(
    pratt: RuleHandle,
    children: &[RuleHandle],
    grammar: &Grammar,
    cx: &LowerCx,
) -> Pattern {
    let mut atoms = Vec::new();
    let mut suffixes = Vec::new();
    let mut precedence = 1;

    for &handle in children.iter().rev() {
        let rule = grammar.get_rule(handle).unwrap();
        let mut pattern = rule.pattern.clone();

        let has_prefix = visit_prefix_leaves(&mut pattern, cx, &mut |expr| {
            if let PatternKind::Transition(Transition::Rule(handle)) = expr.kind() {
                if *handle == pratt {
                    let comparison = match rule.attributes.right_assoc {
                        true => ComparisonKind::LowerEqual,
                        false => ComparisonKind::Lower,
                    };
                    let transition = Transition::CompareBindingPower(comparison, precedence);
                    expr.set_kind(transition.to_kind());
                    return true;
                }
            }
            false
        });

        let is_left_recursive = has_prefix == Some(true);

        let span = pattern.span();
        pattern
            .to_sequence(true)
            .push(Transition::CloseSpan(handle).to_pattern(span));

        if is_left_recursive {
            suffixes.push(pattern);
            precedence += 1;
        } else {
            atoms.push(pattern);
        }
    }

    let span = grammar.get_rule(pratt).unwrap().pattern.span();

    let finished = if suffixes.is_empty() {
        Group::Choice.to_pattern(atoms, span)
    } else {
        Group::Sequence { explicit: true }.to_pattern(
            vec![
                Group::Choice.to_pattern(atoms, span),
                Group::Loop.to_pattern(vec![Group::Choice.to_pattern(suffixes, span)], span),
            ],
            span,
        )
    };

    finished
}
