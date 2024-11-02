use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition},
    error::ErrorAccumulator,
    span::Span,
};

use super::{builtin::lower_builtin, grammar::Grammar};

pub struct LowerCx<'a> {
    pub err: &'a ErrorAccumulator,
}

impl<'a> LowerCx<'a> {
    pub fn new(err: &'a ErrorAccumulator) -> LowerCx<'a> {
        Self { err }
    }
}

pub fn lower(grammar: &mut Grammar, cx: &LowerCx) {
    for (_, rule) in grammar.rules.iter_mut() {
        rule.pattern.visit_mut(|pattern| {
            lower_pattern(pattern, cx);
        });
    }
}

pub enum LoweredKind {
    Transition(Transition),
    Sequence,
    Choice,
    Maybe { expect: bool },
    Loop,
}

pub struct LoweredNode {
    kind: LoweredKind,
    span: Span,
    children: Vec<LoweredNode>,
}

pub struct PatternProperties {
    maybe_advances: bool,
    always_advances: bool,
}

pub fn lower_pattern(pattern: &mut Pattern, cx: &LowerCx) {
    match pattern.kind() {
        PatternKind::Group(group) => match *group {
            Group::Sequence { explicit: _ } => {
                inline_some_children(pattern, &Group::Sequence { explicit: true })
            }
            Group::Choice => {
                inline_some_children(pattern, &Group::Choice);
            }
            Group::OneOrMore => {
                let child = pattern.children_mut()[0].take();

                let repeat = Group::Loop.to_pattern(vec![child.clone()], pattern.span());
                let sequence = Group::Sequence { explicit: false }
                    .to_pattern(vec![child, repeat], pattern.span());

                *pattern = sequence;
            }
            Group::Maybe => {
                let children = pattern.children_vec_mut();
                debug_assert_eq!(children.len(), 1);
                match children[0].kind() {
                    PatternKind::Group(Group::Maybe | Group::Loop) => {
                        *pattern = children.pop().unwrap();
                    }
                    _ => {}
                }
            }
            Group::InlineCall { ref name } => {
                *pattern = lower_builtin(pattern, &name.clone(), cx);
            }
            Group::Loop => {}
        },
        PatternKind::Pratt(_)
        | PatternKind::Transition(_)
        | PatternKind::Commit
        | PatternKind::UnresolvedIdent(_)
        | PatternKind::UnresolvedLiteral(_)
        | PatternKind::InlineParameter(_) => {}
    }
}

fn inline_some_children(pattern: &mut Pattern, group: &Group) {
    let children = pattern.children_vec_mut();
    if children.len() == 1 {
        *pattern = children[0].clone();
    } else {
        let mut merge = false;
        for child in children.iter() {
            if let PatternKind::Group(g) = child.kind() {
                if g == group {
                    merge = true;
                    break;
                }
            }
        }

        if merge {
            let mut new_children = Vec::new();
            for mut child in children.drain(..) {
                if let PatternKind::Group(g) = child.kind() {
                    if g == group {
                        new_children.append(child.children_vec_mut());
                        continue;
                    }
                }

                new_children.push(child)
            }

            *children = new_children;
        }
    }
}
