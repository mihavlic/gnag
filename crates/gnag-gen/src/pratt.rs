use crate::convert::RuleExpr;

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
        | RuleExpr::Not(_) => {
            unreachable!("These should have been eliminated during lowering")
        }
        RuleExpr::Commit | RuleExpr::Pratt(_) => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Associativity {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PrattExprKind {
    /// '(' Expr ')'
    Atom,
    /// '!' Expr
    Prefix,
    /// Expr '!'
    Suffix,
    /// Expr '+' Expr
    Binary(Associativity),
}

impl PrattExprKind {
    pub fn get_binding_power(self, offset: &mut u32) -> (Option<u32>, Option<u32>) {
        let start = *offset;
        match self {
            PrattExprKind::Atom => (None, None),
            PrattExprKind::Prefix => {
                *offset += 1;
                (None, Some(start))
            }
            PrattExprKind::Suffix => {
                *offset += 1;
                (Some(start), None)
            }
            PrattExprKind::Binary(associativity) => {
                *offset += 2;
                let (l, r) = match associativity {
                    Associativity::Left => (1, 0),
                    Associativity::Right => (0, 1),
                };
                (Some(start + l), Some(start + r))
            }
        }
    }
}
