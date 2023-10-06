use crate::convert::{RuleHandle, TokenHandle};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PrattExprKind {
    Atom,
    Prefix,
    Postfix,
    Binary(Associativity),
}

impl PrattExprKind {
    pub fn get_binding_power(self, order: u32) -> (Option<u32>, Option<u32>) {
        assert!(order != 0);
        let base = order * 2 - 1;
        match self {
            PrattExprKind::Atom => (None, None),
            PrattExprKind::Prefix => (None, Some(base)),
            PrattExprKind::Postfix => (Some(base), None),
            PrattExprKind::Binary(associativity) => {
                let (l, r) = match associativity {
                    Associativity::Left => (1, 0),
                    Associativity::Right => (0, 1),
                };
                (Some(base + l), Some(base + r))
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Associativity {
    Left,
    Right,
}

#[derive(Clone, Debug)]
pub enum PrattExpr {
    Token(TokenHandle),
    Rule(RuleHandle),
}

#[derive(Clone, Debug)]
pub struct PrattChild {
    pub expr: PrattExpr,
    pub kind: PrattExprKind,
    pub order: u32,
}
