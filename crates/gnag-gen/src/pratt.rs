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
