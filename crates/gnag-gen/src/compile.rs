use std::collections::HashSet;

use gnag::{
    ctx::ConvertCtx,
    file::{ConvertedFile, RuleExpr, RuleHandle, TokenAttribute, TokenHandle},
    handle::{HandleVec, SecondaryVec},
    SpannedError, StrSpan,
};

use crate::{
    pratt::{Associativity, PrattChild, PrattExpr, PrattExprKind},
    LoweredFile,
};

pub enum CompiledTokenKind {
    Skip,
    ErrorToken,
    Normal,
}

fn decide_pratt_expr(
    pratt_rule: RuleHandle,
    associativity: Associativity,
    expr: &RuleExpr,
) -> Option<PrattExprKind> {
    let is_pratt_parent = |rule: &RuleExpr| match rule {
        RuleExpr::Rule(rule) => *rule == pratt_rule,
        _ => false,
    };

    match expr {
        RuleExpr::Sequence(seq) => match seq.as_slice() {
            [] => None,
            [_] => unreachable!("One-sized sequence should have been converted into inner nodes."),
            // // TODO should probably result in an error
            // [a] if is_pratt_parent(a) => None,
            [a, .., b] => {
                let a = is_pratt_parent(a);
                let b = is_pratt_parent(b);

                let kind = match (a, b) {
                    // the case where `seq.len() == 2` ie. the operator is `()` has special handling
                    (true, true) => PrattExprKind::Binary(associativity),
                    (false, true) => PrattExprKind::Prefix,
                    (true, false) => PrattExprKind::Postfix,
                    (false, false) => PrattExprKind::Atom,
                };

                Some(kind)
            }
        },
        RuleExpr::InlineParameter(_) => unreachable!(),
        RuleExpr::InlineCall(_) => unreachable!(),
        RuleExpr::ZeroSpace | RuleExpr::Empty => None,
        RuleExpr::Error => None,
        RuleExpr::Token(_)
        | RuleExpr::Rule(_)
        | RuleExpr::Choice(_)
        | RuleExpr::ZeroOrMore(_)
        | RuleExpr::OneOrMore(_)
        | RuleExpr::Maybe(_)
        | RuleExpr::Any
        | RuleExpr::Not(_)
        | RuleExpr::SeparatedList { .. }
        | RuleExpr::PrattRecursion { .. } => Some(PrattExprKind::Atom),
    }
}

#[derive(Clone)]
pub enum CompiledRule {
    Unchanged,
    PrattChild(RuleExpr),
    Pratt(Vec<PrattChild>),
}

impl CompiledRule {
    fn or_insert_expr(&mut self, expr: &RuleExpr) -> &mut RuleExpr {
        match self {
            CompiledRule::Unchanged => *self = CompiledRule::PrattChild(expr.clone()),
            CompiledRule::PrattChild(_) => {}
            CompiledRule::Pratt(_) => panic!(),
        }
        match self {
            CompiledRule::PrattChild(a) => return a,
            _ => unreachable!(),
        }
    }
    fn insert_pratt(&mut self, children: Vec<PrattChild>) {
        match self {
            CompiledRule::Unchanged => *self = CompiledRule::Pratt(children),
            CompiledRule::PrattChild(_) => panic!(),
            CompiledRule::Pratt(_) => panic!(),
        }
    }
}

pub struct CompiledFile {
    pub error_token: Option<TokenHandle>,
    // pub root_rule: Option<RuleHandle>,
    pub rules: SecondaryVec<RuleHandle, RuleExpr>,
    pub errors: Vec<SpannedError>,
}

impl CompiledFile {
    pub fn new(src: &str, converted: &ConvertedFile, lowered: &LoweredFile) -> CompiledFile {
        let cx = ConvertCtx::new(src);

        let mut error_token = None;
        for (handle, token) in converted.tokens.iter_kv() {
            if let Some(TokenAttribute::ErrorToken(span)) = token.attribute {
                match error_token {
                    Some(_) => cx.error(span, "Only one error token may exist"),
                    None => error_token = Some(handle),
                }
            }
        }

        let end = StrSpan::at(src.len().try_into().unwrap());
        if error_token.is_none() {
            cx.error(end, "No error token defined")
        }

        let mut compiled = converted.rules.map_fill(CompiledRule::Unchanged);
        for (k, v) in converted.rules.iter_kv() {
            if v.attributes.pratt {
                let rules = convert_to_pratt(lowered, k, converted, &mut compiled, &cx);
                compiled[k].insert_pratt(rules);
            }
        }

        let mut hashset = HashSet::new();
        let prefix_children = lowered.rules.map_ref_with_key(|handle, expr| {
            let expr = match &compiled[handle] {
                CompiledRule::Unchanged | CompiledRule::Pratt(_) => expr,
                CompiledRule::PrattChild(a) => a,
            };

            expr.visit_prefix_leaves(|leaf| {
                if let RuleExpr::Rule(handle) = leaf {
                    hashset.insert(*handle);
                }
                false
            });
            hashset.drain().collect::<Vec<_>>()
        });

        let mut data = SecondaryVec::new_preallocated(&lowered.rules);
        let mut visited = lowered.rules.map_fill(false);
        let mut stack = Vec::new();
        for handle in lowered.rules.iter_keys() {
            find_prefix_cycles(
                handle,
                &prefix_children,
                &mut data,
                &mut visited,
                &mut stack,
            );
            debug_assert!(stack.is_empty());
        }

        for (handle, data) in data.iter_kv_mut() {
            data.sort();
            data.dedup();

            let ast = converted.get_rule_ast(handle);

            for &mut child in data {
                let child = &converted.rules[child];
                cx.error(
                    ast.span,
                    format_args!("Rule is left-recursive through {}", child.name),
                );
            }
        }

        CompiledFile {
            error_token,
            rules: SecondaryVec::new(),
            errors: cx.finish(),
        }
    }
}

fn convert_to_pratt(
    lowered: &LoweredFile,
    k: RuleHandle,
    converted: &ConvertedFile,
    compiled: &mut HandleVec<RuleHandle, CompiledRule>,
    cx: &ConvertCtx<'_>,
) -> Vec<PrattChild> {
    let mut order = 1;
    let mut rules = Vec::new();
    for expr in lowered.rules[k].get_choice_slice() {
        let (kind, child) = match expr {
            &RuleExpr::Token(token) => (PrattExprKind::Atom, PrattExpr::Token(token)),
            &RuleExpr::Rule(rule) => {
                let expr = &lowered.rules[rule];
                let def = &converted.rules[rule];
                let associativity = match def.attributes.right_assoc {
                    true => Associativity::Right,
                    // left associativity by default
                    false => Associativity::Left,
                };
                match decide_pratt_expr(k, associativity, expr) {
                    Some(kind) => {
                        // change regular RuleExpr::Rule to RuleExpr::PrattRecursion
                        if let PrattExprKind::Binary(_)
                        | PrattExprKind::Prefix
                        | PrattExprKind::Postfix = kind
                        {
                            let compiled_expr = compiled[rule].or_insert_expr(expr);

                            let RuleExpr::Sequence(seq) = compiled_expr else {
                                unreachable!()
                            };

                            let (l_bp, r_bp) = kind.get_binding_power(order);

                            if let PrattExprKind::Binary(_) | PrattExprKind::Postfix = kind {
                                let first = seq.first_mut().unwrap();
                                assert!(matches!(first, RuleExpr::Rule(_)));
                                *first = RuleExpr::PrattRecursion {
                                    pratt: k,
                                    binding_power: l_bp.unwrap(),
                                };
                            }
                            if let PrattExprKind::Binary(_) | PrattExprKind::Prefix = kind {
                                let last = seq.last_mut().unwrap();
                                assert!(matches!(last, RuleExpr::Rule(_)));
                                *last = RuleExpr::PrattRecursion {
                                    pratt: k,
                                    binding_power: r_bp.unwrap(),
                                };
                            }
                        }

                        (kind, PrattExpr::Rule(rule))
                    }
                    None => {
                        let ast = converted.get_rule_ast(rule);
                        cx.error(ast.span, "Failed to convert pattern to pratt form");
                        continue;
                    }
                }
            }
            _ => {
                let ast = converted.get_rule_ast(k);
                cx.error(
                    ast.span,
                    "Pratt expression can only contain Tokens or Rules",
                );
                continue;
            }
        };

        rules.push(PrattChild {
            expr: child,
            kind,
            order,
        });
        order += 1;
    }
    rules
}

fn find_prefix_cycles(
    handle: RuleHandle,
    prefix_children: &HandleVec<RuleHandle, Vec<RuleHandle>>,
    data: &mut SecondaryVec<RuleHandle, Vec<RuleHandle>>,
    visited: &mut HandleVec<RuleHandle, bool>,
    stack: &mut Vec<RuleHandle>,
) {
    if let Some(pos) = stack.iter().position(|rule| *rule == handle) {
        let mut parent = stack.last().copied().unwrap();
        //      /pos
        // A -> B -> C -> D
        //      ↑_________|
        for &child in &stack[pos..] {
            data.entry(parent).get_or_insert(Vec::new()).push(child);
            parent = child;
        }
        return;
    }

    if visited[handle] {
        return;
    }
    visited[handle] = true;

    stack.push(handle);
    for &prefix in &prefix_children[handle] {
        find_prefix_cycles(prefix, prefix_children, data, visited, stack);
    }
    stack.pop();
}
