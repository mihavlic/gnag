use std::{
    borrow::Borrow,
    collections::{hash_map::Entry, HashMap},
};

use crate::{
    convert::{ConvertedFile, HandleKind, InlineHandle, ItemKind, RuleBody, RuleHandle},
    expr::{CallExpr, RuleExpr, Transition},
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
                if let RuleExpr::Transition(Transition::Bytes(bytes)) = &rule.body.expr {
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
            RuleExpr::UnresolvedIdentifier { name, name_span } => {
                *node = lower_reference(&**name, *name_span, self);
            }
            _ => (),
        });
        self.stack.pop();

        self.inlined_inlines.entry(handle).insert(expr)
    }

    fn get_handle_by_name(
        &self,
        name: &str,
        name_span: StrSpan,
        kind: Option<HandleKind>,
    ) -> Option<ItemKind> {
        let handle = self.name_to_item.get(name).cloned();
        match handle {
            Some(_) if kind.is_none() => handle,
            Some(ItemKind::Inline(_)) if kind == Some(HandleKind::Inline) => handle,
            Some(ItemKind::Rule(_)) if kind == Some(HandleKind::Rule) => handle,
            Some(_) => {
                self.error(
                    name_span,
                    format_args!("Expected {} rule", kind.unwrap().name()),
                );
                None
            }
            None => {
                self.error(name_span, "Unknown item");
                None
            }
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

    let handle = match cx.get_handle_by_name(name, name_span, Some(HandleKind::Inline)) {
        Some(ItemKind::Inline(handle)) => handle,
        _ => return RuleExpr::error(),
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
        | RuleExpr::Not(_) => {
            unreachable!("These should have been eliminated during lowering")
        }
        RuleExpr::Commit | RuleExpr::Pratt(_) => None,
    }
}

fn lower_pratt(
    parent: Option<RuleHandle>,
    children: &[RuleHandle],
    lowered_rules: &HandleVec<RuleHandle, RuleExpr>,
    cx: &mut LoweringCx,
) -> RuleExpr {
    let parent = parent.filter(|handle| {
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
    match cx.get_handle_by_name(name, name_span, None) {
        Some(ItemKind::Rule(a)) => RuleExpr::rule(a),
        Some(ItemKind::Inline(_)) => {
            cx.error(name_span, "Use <> syntax for inlines");
            RuleExpr::error()
        }
        None => RuleExpr::error(),
    }
}

fn lower_expr(
    parent: Option<RuleHandle>,
    expr: &mut RuleExpr,
    lowered_rules: &HandleVec<RuleHandle, RuleExpr>,
    cx: &mut LoweringCx,
) {
    expr.visit_nodes_bottom_up_mut(|node| match node {
        RuleExpr::Pratt(vec) => *node = lower_pratt(parent, vec, lowered_rules, cx),
        RuleExpr::InlineCall(call) => *node = lower_call(call, cx),
        // it is currently corrent to resolve references in the same traversal as other lowering
        // because we're going bottom-up
        // the only lowering which touches other rules is pratt where children are inserted before their parents before conversion
        RuleExpr::UnresolvedIdentifier { name, name_span } => {
            *node = lower_reference(&**name, *name_span, cx);
        }
        RuleExpr::Transition(Transition::Bytes(bytes)) => {
            if let Some(handle) = parent {
                let converted = &cx.file.rules[handle];
                if converted.kind == RuleKind::Rules {
                    *node = match cx.literal_to_token.get(&**bytes) {
                        Some(a) => RuleExpr::rule(*a),
                        None => {
                            cx.error(StrSpan::empty(), "(TODO span) No matching token");
                            RuleExpr::error()
                        }
                    }
                }
            }
        }
        RuleExpr::Not(expr) => {
            if let RuleExpr::Transition(Transition::Rule(handle)) = **expr {
                *node = RuleExpr::Transition(Transition::Not(handle));
            } else {
                cx.error(
                    StrSpan::empty(),
                    "(TODO span) RuleExpr::Not only works with tokens",
                );
                *node = RuleExpr::error();
            }
        }
        RuleExpr::OneOrMore(expr) => {
            let expr = expr.take();
            *node = RuleExpr::Sequence(vec![expr.clone(), RuleExpr::Loop(Box::new(expr))]);
        }
        _ => (),
    });
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
            lower_expr(Some(handle), &mut expr, &mut rules, &mut cx);
            _ = std::mem::replace(&mut rules[handle], expr);
        }

        LoweredFile { rules }
    }
}
