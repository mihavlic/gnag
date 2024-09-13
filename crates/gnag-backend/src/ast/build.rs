use std::{cell::RefCell, ops::Deref, rc::Rc};

use gnag_parser::kinds;
use gnag_runtime::{
    trace::{PreorderTrace, TraceOffsetIterator, TraceVisitEvent},
    NodeEvent, NodeKind,
};

use crate::{
    ast::{
        pattern::{Group, Pattern, PatternKind},
        ItemGroupKind, Rule, RuleBody,
    },
    error::ErrorAccumulator,
    span::Span,
};

use super::{File, Ident, Literal, Pratt, RuleGroup};

struct CstIter<'a, 'b> {
    inner: TraceOffsetIterator<'a, 'b>,
}

impl<'a, 'b> CstIter<'a, 'b> {
    fn new(cst: &'a PreorderTrace, stack: &'b mut Vec<(NodeEvent, u32)>) -> CstIter<'a, 'b> {
        Self {
            inner: cst.iter_offsets(stack),
        }
    }
}

impl<'a, 'b> Iterator for CstIter<'a, 'b> {
    type Item = (TraceVisitEvent, NodeKind, Span);

    fn next(&mut self) -> Option<Self::Item> {
        let (offset, event, node) = self.inner.next()?;
        let span = Span::new(offset, self.inner.current_offset());
        Some((event, node.kind, span))
    }
}

pub struct ConvertCx<'a, 'b> {
    src: &'a str,
    literal_scratch: RefCell<Vec<u8>>,
    err: &'b ErrorAccumulator,
}

impl<'a, 'b> ConvertCx<'a, 'b> {
    pub fn new(src: &'a str, err: &'b ErrorAccumulator) -> ConvertCx<'a, 'b> {
        Self {
            src,
            literal_scratch: RefCell::default(),
            err,
        }
    }
    pub fn identifier(&self, span: Span) -> Ident {
        Ident {
            span,
            value: self.raw_identifier(span).into(),
        }
    }
    pub fn literal(&self, span: Span) -> Literal {
        Literal {
            span,
            value: self.raw_literal(span).deref().as_slice().into(),
        }
    }
    pub fn raw_identifier(&self, span: Span) -> &str {
        span.as_str(self.src)
    }
    pub fn raw_literal(&self, span: Span) -> std::cell::RefMut<Vec<u8>> {
        let mut scratch = self.literal_scratch.borrow_mut();
        scratch.clear();

        let bytes = self.src.as_bytes();
        super::literal::extract_literal(span.as_bytes(bytes), span, &mut *scratch, self.err);

        scratch
    }
}

pub fn build(cst: &PreorderTrace, cx: &ConvertCx) -> Option<File> {
    let mut stack = Vec::new();
    let mut iter = CstIter::new(cst, &mut stack);

    file(&mut iter, cx)
}

fn file(iter: &mut CstIter, cx: &ConvertCx) -> Option<File> {
    let mut groups = Vec::new();

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return Some(File { span, groups });
        }

        match node {
            kinds::RuleGroup => {
                groups.extend(rule_group(iter, cx));
            }
            _ => {}
        }
    }

    None
}

fn rule_group(iter: &mut CstIter, cx: &ConvertCx) -> Option<RuleGroup> {
    let mut rules = Vec::new();
    let mut kind = None;

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return Some(RuleGroup {
                span,
                kind: kind?,
                items: rules,
            });
        }

        match node {
            kinds::LexerKeyword => kind = Some(ItemGroupKind::Lexer),
            kinds::ParserKeyword => kind = Some(ItemGroupKind::Parser),
            kinds::Rule => rules.extend(rule(iter, cx).map(Rc::new)),
            _ => {}
        }
    }

    panic!("Expected scope end")
}

fn attribute(iter: &mut CstIter, cx: &ConvertCx) -> Option<Ident> {
    let mut ident = None;

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return ident.map(|span| cx.identifier(span));
        }

        match node {
            kinds::Ident => ident = Some(span),
            _ => {}
        }
    }

    panic!("Expected scope end")
}

fn parameters(iter: &mut CstIter, cx: &ConvertCx) -> Vec<Ident> {
    let mut parameters = Vec::new();

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return parameters;
        }

        match node {
            kinds::Ident => parameters.push(cx.identifier(span)),
            _ => {}
        }
    }

    panic!("Expected scope end")
}

fn pratt_group(iter: &mut CstIter, cx: &ConvertCx) -> Option<Pratt> {
    let mut rules = Vec::new();

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return Some(Pratt { span, rules });
        }

        match node {
            kinds::Rule => rules.extend(rule(iter, cx).map(Rc::new)),
            _ => {}
        }
    }

    panic!("Expected scope end")
}

fn rule(iter: &mut CstIter, cx: &ConvertCx) -> Option<Rule> {
    let mut name = None;
    let mut attributes = Vec::new();
    let mut parameters = None;
    let mut body = None;

    while let Some((event, node, span)) = iter.next() {
        if event == TraceVisitEvent::Close {
            return Some(Rule {
                span,
                name: name.map(|span| cx.identifier(span))?,
                attributes,
                parameters,
                body: body?,
            });
        }

        match node {
            kinds::PrattExpr => {
                body = pratt_group(iter, cx).map(RuleBody::Pratt);
            }
            kinds::Atom
            | kinds::CallExpr
            | kinds::ParenExpr
            | kinds::PostExpr
            | kinds::SequenceExpr
            | kinds::ChoiceExpr => {
                body = expression(iter, cx, node).map(RuleBody::Pattern);
            }
            kinds::Attribute => attributes.extend(attribute(iter, cx)),
            kinds::Parameters => parameters = Some(self::parameters(iter, cx)),
            kinds::Ident => name = Some(span),
            _ => {}
        }
    }

    panic!("Expected scope end")
}

fn expression(iter: &mut CstIter, cx: &ConvertCx, kinda: NodeKind) -> Option<Pattern> {
    fn implicit_sequence_children(expr: Pattern) -> Vec<Pattern> {
        match expr.kind() {
            PatternKind::Group(Group::Sequence { explicit: false }) => expr.into_children(),
            _ => vec![expr],
        }
    }

    match kinda {
        kinds::Atom => {
            let mut expr = None;
            while let Some((event, node, span)) = iter.next() {
                if event == TraceVisitEvent::Close {
                    return expr;
                }

                match node {
                    kinds::Ident => {
                        let value = cx.identifier(span).value;
                        expr = Some(PatternKind::UnresolvedIdent(value).to_pattern(span));
                    }
                    kinds::String => {
                        let value = cx.literal(span).value;
                        expr = Some(PatternKind::UnresolvedLiteral(value).to_pattern(span));
                    }
                    _ => {}
                }
            }
        }
        kinds::ParenExpr => {
            let mut expr = None;

            while let Some((event, kind, span)) = iter.next() {
                // ( A B C ) becomes
                //
                // ParenExpr
                //   SequenceExpr
                //     A
                //     B
                //     C
                //
                // we want to convert this to a single sequence

                if event == TraceVisitEvent::Close {
                    let children = implicit_sequence_children(expr?);
                    return Some(Group::Sequence { explicit: true }.to_pattern(children, span));
                }

                match kind {
                    kinds::Atom
                    | kinds::CallExpr
                    | kinds::ParenExpr
                    | kinds::PrattExpr
                    | kinds::PostExpr
                    | kinds::SequenceExpr
                    | kinds::ChoiceExpr => {
                        expr = expression(iter, cx, kind);
                    }
                    _ => {}
                }
            }
        }
        kinds::CallExpr => {
            let mut name = None;
            let mut expr = None;

            while let Some((event, kind, span)) = iter.next() {
                if event == TraceVisitEvent::Close {
                    let children = expr.map(implicit_sequence_children).unwrap_or_default();
                    return Some(
                        Group::InlineCall {
                            name: cx.identifier(name?),
                        }
                        .to_pattern(children, span),
                    );
                }

                match kind {
                    kinds::Ident => name = Some(span),
                    kinds::Atom
                    | kinds::CallExpr
                    | kinds::ParenExpr
                    | kinds::PrattExpr
                    | kinds::PostExpr
                    | kinds::SequenceExpr
                    | kinds::ChoiceExpr => {
                        expr = expression(iter, cx, kind);
                    }
                    _ => {}
                }
            }
        }
        kinds::PostExpr => {
            let mut group = None;
            let mut expr = None;

            while let Some((event, kind, span)) = iter.next() {
                if event == TraceVisitEvent::Close {
                    let expr = expr.unwrap_or_else(|| Pattern::empty(span));
                    return group.map(|group: Group| group.to_pattern(vec![expr], span));
                }

                match kind {
                    kinds::Question => group = Some(Group::Maybe),
                    kinds::Star => group = Some(Group::Loop),
                    kinds::Plus => group = Some(Group::OneOrMore),
                    kinds::Atom
                    | kinds::CallExpr
                    | kinds::ParenExpr
                    | kinds::PrattExpr
                    | kinds::PostExpr
                    | kinds::SequenceExpr
                    | kinds::ChoiceExpr => {
                        expr = expression(iter, cx, kind);
                    }
                    _ => {}
                }
            }
        }
        kinds::ChoiceExpr | kinds::SequenceExpr => {
            let mut children = Vec::new();

            while let Some((event, kind, span)) = iter.next() {
                if event == TraceVisitEvent::Close {
                    let group = match kinda {
                        kinds::ChoiceExpr => Group::Choice,
                        kinds::SequenceExpr => Group::Sequence { explicit: false },
                        _ => unreachable!(),
                    };
                    return Some(group.to_pattern(children, span));
                }

                match kind {
                    kinds::Atom
                    | kinds::CallExpr
                    | kinds::ParenExpr
                    | kinds::PrattExpr
                    | kinds::PostExpr
                    | kinds::SequenceExpr
                    | kinds::ChoiceExpr => {
                        children.extend(expression(iter, cx, kind));
                    }
                    _ => {}
                }
            }
        }
        kinds::PrattExpr => {
            let mut keyword = None;

            while let Some((event, kind, span)) = iter.next() {
                if event == TraceVisitEvent::Close {
                    let keyword = keyword.unwrap_or(span);
                    cx.err
                        .error_static(keyword, "Pratt expression cannot be nested");
                    return Some(Pattern::error(span));
                }

                match kind {
                    kinds::PrattKeyword => keyword = Some(span),
                    _ => {}
                }
            }
        }
        _ => return None,
    }

    panic!("Expected scope end")
}
