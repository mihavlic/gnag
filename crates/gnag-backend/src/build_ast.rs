use std::borrow::Borrow;

use gnag_runtime::{
    trace::{PreorderTrace, TraceOffsetIterator, TraceVisitEvent},
    Language, NodeEvent, NodeKind,
};

use crate::{
    ast::{Ast, AstEvent, AstGroup, AstIndex, AstLeaf},
    error::ErrorAccumulator,
    span::{Span, Spanned},
};

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
        loop {
            let (offset, event, node) = self.inner.next()?;
            if node.kind.is_skip() {
                continue;
            }

            let span = Span {
                start: offset,
                end: self.inner.current_offset(),
            };

            return Some((event, node.kind, span));
        }
    }
}

pub struct CurrentChild {
    pub index: AstIndex,
    pub group_close: Option<AstIndex>,
}

pub struct CurrentGroup {
    current_children_start: usize,
    open: AstIndex,
}

struct AstVisitor {
    current_children: Vec<CurrentChild>,
    current_groups: Vec<CurrentGroup>,
}

impl AstVisitor {
    fn new() -> Self {
        Self {
            current_children: Vec::new(),
            current_groups: Vec::new(),
        }
    }
    pub fn open_group(&mut self, open: AstIndex) {
        self.current_groups.push(CurrentGroup {
            current_children_start: self.current_children.len(),
            open,
        });
    }
    pub fn close_group(&mut self, close: AstIndex) {
        let group = self.current_groups.pop().unwrap();
        self.current_children.truncate(group.current_children_start);
        self.current_children.push(CurrentChild {
            index: group.open,
            group_close: Some(close),
        });
    }
    pub fn leaf(&mut self, leaf: AstIndex) {
        self.current_children.push(CurrentChild {
            index: leaf,
            group_close: None,
        });
    }
    pub fn current_children(&self) -> &[CurrentChild] {
        let group = self.current_groups.last().unwrap();
        &self.current_children[group.current_children_start..]
    }
}

pub struct AstBuilder {
    visitor: AstVisitor,
    ast: Ast,
}

impl AstBuilder {
    pub fn new() -> AstBuilder {
        Self {
            visitor: AstVisitor::new(),
            ast: Ast::new(),
        }
    }
    pub fn open_group(&mut self) {
        let open = self.ast.push(AstEvent::OpenGroup);
        self.visitor.open_group(open);
    }
    pub fn close_group(&mut self, group: Spanned<AstGroup>) {
        let close = self.ast.push(AstEvent::CloseGroup(group));
        self.visitor.close_group(close);
    }
    pub fn leaf(&mut self, leaf: Spanned<AstLeaf>) {
        let leaf = self.ast.push(AstEvent::Leaf(leaf));
        self.visitor.leaf(leaf);
    }
    pub fn current_children(&self) -> &[CurrentChild] {
        self.visitor.current_children()
    }
    pub fn nth_leaf(&self, n: usize) -> Option<&Spanned<AstLeaf>> {
        let children = self.visitor.current_children();
        let child = children.get(n)?;
        if let Some(AstEvent::Leaf(leaf)) = self.ast.get(child.index) {
            return Some(leaf);
        } else {
            return None;
        }
    }
}

pub struct ConvertCx<'a, 'b, 'c> {
    src: &'a str,
    language: &'b Language,
    err: &'c ErrorAccumulator,
    literal_scratch: Vec<u8>,
}

impl<'a, 'b, 'c> ConvertCx<'a, 'b, 'c> {
    pub fn extract_identifier(&mut self, span: Span) -> &str {
        span.as_str(self.src)
    }
    pub fn extract_literal(&mut self, span: Span) -> &[u8] {
        self.literal_scratch.clear();
        crate::literal::extract_literal(
            self.src.as_bytes(),
            span,
            &mut self.literal_scratch,
            self.err,
        );
        &self.literal_scratch
    }
}

impl Borrow<Language> for ConvertCx<'_, '_, '_> {
    fn borrow(&self) -> &Language {
        self.language
    }
}

impl Borrow<str> for ConvertCx<'_, '_, '_> {
    fn borrow(&self) -> &str {
        self.src
    }
}

fn build_ast(cst: &PreorderTrace, src: &str) {
    let mut stack = Vec::new();
    let iter = CstIter::new(cst, &mut stack);

    let mut ast = AstBuilder::new();

    for (event, kind, span) in iter {
        match event {
            TraceVisitEvent::Open => {
                ast.open_group();
            }
            TraceVisitEvent::Token => {
                if let Some(leaf) = convert_leaf(kind, span, src) {
                    ast.leaf(Spanned::new(leaf, span));
                }
            }
            TraceVisitEvent::Close => {
                let group = convert_group(kind, &mut ast);
                ast.close_group(Spanned::new(group, span));
            }
        }
    }
}

fn convert_leaf(kind: NodeKind, span: Span, cx: &mut ConvertCx) -> Option<AstLeaf> {
    use gnag_parser::kinds;

    match kind {
        kinds::Whitespace | kinds::Comment | kinds::Newline => None,

        kinds::String => {
            let extracted = cx.extract_literal(span);
            Some(AstLeaf::UnresolvedLiteral(extracted.into()))
        }
        kinds::Ident => {
            let extracted = cx.extract_identifier(span);
            Some(AstLeaf::UnresolvedIdent(extracted.into()))
        }
        kinds::InlineKeyword => todo!(),
        kinds::TokensKeywords => todo!(),
        kinds::RulesKeyword => todo!(),
        kinds::PrattKeyword => todo!(),
        kinds::GroupKeyword => todo!(),
        kinds::LCurly => todo!(),
        kinds::RCurly => todo!(),
        kinds::LParen => todo!(),
        kinds::RParen => todo!(),
        kinds::LBracket => todo!(),
        kinds::RBracket => todo!(),
        kinds::LAngle => todo!(),
        kinds::RAngle => todo!(),
        kinds::Question => todo!(),
        kinds::Pipe => todo!(),
        kinds::Star => todo!(),
        kinds::Plus => todo!(),
        kinds::At => todo!(),
        kinds::Colon => todo!(),
        kinds::Comma => todo!(),
        kinds::Dot => todo!(),
        kinds::Equals => todo!(),
        kinds::Error => todo!(),
        _ => panic!("Unexpected NodeKind"),
    }
}

fn convert_group(kind: NodeKind, ast: &mut AstBuilder) -> AstGroup {
    match kind {
        kinds::File => todo!(),
        kinds::TokensOrRules => todo!(),
        kinds::Attribute => todo!(),
        kinds::Parameters => todo!(),
        kinds::Rule => todo!(),
        kinds::Atom => todo!(),
        kinds::CallExpr => todo!(),
        kinds::ParenExpr => todo!(),
        kinds::PrattExpr => todo!(),
        kinds::PostExpr => todo!(),
        kinds::SeqExpr => todo!(),
        kinds::BinExpr => todo!(),
        kinds::Expr => todo!(),
        _ => panic!("Unexpected NodeKind"),
    }
}
