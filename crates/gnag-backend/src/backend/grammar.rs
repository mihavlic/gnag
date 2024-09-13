use std::rc::Rc;

use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};

use crate::{
    ast::{
        self,
        pattern::{Pattern, PatternKind},
        Ast, ItemGroupKind, RcString,
    },
    error::ErrorAccumulator,
};

use super::{
    lexer::create_lexer_expr,
    lower::{self, LowerCx},
    pratt,
    resolve::{self, ResolveCx},
    Attributes, LexerKind, Rule, RuleKind,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RuleHandle(u32);

entity_impl! { RuleHandle }

impl RuleHandle {
    pub fn name(self, cx: &Grammar) -> &RcString {
        &cx.get_rule(self).unwrap().name
    }
}

pub struct Grammar {
    pub rules: PrimaryMap<RuleHandle, Rule>,
    pub ast: SecondaryMap<RuleHandle, Option<Rc<ast::Rule>>>,
}

impl Grammar {
    pub fn new(ast: &Ast, err: &ErrorAccumulator) -> Grammar {
        let mut this = Grammar {
            rules: PrimaryMap::new(),
            ast: SecondaryMap::new(),
        };

        if let Some(file) = &ast.file {
            for group in &file.groups {
                let kind = match group.kind {
                    ItemGroupKind::Lexer => RuleKind::lexer(),
                    ItemGroupKind::Parser => RuleKind::parser(),
                };
                this.add_group(kind, &group.items, err);
            }
        }

        this
    }
    fn add_group(
        &mut self,
        kind: RuleKind,
        rules: &[Rc<ast::Rule>],
        err: &ErrorAccumulator,
    ) -> Vec<RuleHandle> {
        rules
            .iter()
            .map(|item| {
                return self.add_rule(item, kind, err);
            })
            .collect()
    }
    fn add_rule(
        &mut self,
        item: &Rc<ast::Rule>,
        kind: RuleKind,
        err: &ErrorAccumulator,
    ) -> RuleHandle {
        let kind = match item.parameters.is_some() {
            true => RuleKind::Template,
            _ => kind,
        };

        let body = match &item.body {
            ast::RuleBody::Pattern(p) => p.clone(),
            ast::RuleBody::Pratt(pratt) => {
                let children = self.add_group(kind, &pratt.rules, err);
                PatternKind::Pratt(children.into()).to_pattern(item.span)
            }
        };

        let handle = {
            let rule = Rule {
                name: item.name.value.clone(),
                kind,
                attributes: Attributes::from_ast(kind, &item.attributes, err),
                pattern: body,
            };
            let handle = self.rules.push(rule);
            self.ast[handle] = Some(item.clone());
            handle
        };

        handle
    }

    pub fn get_rule_mut(&mut self, handle: RuleHandle) -> Option<&mut Rule> {
        self.rules.get_mut(handle)
    }

    pub fn get_ast(&self, handle: RuleHandle) -> Option<&ast::Rule> {
        self.ast.get(handle)?.as_deref()
    }

    pub fn get_rule(&self, handle: RuleHandle) -> Option<&Rule> {
        self.rules.get(handle)
    }

    pub fn get_pattern(&self, handle: RuleHandle) -> Option<&Pattern> {
        self.rules.get(handle).map(|rule| &rule.pattern)
    }

    pub fn get_pattern_mut(&mut self, handle: RuleHandle) -> Option<&mut Pattern> {
        self.rules.get_mut(handle).map(|rule| &mut rule.pattern)
    }

    pub fn display_into(&self, buf: &mut dyn std::fmt::Write) -> std::fmt::Result {
        for (_, rule) in self.rules.iter() {
            write!(buf, "\n")?;
            write!(buf, "{} =\n", rule.name)?;
            rule.pattern.display_into_indent(buf, self, 1)?;
        }
        Ok(())
    }

    pub fn iter_keys(&self) -> Keys {
        Keys {
            inner: 0..(self.rules.len().try_into().unwrap()),
        }
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter {
            rules: self.rules.iter(),
            ast: self.ast.values(),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut {
            rules: self.rules.iter_mut(),
            ast: self.ast.values(),
        }
    }
}

pub struct Keys {
    inner: std::ops::Range<u32>,
}

impl Keys {
    pub fn next_with<'a, 'b>(
        &'a mut self,
        grammar: &'b Grammar,
    ) -> Option<(RuleHandle, &'b Rule, Option<&'b ast::Rule>)> {
        let handle = self.next()?;
        let rule = grammar.rules.get(handle).unwrap();
        let ast = match grammar.ast.get(handle) {
            Some(a) => a.as_ref().map(Rc::as_ref),
            None => None,
        };
        Some((handle, rule, ast))
    }
    pub fn next_with_mut<'a, 'b>(
        &'a mut self,
        grammar: &'b mut Grammar,
    ) -> Option<(RuleHandle, &'b mut Rule, Option<&'b ast::Rule>)> {
        let handle = self.next()?;
        let rule = grammar.rules.get_mut(handle).unwrap();
        let ast = match grammar.ast.get(handle) {
            Some(a) => a.as_ref().map(Rc::as_ref),
            None => None,
        };
        Some((handle, rule, ast))
    }
}

impl Iterator for Keys {
    type Item = RuleHandle;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(RuleHandle::from_u32)
    }
}

pub struct Iter<'a> {
    rules: cranelift_entity::Iter<'a, RuleHandle, Rule>,
    ast: std::slice::Iter<'a, Option<Rc<ast::Rule>>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = (RuleHandle, &'a Rule, Option<&'a ast::Rule>);

    fn next(&mut self) -> Option<Self::Item> {
        let (handle, rule) = self.rules.next()?;
        let ast = match self.ast.next() {
            Some(a) => a.as_ref().map(Rc::as_ref),
            None => None,
        };
        Some((handle, rule, ast))
    }
}

pub struct IterMut<'a> {
    rules: cranelift_entity::IterMut<'a, RuleHandle, Rule>,
    ast: std::slice::Iter<'a, Option<Rc<ast::Rule>>>,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = (RuleHandle, &'a mut Rule, Option<&'a ast::Rule>);

    fn next(&mut self) -> Option<Self::Item> {
        let (handle, rule) = self.rules.next()?;
        let ast = match self.ast.next() {
            Some(a) => a.as_ref().map(Rc::as_ref),
            None => None,
        };
        Some((handle, rule, ast))
    }
}

impl Grammar {
    pub fn resolve(&mut self, err: &ErrorAccumulator) {
        let cx = ResolveCx::new(self, err);
        resolve::resolve(self, &cx);
    }
    pub fn lower(&mut self, err: &ErrorAccumulator) {
        let cx = LowerCx::new(err);
        lower::lower(self, &cx);
    }
    pub fn create_lexer(&mut self, err: &ErrorAccumulator) {
        let cx = LowerCx::new(err);
        let mut pattern = create_lexer_expr(self, &cx);
        lower::lower_pattern(&mut pattern, &cx);

        self.rules.push(Rule {
            name: "Lexer".into(),
            kind: RuleKind::Lexer(LexerKind::Lexer),
            attributes: Attributes::default(),
            pattern,
        });
    }
    pub fn create_pratt_rules(&mut self, err: &ErrorAccumulator) {
        let cx = LowerCx::new(err);

        let mut keys = self.iter_keys();

        while let Some((handle, rule, _)) = keys.next_with(self) {
            if let PatternKind::Pratt(children) = rule.pattern.kind() {
                let mut pattern = pratt::create_pratt(handle, children, self, &cx);
                lower::lower_pattern(&mut pattern, &cx);

                for &child in Rc::clone(children).iter() {
                    let rule = self.get_rule_mut(child).unwrap();
                    rule.kind = RuleKind::Parser(super::ParserKind::PrattChild);
                }

                let rule = self.get_rule_mut(handle).unwrap();
                rule.pattern = pattern;
                rule.kind = RuleKind::Parser(super::ParserKind::Pratt);
            }
        }
    }
}
