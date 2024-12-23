use std::rc::Rc;

use cranelift_entity::{entity_impl, EntityRef, PrimaryMap, SecondaryMap};

use crate::{
    ast::{
        self,
        pattern::{Pattern, PatternKind, Transition},
        Ast, ItemGroupKind, RcString,
    },
    error::ErrorAccumulator,
};

use super::{
    lexer::create_lexer_expr,
    lower::{self, LowerCx, LoweredPattern},
    pratt,
    resolve::{self, ResolveCx},
    Attributes, LexerKind, ParserKind, Rule, RuleKind,
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
    pub resolved: SecondaryMap<RuleHandle, Option<Pattern>>,
    pub lowered: SecondaryMap<RuleHandle, Option<LoweredPattern>>,
}

impl Grammar {
    pub fn new(ast: &Ast, err: &ErrorAccumulator) -> Grammar {
        let mut this = Grammar {
            rules: PrimaryMap::new(),
            ast: SecondaryMap::new(),
            resolved: SecondaryMap::new(),
            lowered: SecondaryMap::new(),
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
            };
            let handle = self.rules.push(rule);
            self.ast[handle] = Some(item.clone());
            self.resolved[handle] = Some(body);
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
        self.resolved.get(handle)?.as_ref()
    }

    pub fn get_pattern_mut(&mut self, handle: RuleHandle) -> Option<&mut Pattern> {
        self.resolved[handle].as_mut()
    }

    pub fn get_lowered(&self, handle: RuleHandle) -> Option<&LoweredPattern> {
        self.lowered.get(handle)?.as_ref()
    }

    pub fn get_lowered_mut(&mut self, handle: RuleHandle) -> Option<&mut LoweredPattern> {
        self.lowered[handle].as_mut()
    }

    pub fn display_resolved(&self, buf: &mut dyn std::fmt::Write) -> std::fmt::Result {
        for (handle, rule) in self.rules.iter() {
            write!(buf, "\n")?;
            write!(buf, "{} =\n", rule.name)?;
            match self.get_pattern(handle) {
                Some(pattern) => pattern.display_into_indent(buf, self, 1)?,
                None => write!(buf, "((None))")?,
            }
        }
        Ok(())
    }

    pub fn iter_keys(&self) -> Keys {
        Keys {
            inner: 0..(self.rules.len().try_into().unwrap()),
        }
    }

    pub fn iter(&self) -> cranelift_entity::Iter<'_, RuleHandle, Rule> {
        self.rules.iter()
    }

    pub fn iter_mut(&mut self) -> cranelift_entity::IterMut<'_, RuleHandle, Rule> {
        self.rules.iter_mut()
    }

    pub fn iter_resolved(&self) -> SecondaryIter<'_, RuleHandle, Pattern> {
        todo!()
    }

    pub fn iter_resolved_mut(&mut self) -> SecondaryIterMut<'_, RuleHandle, Pattern> {
        todo!()
    }

    pub fn iter_lowered(&self) -> SecondaryIter<'_, RuleHandle, LoweredPattern> {
        todo!()
    }

    pub fn iter_lowered_mut(&mut self) -> SecondaryIterMut<'_, RuleHandle, LoweredPattern> {
        todo!()
    }
}

pub struct Keys {
    inner: std::ops::Range<u32>,
}

impl Keys {
    pub fn next_with<'a, 'b>(&'a mut self, grammar: &'b Grammar) -> Option<(RuleHandle, &'b Rule)> {
        let handle = self.next()?;
        let rule = grammar.rules.get(handle)?;
        Some((handle, rule))
    }
    pub fn next_with_mut<'a, 'b>(
        &'a mut self,
        grammar: &'b mut Grammar,
    ) -> Option<(RuleHandle, &'b mut Rule)> {
        let handle = self.next()?;
        let rule = grammar.rules.get_mut(handle)?;
        Some((handle, rule))
    }
}

impl Iterator for Keys {
    type Item = RuleHandle;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(RuleHandle::from_u32)
    }
}

pub struct SecondaryIter<'a, K: EntityRef, V> {
    inner: cranelift_entity::Iter<'a, K, Option<V>>,
}

impl<'a, K: EntityRef, V> Iterator for SecondaryIter<'a, K, V> {
    type Item = (K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (handle, next) = self.inner.next()?;
            match next {
                Some(a) => return Some((handle, a)),
                None => continue,
            }
        }
    }
}

pub struct SecondaryIterMut<'a, K: EntityRef, V> {
    inner: cranelift_entity::IterMut<'a, K, Option<V>>,
}

impl<'a, K: EntityRef, V> Iterator for SecondaryIterMut<'a, K, V> {
    type Item = (K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (handle, next) = self.inner.next()?;
            match next {
                Some(a) => return Some((handle, a)),
                None => continue,
            }
        }
    }
}

// pub struct Iter<'a> {
//     rules: cranelift_entity::Iter<'a, RuleHandle, Rule>,
//     ast: std::slice::Iter<'a, Option<Rc<ast::Rule>>>,
// }

// impl<'a> Iterator for Iter<'a> {
//     type Item = (RuleHandle, &'a Rule, Option<&'a ast::Rule>);

//     fn next(&mut self) -> Option<Self::Item> {
//         let (handle, rule) = self.rules.next()?;
//         let ast = match self.ast.next() {
//             Some(a) => a.as_ref().map(Rc::as_ref),
//             None => None,
//         };
//         Some((handle, rule, ast))
//     }
// }

// pub struct IterMut<'a> {
//     rules: cranelift_entity::IterMut<'a, RuleHandle, Rule>,
//     ast: std::slice::Iter<'a, Option<Rc<ast::Rule>>>,
// }

// impl<'a> Iterator for IterMut<'a> {
//     type Item = (RuleHandle, &'a mut Rule, Option<&'a ast::Rule>);

//     fn next(&mut self) -> Option<Self::Item> {
//         let (handle, rule) = self.rules.next()?;
//         let ast = match self.ast.next() {
//             Some(a) => a.as_ref().map(Rc::as_ref),
//             None => None,
//         };
//         Some((handle, rule, ast))
//     }
// }

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

        let handle = self.rules.push(Rule {
            name: "Lexer".into(),
            kind: RuleKind::Lexer(LexerKind::Lexer),
            attributes: Attributes::default(),
        });
        self.resolved[handle] = Some(pattern);
    }
    pub fn create_pratt_rules(&mut self, err: &ErrorAccumulator) {
        let cx = LowerCx::new(err);

        for handle in self.iter_keys() {
            let Some(pattern) = self.get_pattern(handle) else {
                continue;
            };
            if let PatternKind::Pratt(children) = pattern.kind() {
                let mut pattern = pratt::create_pratt(handle, children, self, &cx);
                lower::lower_pattern(&mut pattern, &cx);

                for &child in Rc::clone(children).iter() {
                    let rule = self.get_rule_mut(child).unwrap();
                    rule.kind = RuleKind::Parser(super::ParserKind::PrattChild);
                }

                let rule = self.get_rule_mut(handle).unwrap();
                rule.kind = RuleKind::Parser(super::ParserKind::Pratt);

                *self.get_pattern_mut(handle).unwrap() = pattern;
            }
        }
    }
    pub fn finish_rules(&mut self) {
        for (handle, rule) in self.rules.iter_mut() {
            if let RuleKind::Parser(kind @ (ParserKind::Rule | ParserKind::Pratt)) = rule.kind {
                let Some(pattern) = &mut self.resolved[handle] else {
                    continue;
                };
                let span = pattern.span();

                let seq = pattern.to_sequence(false);
                if let ParserKind::Rule = kind {
                    seq.push(Transition::CloseSpan(handle).to_pattern(span));
                }
                seq.push(Transition::Return(true).to_pattern(span));

                let choice = pattern.to_choice();
                choice.push(Transition::Return(false).to_pattern(span));
            }
        }
    }
}
