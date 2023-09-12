use std::collections::HashSet;

use crate::{
    ast,
    convert::{self, ConvertCtx},
    handle::HandleVec,
    lex, Lexer, Node, ParseError, StrSpan,
};

crate::simple_handle! {
    pub TokenHandle,
    pub RuleHandle,
    pub AstItemHandle
}

pub enum AstItem {
    Token(ast::TokenRule, Option<TokenHandle>),
    Rule(ast::SynRule, Option<RuleHandle>),
}

impl AstItem {
    pub fn name(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.name,
            AstItem::Rule(a, _) => a.name,
        }
    }
    pub fn span(&self) -> StrSpan {
        match self {
            AstItem::Token(a, _) => a.span,
            AstItem::Rule(a, _) => a.span,
        }
    }
}

#[derive(Debug)]
pub struct Attribute {
    pub name: String,
}

pub enum TokenPattern {
    Regex(String),
    RustCode(String),
}

pub struct TokenDef {
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub pattern: TokenPattern,
}

#[derive(Debug)]
pub struct RuleDef {
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub inline: bool,
    pub arguments: Vec<String>,
    pub expr: RuleExpr,
}

#[derive(Default)]
pub struct File {
    pub ast_items: HandleVec<AstItemHandle, AstItem>,

    pub ast_tokens: HandleVec<TokenHandle, AstItemHandle>,
    pub ast_rules: HandleVec<RuleHandle, AstItemHandle>,

    pub ir_tokens: HandleVec<TokenHandle, TokenDef>,
    pub ir_rules: HandleVec<RuleHandle, RuleDef>,
}

impl File {
    pub fn new_from_string(str: &str) -> (Self, Vec<ParseError>, Vec<ParseError>, Vec<Node>, Node) {
        let mut lexer = Lexer::new(str.as_bytes());

        let (tokens, trivia) = lex(&mut lexer);
        let mut parser = crate::Parser::new(str, tokens, trivia);
        _ = crate::file(&mut parser);

        let mut arena = Vec::new();
        let root = parser.build_tree(&mut arena);

        let cx = ConvertCtx::new(&str);
        let file = File::new(&cx, &root, &arena);
        (file, parser.errors, cx.finish(), arena, root)
    }
    pub fn new(cx: &ConvertCtx, cst: &Node, arena: &[Node]) -> Self {
        let file = ast::file(&cst, &arena).unwrap();
        let mut file = convert::file(cx, file);
        file.process_inlines();
        file
    }
    fn process_inlines(&mut self) {
        let mut partial_rules = Vec::new();
        let mut finished_rules = HashSet::new();
        for r in self.ir_rules.iter_keys() {
            self.rule_apply_inlines(r, &mut partial_rules, &mut finished_rules);
        }
    }
    fn rule_apply_inlines(
        &mut self,
        rule_handle: RuleHandle,
        partial_rules: &mut Vec<RuleHandle>,
        finished_rules: &mut HashSet<RuleHandle>,
    ) {
        if finished_rules.contains(&rule_handle) {
            return;
        }

        let rule = &self.ir_rules[rule_handle];
        if rule.inline {
            let conflict = partial_rules.contains(&rule_handle);
            partial_rules.push(rule_handle);

            if conflict {
                let names = partial_rules
                    .iter()
                    .flat_map(|handle| {
                        let name = &self.ir_rules[*handle].name;
                        [name, " "]
                    })
                    .collect::<String>();

                panic!("{} rule is recursively inlined:\n{}", rule.name, names);
            }

            let mut take = std::mem::replace(&mut self.ir_rules[rule_handle].expr, RuleExpr::Error);
            take.visit_nodes_top_down(&mut |node| {
                if let RuleExpr::Rule(handle) = node {
                    if self.ir_rules[*handle].inline {
                        self.rule_apply_inlines(*handle, partial_rules, finished_rules);
                        *node = self.ir_rules[*handle].expr.clone();
                    }
                }
            });
            take.finalize();
            _ = std::mem::replace(&mut self.ir_rules[rule_handle].expr, take);

            assert_eq!(partial_rules.pop(), Some(rule_handle));
        }

        finished_rules.insert(rule_handle);
    }
}

impl std::ops::Index<TokenHandle> for File {
    type Output = TokenDef;
    fn index(&self, index: TokenHandle) -> &Self::Output {
        &self.ir_tokens[index]
    }
}

impl std::ops::Index<RuleHandle> for File {
    type Output = RuleDef;
    fn index(&self, index: RuleHandle) -> &Self::Output {
        &self.ir_rules[index]
    }
}

impl std::ops::IndexMut<TokenHandle> for File {
    fn index_mut(&mut self, index: TokenHandle) -> &mut Self::Output {
        &mut self.ir_tokens[index]
    }
}

impl std::ops::IndexMut<RuleHandle> for File {
    fn index_mut(&mut self, index: RuleHandle) -> &mut Self::Output {
        &mut self.ir_rules[index]
    }
}

#[derive(Clone, Debug)]
pub enum RuleExpr {
    // base nodes
    Token(TokenHandle),
    Rule(RuleHandle),
    // structuring nodes
    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    // repetition
    ZeroOrMore(Box<RuleExpr>),
    OneOrMore(Box<RuleExpr>),
    Maybe(Box<RuleExpr>),
    // builtins
    Any,
    Not(Box<RuleExpr>),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },
    ZeroSpace,
    Empty,
    Error,
}

impl RuleExpr {
    pub fn is_sequence(&self) -> bool {
        matches!(self, Self::Sequence(_))
    }
    pub fn is_choice(&self) -> bool {
        matches!(self, Self::Choice(_))
    }
    pub fn visit_nodes_top_down(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        fun(self);
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_top_down(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_top_down(fun);
                separator.visit_nodes_top_down(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_top_down(fun);
            }
            _ => {}
        }
    }
    pub fn visit_nodes_bottom_up(&mut self, fun: &mut dyn FnMut(&mut RuleExpr)) {
        match self {
            RuleExpr::Sequence(vec) | RuleExpr::Choice(vec) => {
                for a in vec {
                    a.visit_nodes_bottom_up(fun);
                }
            }
            RuleExpr::SeparatedList { element, separator } => {
                element.visit_nodes_bottom_up(fun);
                separator.visit_nodes_bottom_up(fun);
            }
            RuleExpr::Not(a)
            | RuleExpr::Maybe(a)
            | RuleExpr::ZeroOrMore(a)
            | RuleExpr::OneOrMore(a) => {
                a.visit_nodes_bottom_up(fun);
            }
            _ => {}
        }
        fun(self);
    }
    // pub fn push_sequence(&mut self, next: RuleExpr) {
    //     match (self, next) {
    //         (RuleExpr::Sequence(seq1), RuleExpr::Sequence(seq2)) => {
    //             seq1.extend(seq2);
    //         }
    //         (RuleExpr::Sequence(seq), other) => {
    //             seq.push(other);
    //         }
    //         (this, RuleExpr::Sequence(mut seq)) => {
    //             let first = std::mem::replace(this, RuleExpr::Error);
    //             seq.insert(0, first);
    //             *this = RuleExpr::Sequence(seq);
    //         }
    //         (this, b) => {
    //             let first = std::mem::replace(this, RuleExpr::Error);
    //             *this = RuleExpr::Sequence(vec![first, b])
    //         }
    //     }
    // }
    pub fn finalize(&mut self) {
        self.visit_nodes_bottom_up(&mut |node| match node {
            RuleExpr::Sequence(seq) => {
                let mut i = 0;
                while i < seq.len() {
                    match &mut seq[i] {
                        RuleExpr::Sequence(a) => {
                            let drain = std::mem::take(a);
                            seq.splice(i..=i, drain);
                        }
                        RuleExpr::Empty => {
                            seq.remove(i);
                        }
                        _ => i += 1,
                    }
                }
                if seq.is_empty() {
                    *node = RuleExpr::Empty;
                }
            }
            RuleExpr::Choice(seq) => {
                let mut i = 0;
                while i < seq.len() {
                    match &mut seq[i] {
                        RuleExpr::Choice(a) => {
                            let drain = std::mem::take(a);
                            seq.splice(i..=i, drain);
                        }
                        RuleExpr::Empty => {
                            seq.remove(i);
                        }
                        _ => i += 1,
                    }
                }
                if seq.is_empty() {
                    *node = RuleExpr::Empty;
                }
            }
            _ => {}
        });
    }
}
