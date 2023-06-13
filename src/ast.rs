use crate::{bump::BumpAlloc, handle::HandleVec, simple_handle, Child, Tree, TreeKind};

simple_handle! {
    TokenHandle,
    RuleHandle
}

pub struct TokenDef {
    name: String,
    expression: String,
}

pub struct RuleDef {
    name: String,
    expression: RuleExpr,
}

#[derive(Default)]
struct File {
    tokens: HandleVec<TokenHandle, TokenDef>,
    rules: HandleVec<RuleHandle, RuleDef>,
}

enum RuleExpr {
    // base nodes
    Terminal(TokenHandle),
    Rule(RuleHandle),
    // structuring nodes
    Sequence(Vec<RuleExpr>),
    Choice(Vec<RuleExpr>),
    // repetition
    ZeroOrMore(Vec<RuleExpr>),
    OneOrMore(Vec<RuleExpr>),
    Maybe(Vec<RuleExpr>),
    // builtins
    Any,
    Not(TokenHandle),
    SeparatedList {
        element: Box<RuleExpr>,
        separator: Box<RuleExpr>,
    },
    ZeroSpace,
}

fn process(tree: &Tree, b: &mut BumpAlloc) -> File {
    let mut file = File::default();
    match tree.kind {
        TreeKind::File => todo!(),
        TreeKind::ErrorTree => todo!(),
        TreeKind::Attribute => todo!(),
        TreeKind::AttributeExpr => todo!(),
        TreeKind::AttributeValue => todo!(),
        TreeKind::Tokenizer => todo!(),
        TreeKind::TokenRule => todo!(),
        TreeKind::SynRule => todo!(),
        TreeKind::Parameters => todo!(),
        TreeKind::SynExpr => todo!(),
        TreeKind::PreExpr => todo!(),
        TreeKind::AtomExpr => todo!(),
        TreeKind::CallExpr => todo!(),
        TreeKind::BinExpr => todo!(),
        TreeKind::SeqExpr => todo!(),
        TreeKind::PostExpr => todo!(),
    }
    for c in &tree.children {
        match c {
            Child::Token(_) => todo!(),
            Child::Tree(_) => todo!(),
        }
    }
}

fn do_file(tree: &Tree) -> File {
    let mut tokens = HandleVec::new();
    let mut rules = HandleVec::new();

    let mut state = 0;
    for c in tree.children {
        match c {
            Child::Token(_) => todo!(),
            Child::Tree(Tree {
                kind,
                children,
                err,
            }) => todo!(),
        }
    }

    File { tokens, rules }
}
