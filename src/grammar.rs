// LEXER

pub enum LexerRuleExpr {
    Literal(String),
    Regex(String),
}

pub struct LexerRule {
    skip: bool,
    name: String,
    rule: LexerRuleExpr,
}

pub struct Lexer {
    rules: Vec<LexerRule>,
}

// PARSER

pub struct TerminalHandle(u32);
pub struct NonterminalHandle(u32);

pub enum ParserRuleAst {
    // base nodes
    Literal(Span),
    Ident(Span),
    // structuring nodes
    Sequence(Vec<ParserRuleAst>),
    Choice(Vec<ParserRuleAst>),
    // repetition
    OneOrMore(Vec<ParserRuleAst>),
    ZeroOrMore(Vec<ParserRuleAst>),
    Maybe(Vec<ParserRuleAst>),
    // function call
    Call(Span, Vec<ParserRuleAst>),
}

pub enum ParserRuleExpr {
    // base nodes
    Terminal(TerminalHandle),
    NonTerminal(NonterminalHandle),
    // structuring nodes
    Sequence(Vec<ParserRuleExpr>),
    Choice(Vec<ParserRuleExpr>),
    // repetition
    OneOrMore(Vec<ParserRuleExpr>),
    ZeroOrMore(Vec<ParserRuleExpr>),
    Maybe(Vec<ParserRuleExpr>),
    // builtins
    Any,
    Not(TerminalHandle),
    ZeroSpace,
}

pub struct ParserRule {
    name: String,
    rule: ParserRuleExpr,
}

pub struct Parser {
    rules: Vec<ParserRule>,
}
