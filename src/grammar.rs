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

pub enum ParserRuleExpr {
    Terminal(String),
    NonTerminal(String),
    // structuring node
    Sequence(Vec<ParserRuleExpr>),
    // postfix repetition
    OneOrMore(Vec<ParserRuleExpr>),
    ZeroOrMore(Vec<ParserRuleExpr>),
    Maybe(Vec<ParserRuleExpr>),
    // immediatelly matches, just an empty rule
    Empty,
}

pub struct ParserRule {
    name: String,
    rule: ParserRuleExpr,
}

pub struct Parser {
    rules: Vec<ParserRule>,
}
