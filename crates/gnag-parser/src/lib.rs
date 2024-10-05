#![allow(non_upper_case_globals, non_snake_case)]

//! This file is generated by gnag-cli from 'grammar.gng'.
//! Edit the grammar file instead.

use gnag_runtime::lexer::*;
use gnag_runtime::parser::*;
use gnag_runtime::*;

pub mod kinds {
    use gnag_runtime::{NodeKind, NodeType};

    pub const Whitespace: NodeKind = NodeKind::new(1, NodeType::Skip);
    pub const Comment: NodeKind = NodeKind::new(2, NodeType::Skip);
    pub const Newline: NodeKind = NodeKind::new(3, NodeType::Token);
    pub const String: NodeKind = NodeKind::new(4, NodeType::Token);
    pub const Ident: NodeKind = NodeKind::new(5, NodeType::Token);
    pub const InlineKeyword: NodeKind = NodeKind::new(6, NodeType::Token);
    pub const LexerKeyword: NodeKind = NodeKind::new(7, NodeType::Token);
    pub const ParserKeyword: NodeKind = NodeKind::new(8, NodeType::Token);
    pub const PrattKeyword: NodeKind = NodeKind::new(9, NodeType::Token);
    pub const GroupKeyword: NodeKind = NodeKind::new(10, NodeType::Token);
    pub const LCurly: NodeKind = NodeKind::new(11, NodeType::Token);
    pub const RCurly: NodeKind = NodeKind::new(12, NodeType::Token);
    pub const LParen: NodeKind = NodeKind::new(13, NodeType::Token);
    pub const RParen: NodeKind = NodeKind::new(14, NodeType::Token);
    pub const LBracket: NodeKind = NodeKind::new(15, NodeType::Token);
    pub const RBracket: NodeKind = NodeKind::new(16, NodeType::Token);
    pub const LAngle: NodeKind = NodeKind::new(17, NodeType::Token);
    pub const RAngle: NodeKind = NodeKind::new(18, NodeType::Token);
    pub const Question: NodeKind = NodeKind::new(19, NodeType::Token);
    pub const Pipe: NodeKind = NodeKind::new(20, NodeType::Token);
    pub const Star: NodeKind = NodeKind::new(21, NodeType::Token);
    pub const Plus: NodeKind = NodeKind::new(22, NodeType::Token);
    pub const At: NodeKind = NodeKind::new(23, NodeType::Token);
    pub const Colon: NodeKind = NodeKind::new(24, NodeType::Token);
    pub const Comma: NodeKind = NodeKind::new(25, NodeType::Token);
    pub const Dot: NodeKind = NodeKind::new(26, NodeType::Token);
    pub const Equals: NodeKind = NodeKind::new(27, NodeType::Token);
    pub const Error: NodeKind = NodeKind::new(28, NodeType::Token);
    pub const File: NodeKind = NodeKind::new(30, NodeType::Nonterminal);
    pub const RuleGroup: NodeKind = NodeKind::new(31, NodeType::Nonterminal);
    pub const Attribute: NodeKind = NodeKind::new(32, NodeType::Nonterminal);
    pub const Parameters: NodeKind = NodeKind::new(33, NodeType::Nonterminal);
    pub const Rule: NodeKind = NodeKind::new(34, NodeType::Nonterminal);
    pub const Atom: NodeKind = NodeKind::new(35, NodeType::Nonterminal);
    pub const CallExpr: NodeKind = NodeKind::new(36, NodeType::Nonterminal);
    pub const ParenExpr: NodeKind = NodeKind::new(37, NodeType::Nonterminal);
    pub const PrattExpr: NodeKind = NodeKind::new(38, NodeType::Nonterminal);
    pub const PostExpr: NodeKind = NodeKind::new(39, NodeType::Nonterminal);
    pub const SequenceExpr: NodeKind = NodeKind::new(40, NodeType::Nonterminal);
    pub const ChoiceExpr: NodeKind = NodeKind::new(41, NodeType::Nonterminal);
}

pub const LANGUAGE: Language = Language {
    lexer_entry: rules::pLexer,
    parser_entry: rules::pFile,
    names: &[
        "NONE",
        "Whitespace",
        "Comment",
        "Newline",
        "String",
        "Ident",
        "InlineKeyword",
        "LexerKeyword",
        "ParserKeyword",
        "PrattKeyword",
        "GroupKeyword",
        "LCurly",
        "RCurly",
        "LParen",
        "RParen",
        "LBracket",
        "RBracket",
        "LAngle",
        "RAngle",
        "Question",
        "Pipe",
        "Star",
        "Plus",
        "At",
        "Colon",
        "Comma",
        "Dot",
        "Equals",
        "Error",
        "Lexer",
        "File",
        "RuleGroup",
        "Attribute",
        "Parameters",
        "Rule",
        "Atom",
        "CallExpr",
        "ParenExpr",
        "PrattExpr",
        "PostExpr",
        "SequenceExpr",
        "ChoiceExpr",
    ],
};

mod rules {
    use super::kinds::*;
    use super::*;

    pub fn pFile(p: &mut Parser) -> bool {
        let start = p.open_span();
        loop {
            if p.token(Newline) {
                continue;
            }
            if !pTokensOrRules(p) {
                break;
            }
        }
        p.close_span(start, File);
        return true;
    }
    pub fn pTokensOrRules(p: &mut Parser) -> bool {
        let start = p.open_span();
        if p.token(LexerKeyword) || p.token(ParserKeyword) {
            let checkpoint: ParserPosition = p.save_position();
            while p.token(Newline) {}
            if p.token(LCurly) {
                while p.token(Newline) || pRule(p) {}
                p.token(RCurly);
            } else {
                p.restore_position(checkpoint);
            }
            p.close_span(start, RuleGroup);
            return true;
        }
        return false;
    }
    pub fn pAttribute(p: &mut Parser) -> bool {
        let start = p.open_span();
        if p.token(At) {
            p.token(Ident);
            p.token(Newline);
            p.close_span(start, Attribute);
            return true;
        }
        return false;
    }
    pub fn pParameters(p: &mut Parser) -> bool {
        let start = p.open_span();
        if p.token(LParen) {
            while p.token(Ident) && p.token(Comma) {}
            p.token(RParen);
            p.close_span(start, Parameters);
            return true;
        }
        return false;
    }
    pub fn pRule(p: &mut Parser) -> bool {
        let start = p.open_span();
        let checkpoint: ParserPosition = p.save_position();
        while pAttribute(p) {}
        if p.token(Ident) {
            pParameters(p);
            p.token(Equals);
            pExpr(p, 0);
            p.token(Newline);
            p.close_span(start, Rule);
            return true;
        }
        p.restore_position(checkpoint);
        return false;
    }
    pub fn pExpr(p: &mut Parser, min_bp: u32) -> bool {
        let start = p.open_span();
        'b0: {
            'b1: {
                'b2: {
                    if !p.token(Ident) {
                        if !p.token(String) {
                            break 'b2;
                        }
                    }
                    p.close_span(start, Atom);
                    break 'b1;
                }
                if p.token(LAngle) {
                    p.token(Ident);
                    pExpr(p, 0);
                    p.token(RAngle);
                    p.close_span(start, CallExpr);
                    break 'b1;
                }
                if p.token(LParen) {
                    pExpr(p, 0);
                    p.token(RParen);
                    p.close_span(start, ParenExpr);
                    break 'b1;
                }
                if p.token(PrattKeyword) {
                    let checkpoint: ParserPosition = p.save_position();
                    while p.token(Newline) {}
                    'b3: {
                        if p.token(LCurly) {
                            loop {
                                if p.token(Newline) {
                                    continue;
                                }
                                if !pRule(p) {
                                    break;
                                }
                            }
                            p.token(RCurly);
                            break 'b3;
                        }
                        p.restore_position(checkpoint);
                    }
                    p.close_span(start, PrattExpr);
                    break 'b1;
                }
                break 'b0;
            }
            'b4: loop {
                if min_bp < 5 {
                    if p.token(Question) || p.token(Star) || p.token(Plus) {
                        p.close_span(start, PostExpr);
                        continue 'b4;
                    }
                }
                if min_bp < 3 {
                    if pExpr(p, 3) {
                        while pExpr(p, 3) {}
                        p.close_span(start, SequenceExpr);
                        continue 'b4;
                    }
                }
                if min_bp < 2 {
                    if p.token(Pipe) {
                        if pExpr(p, 2) {
                            while p.token(Pipe) && pExpr(p, 2) {}

                            p.close_span(start, ChoiceExpr);
                            continue 'b4;
                        }
                    }
                }
                break;
            }
            return true;
        }
        return false;
    }
    pub fn pLexer(l: &mut Lexer) -> Option<NodeKind> {
        if l.byte_sequence(b"\n") {
            return Some(Newline);
        }
        if l.ascii_class(CharacterClass::Whitespace) {
            while l.ascii_class(CharacterClass::Whitespace) {}
            return Some(Whitespace);
        }
        if l.byte_sequence(b"//") {
            l.string_like(b'\n');
            return Some(Comment);
        }
        if l.string_like(b'\'') {
            return Some(String);
        }
        if l.ascii_class(CharacterClass::IdentifierStart) {
            while l.ascii_class(CharacterClass::IdentifierContinue) {}
            if l.keyword(b"lexer") {
                return Some(LexerKeyword);
            }
            if l.keyword(b"parser") {
                return Some(ParserKeyword);
            }
            if l.keyword(b"pratt") {
                return Some(PrattKeyword);
            }
            if l.keyword(b"group") {
                return Some(GroupKeyword);
            }
            return Some(Ident);
        }
        if l.byte_sequence(b"{") {
            return Some(LCurly);
        }
        if l.byte_sequence(b"}") {
            return Some(RCurly);
        }
        if l.byte_sequence(b"(") {
            return Some(LParen);
        }
        if l.byte_sequence(b")") {
            return Some(RParen);
        }
        if l.byte_sequence(b"[") {
            return Some(LBracket);
        }
        if l.byte_sequence(b"]") {
            return Some(RBracket);
        }
        if l.byte_sequence(b"<") {
            return Some(LAngle);
        }
        if l.byte_sequence(b">") {
            return Some(RAngle);
        }
        if l.byte_sequence(b"?") {
            return Some(Question);
        }
        if l.byte_sequence(b"|") {
            return Some(Pipe);
        }
        if l.byte_sequence(b"*") {
            return Some(Star);
        }
        if l.byte_sequence(b"+") {
            return Some(Plus);
        }
        if l.byte_sequence(b"@") {
            return Some(At);
        }
        if l.byte_sequence(b":") {
            return Some(Colon);
        }
        if l.byte_sequence(b",") {
            return Some(Comma);
        }
        if l.byte_sequence(b".") {
            return Some(Dot);
        }
        if l.byte_sequence(b"=") {
            return Some(Equals);
        }
        'b0: {
            'b1: {
                if l.not_ascii_class(CharacterClass::Whitespace) {
                    while l.not_ascii_class(CharacterClass::Whitespace) {}
                    break 'b1;
                }
                if !l.any_utf8() {
                    break 'b0;
                }
            }
            return Some(Error);
        }
        return None;
    }
}
