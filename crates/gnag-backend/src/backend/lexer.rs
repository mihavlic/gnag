use crate::{
    ast::pattern::{Group, Pattern, PatternKind, Transition},
    span::Span,
};

use super::{grammar::Grammar, lower::LowerCx};

pub(crate) fn create_lexer_expr(grammar: &mut Grammar, cx: &LowerCx) -> Pattern {
    let mut has_word_token = false;
    let mut keyword_cases = Vec::new();

    for (handle, rule, ast) in grammar.iter() {
        if !rule.kind.is_lexer() {
            continue;
        }

        let span = ast.unwrap().name.span;
        let is_word = rule.attributes.word;
        let is_keyword = rule.attributes.keyword;

        if is_word {
            if has_word_token {
                cx.err.error_static(span, "Only one @word token may exist");
            }
            has_word_token = true;
        }

        if is_keyword {
            let span = rule.pattern.span();
            match rule.pattern.kind() {
                PatternKind::Transition(Transition::Bytes(bytes)) => {
                    let pattern = Group::Sequence { explicit: false }.to_pattern(
                        vec![
                            Transition::Keyword(bytes.clone()).to_pattern(span),
                            Transition::LexerReturn(Some(handle)).to_pattern(span),
                        ],
                        span,
                    );
                    keyword_cases.push(pattern);
                }
                _ => cx
                    .err
                    .error_static(span, "@keyword requires string literal in body"),
            };
        }
    }

    let mut token_cases = Vec::new();
    for (handle, rule, ast) in grammar.iter() {
        if !rule.kind.is_lexer() {
            continue;
        }

        let span = ast.unwrap().name.span;
        let is_word = rule.attributes.word;
        let is_keyword = rule.attributes.keyword;

        if is_keyword {
            if !has_word_token {
                cx.err.error_static(span, "Missing @keyword token");
            }
            // the keyword rules get handled under @the word case
        } else if is_word {
            keyword_cases.push(Transition::LexerReturn(Some(handle)).to_pattern(span));

            let keyword_cases = std::mem::take(&mut keyword_cases);

            let mut body = rule.pattern.clone();
            body.to_sequence(true)
                .push(Group::Choice.to_pattern(keyword_cases, span));
            token_cases.push(body);
        } else {
            let mut body = rule.pattern.clone();
            body.to_sequence(true)
                .push(Transition::LexerReturn(Some(handle)).to_pattern(span));
            token_cases.push(body);
        }
    }

    token_cases.push(Transition::LexerReturn(None).to_pattern(Span::empty()));

    Group::Choice.to_pattern(token_cases, Span::empty())
}
