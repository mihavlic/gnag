use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

enum TemplateAst {
    Static(String),
    Substitution(Box<TokenTree>),
    Error {
        message: &'static str,
        span: Span,
    },
    Iteration {
        children: Vec<TemplateAst>,
        span: Span,
    },
}

struct TemplateBuilder {
    previous_spacing: Spacing,
    string: String,
    actions: Vec<TemplateAst>,
}

impl TemplateBuilder {
    fn new() -> TemplateBuilder {
        Self {
            previous_spacing: Spacing::Alone,
            string: String::new(),
            actions: Vec::new(),
        }
    }
    fn flush_string(&mut self) {
        if !self.string.is_empty() {
            let string = self.string.clone();
            self.string.clear();
            self.actions.push(TemplateAst::Static(string));
        }
    }
    fn static_text(&mut self, str: &str, spacing: Spacing) {
        'add_space: {
            if self.previous_spacing == Spacing::Joint {
                break 'add_space;
            }

            let Some(a) = str.chars().next() else {
                return;
            };

            let Some(b) = self.string.chars().rev().next() else {
                break 'add_space;
            };

            if a == '#' {
                break 'add_space;
            }

            if b == ',' {
                break 'add_space;
            }

            if (a.is_alphanumeric() && matches!(b, '(' | '[' | '<'))
                || (b.is_alphanumeric() && matches!(a, ')' | ']' | '>'))
            {
                break 'add_space;
            }

            self.string.push_str(" ");
        }

        self.previous_spacing = spacing;
        self.string.push_str(str);
    }
    fn substitution(&mut self, expr: TokenTree) {
        self.flush_string();
        self.actions
            .push(TemplateAst::Substitution(Box::new(expr.into())))
    }
    fn iteration(&mut self, span: Span, children: Vec<TemplateAst>) {
        self.flush_string();
        self.actions.push(TemplateAst::Iteration { span, children });
    }
    fn scope(&mut self, fun: impl FnOnce(&mut Self)) -> Vec<TemplateAst> {
        let len = self.actions.len();
        fun(self);
        self.flush_string();
        self.actions.drain(len..).collect()
    }
}

fn is_punct(tt: Option<&TokenTree>, c: char) -> bool {
    match tt {
        Some(TokenTree::Punct(p)) => p.as_char() == c,
        _ => false,
    }
}

type TokenIter<'a> = std::slice::Iter<'a, TokenTree>;

fn collect_token_stream(stream: TokenStream) -> Vec<TokenTree> {
    stream.into_iter().collect()
}

fn parse_substitution<'a>(iter: &mut TokenIter<'a>, builder: &mut TemplateBuilder) -> bool {
    let original_iter = iter.clone();
    let Some(next) = iter.next() else {
        return false;
    };

    match next {
        TokenTree::Ident(_) | TokenTree::Literal(_) => {
            builder.substitution(next.clone());
        }
        TokenTree::Group(g)
            if matches!(g.delimiter(), Delimiter::Parenthesis | Delimiter::Brace) =>
        {
            let mut peek = iter.clone();
            let first = peek.next();
            let second = peek.next();

            let first_is_star = is_punct(first, '*');
            let second_is_star = is_punct(second, '*');

            if first_is_star || second_is_star {
                let children = builder.scope(|builder| {
                    if g.delimiter() == Delimiter::Brace {
                        // strip the delimiter, we don't want to pass it to rust code
                        builder.substitution(group(Delimiter::None, g.stream()));
                    } else {
                        parse_body(g.stream(), builder);
                    }

                    if second_is_star {
                        let separator = first.unwrap().to_string();
                        builder.static_text(&separator, Spacing::Alone);
                    }
                });

                builder.iteration(g.span(), children);
            } else {
                builder.substitution(group(Delimiter::None, g.stream()));
            }

            if first_is_star {
                iter.next();
            }
            if second_is_star {
                iter.next();
            }
        }
        _ => {
            *iter = original_iter;
            return false;
        }
    }
    true
}

fn parse_body(stream: TokenStream, builder: &mut TemplateBuilder) {
    let tokens = collect_token_stream(stream);

    let mut iter = tokens.iter();
    parse_body_iter(&mut iter, builder);
    assert_eq!(iter.len(), 0);
}

fn parse_body_iter(iter: &mut TokenIter, builder: &mut TemplateBuilder) {
    let mut is_escaped = false;
    while let Some(element) = iter.next() {
        let escaped = std::mem::replace(&mut is_escaped, false);

        match element {
            TokenTree::Punct(punct) if !escaped => match punct.as_char() {
                '\\' => {
                    is_escaped = true;
                    continue;
                }
                '#' => {
                    if parse_substitution(iter, builder) {
                        continue;
                    }
                }
                _ => {}
            },
            TokenTree::Group(g) => {
                let (open, close) = match g.delimiter() {
                    Delimiter::Parenthesis => ("(", ")"),
                    Delimiter::Brace => ("{", "}"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::None => ("", ""),
                };
                builder.static_text(open, Spacing::Alone);
                parse_body(g.stream(), builder);
                builder.static_text(close, Spacing::Alone);

                continue;
            }
            _ => (),
        }

        let spacing = match element {
            TokenTree::Punct(p) => p.spacing(),
            _ => Spacing::Alone,
        };
        builder.static_text(&element.to_string(), spacing);
    }
}

fn ident(str: &str) -> TokenTree {
    Ident::new(str, Span::call_site()).into()
}

fn ident_mixed_hygiene(str: &str) -> TokenTree {
    Ident::new(str, Span::mixed_site()).into()
}

fn punct(char: char) -> TokenTree {
    Punct::new(char, proc_macro::Spacing::Alone).into()
}

fn punct_joint(char: char) -> TokenTree {
    Punct::new(char, proc_macro::Spacing::Joint).into()
}

fn group(delimiter: Delimiter, stream: impl Into<TokenStream>) -> TokenTree {
    Group::new(delimiter, stream.into()).into()
}

fn string_literal(str: &str) -> TokenTree {
    Literal::string(str).into()
}

fn error(str: &str, span: Span) -> TokenStream {
    let mut message = string_literal(str);
    message.set_span(span);

    let mut a = ident("compile_error");
    let mut b = punct('!');
    let mut c = group(Delimiter::Parenthesis, message);

    a.set_span(span);
    b.set_span(span);
    c.set_span(span);

    [a, b, c].into_iter().collect()
}

fn ast_to_code(render_cx: &TokenTree, ast: Vec<TemplateAst>) -> TokenStream {
    let mut stream = Vec::<TokenTree>::new();

    for ast in ast {
        match ast {
            TemplateAst::Static(str) => {
                // cx.append_str("{str}")
                stream.extend([
                    render_cx.clone(),
                    punct('.'),
                    ident_mixed_hygiene("append_str"),
                    group(Delimiter::Parenthesis, string_literal(&str)),
                    punct(';'),
                ]);
            }
            TemplateAst::Substitution(tt) => {
                // tt.render_into(cx)
                stream.extend([
                    *tt,
                    punct('.'),
                    ident_mixed_hygiene("render_into"),
                    group(Delimiter::Parenthesis, render_cx.clone()),
                    punct(';'),
                ]);
            }
            TemplateAst::Iteration { span, mut children } => {
                // find the expression to iterate over
                // we technically parse a recursive grammar where iterations can contain anything
                // and then we enforce a subset here
                let iter_variable = ident("value");
                let mut iterator_expr = None;
                for child in &mut children {
                    match child {
                        TemplateAst::Substitution(expr) => {
                            if iterator_expr.is_none() {
                                iterator_expr = Some(expr.clone());
                                *child = TemplateAst::Substitution(Box::new(iter_variable.clone()));
                            } else {
                                *child = TemplateAst::Error { span: expr.span(), message: "Iterating over multiple iterators at the same time is currently not implemented." };
                            }
                        }
                        TemplateAst::Iteration { span, children: _ } => {
                            *child = TemplateAst::Error {
                                span: *span,
                                message: "Nested iterations are forbidden.",
                            };
                        }
                        _ => {}
                    }
                }

                if let Some(iterator_expr) = iterator_expr {
                    // doing the nested ast_to_code here supresses possible nested errors
                    let loop_body = ast_to_code(render_cx, children);
                    stream.extend([
                        ident("for"),
                        iter_variable.clone(),
                        ident("in"),
                        *iterator_expr,
                        group(Delimiter::Brace, loop_body),
                    ]);
                } else {
                    stream.extend(error("No value provided for iteration", span));
                }
            }
            TemplateAst::Error { span, message } => {
                let error = error(message, span);
                stream.extend(error);
                stream.extend([punct(';')]);
            }
        };
    }

    TokenStream::from_iter(stream)
}

fn convert_body_to_code(render_cx: &TokenTree, iter: &mut TokenIter) -> TokenStream {
    let mut builder = TemplateBuilder::new();

    let ast = builder.scope(|builder| {
        parse_body_iter(iter, builder);
    });

    ast_to_code(render_cx, ast)
}

fn parse_leading_expr_best_effort<'a>(iter: &mut TokenIter<'a>) -> Option<TokenStream> {
    let original_iter = iter;
    let mut iter = original_iter.clone();

    let mut output = Vec::new();

    while let Some(peek) = iter.clone().next() {
        if let TokenTree::Punct(p) = peek {
            if p.as_char() == ',' || p.as_char() == ';' {
                break;
            }

            iter.next();
            output.push(peek.clone());
        } else {
            break;
        }
    }

    let next = iter.next()?;
    if let TokenTree::Group(_) | TokenTree::Ident(_) | TokenTree::Literal(_) = next {
        output.push(next.clone());
    } else {
        return None;
    }

    let next = iter.next();
    if next.is_some() && !is_punct(next, ',') {
        return None;
    }

    *original_iter = iter;
    Some(TokenStream::from_iter(output))
}

#[proc_macro]
pub fn template(stream: TokenStream) -> TokenStream {
    let render_cx = ident("cx");
    let template = convert_body_to_code(&render_cx, &mut collect_token_stream(stream).iter());

    let lambda_body = {
        let stream = [
            punct('|'),
            render_cx,
            punct('|'),
            group(Delimiter::Brace, template),
        ];
        TokenStream::from_iter(stream)
    };

    let body = {
        [
            punct_joint(':'),
            punct(':'),
            ident("code_render"),
            punct_joint(':'),
            punct(':'),
            ident("Template"),
            group(Delimiter::Parenthesis, lambda_body),
        ]
        .into_iter()
        .collect()
    };

    body
}

#[proc_macro]
pub fn render(stream: TokenStream) -> TokenStream {
    let tokens = collect_token_stream(stream);
    let mut iter = tokens.iter();

    let render_cx = ident("cx");
    let render_cx_value = parse_leading_expr_best_effort(&mut iter)
        .expect("Macro must start with RenderCx expression");

    let template = convert_body_to_code(&render_cx, &mut iter);

    let body = [
        // evaluate cx
        ident("let"),
        render_cx.clone(),
        punct(':'),
        punct('&'),
        punct_joint(':'),
        punct(':'),
        ident("code_render"),
        punct_joint(':'),
        punct(':'),
        ident("RenderCx"),
        punct('='),
        punct('&'),
        group(Delimiter::None, render_cx_value),
        punct(';'),
        // let start = cx.start_render();
        ident("let"),
        ident("start"),
        punct('='),
        render_cx.clone(),
        punct('.'),
        ident("start_render"),
        group(Delimiter::Parenthesis, TokenStream::new()),
        punct(';'),
        // self.render_into(cx);
        group(Delimiter::Brace, template),
        // cx.finish_render(start)
        render_cx.clone(),
        punct('.'),
        ident("finish_render"),
        group(Delimiter::Parenthesis, ident("start")),
    ]
    .into_iter()
    .collect::<Vec<_>>();

    std::iter::once(group(Delimiter::Brace, TokenStream::from_iter(body))).collect()
}
