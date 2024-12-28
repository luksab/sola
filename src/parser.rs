use chumsky::prelude::*;
use logos::Logos;

use crate::base_ast::*;

// The Chumsky parser will produce tokens first, then parse them into AST.
#[derive(Logos, Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token<'input> {
    // Operators
    #[token("=")]
    Assign,
    #[token("==")]
    Eq,
    #[token("!=")]
    Ne,
    #[token("<")]
    Lt,
    #[token("<=")]
    Le,
    #[token(">")]
    Gt,
    #[token(">=")]
    Ge,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("!")]
    Exclam,

    // Keywords
    #[token("extern")]
    Extern,
    #[token("fn")]
    Fn,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("while")]
    While,
    #[token("let")]
    Let,
    #[token("return")]
    Return,
    #[regex(r"true|false")]
    BoolLiteral(&'input str),
    #[token("i32")]
    TypeI32,
    #[token("bool")]
    TypeBool,

    // Symbols
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(",")]
    Comma,
    #[token(";")]
    Semicolon,
    #[token(":")]
    Colon,
    #[token("->")]
    Arrow,

    // Identifiers, literals, comments
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier(&'input str),
    #[regex(r#"\d+"#)]
    Integer(&'input str),
    #[regex(r#""[^"]*""#)]
    StrLit(&'input str),
    #[regex(r"//.*")]
    Comment(&'input str),

    // Whitespace
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,

    // Error token
    Error,
}

pub fn parser<'input>() -> impl Parser<Token<'input>, Program<'input>, Error = Simple<Token<'input>>>
{
    let expr_parser = std::sync::Arc::new(expression_parser());
    program_parser(expr_parser)
}

fn program_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Program<'input>, Error = Simple<Token<'input>>> {
    top_level_parser(expr_parser)
        .repeated()
        .map(|things| Program { things })
        .then_ignore(end())
}

fn top_level_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, TopLevel<'input>, Error = Simple<Token<'input>>> {
    choice((
        function_parser(expr_parser).map(TopLevel::Function),
        comment_parser().map(TopLevel::Comment),
    ))
}

fn comment_parser<'input>(
) -> impl Parser<Token<'input>, Comment<'input>, Error = Simple<Token<'input>>> {
    filter_map(|span, token| match token {
        Token::Comment(c) => Ok(Comment::new(c)),
        other => Err(Simple::expected_input_found(span, vec![], Some(other))),
    })
}

fn function_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Function<'input>, Error = Simple<Token<'input>>> {
    // {extern} fn <identifier> ( <params> ) -> <type> { ... }
    let extern_fn = just(Token::Extern)
        .then_ignore(just(Token::Fn))
        .ignore_then(
            function_definition_parser().map_with_span(|definition, span| (definition, span)),
        )
        .map_with_span(|definition, span| Function {
            definition,
            body: None,
            span,
        });

    extern_fn.or(just(Token::Fn)
        .ignore_then(
            function_definition_parser().map_with_span(|definition, span| (definition, span)),
        )
        .then(block_parser(expr_parser).map_with_span(|b, s| (b, s)))
        .map_with_span(|(definition, body), span| Function {
            definition,
            body: Some(Box::new((Expression::Block(body.0), body.1))),
            span,
        }))
}

fn function_definition_parser<'input>(
) -> impl Parser<Token<'input>, FunctionDefinition<'input>, Error = Simple<Token<'input>>> {
    // <identifier> ( <params> ) -> <type>
    identifier_parser()
        .then_ignore(just(Token::LParen))
        .then(
            parameter_parser()
                .separated_by(just(Token::Comma))
                .allow_trailing(),
        )
        .then_ignore(just(Token::RParen))
        .then(just(Token::Arrow).ignore_then(type_parser()).or_not())
        .map(|((name, params), return_type)| FunctionDefinition {
            name,
            params,
            return_type,
        })
}

fn parameter_parser<'input>(
) -> impl Parser<Token<'input>, Parameter<'input>, Error = Simple<Token<'input>>> {
    // <identifier>: <type>
    identifier_parser()
        .then_ignore(just(Token::Colon)) // or parse ':' properly if you want
        .then(type_parser())
        .map_with_span(|(name, tipe), span| Parameter { name, tipe, span })
}

fn type_parser<'input>() -> impl Parser<Token<'input>, Type<'input>, Error = Simple<Token<'input>>>
{
    choice((
        just(Token::TypeI32).to(Type::I32),
        just(Token::TypeBool).to(Type::Bool),
    ))
}

fn block_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Block<'input>, Error = Simple<Token<'input>>> {
    // { <statements> <expr>? }
    recursive(|block| {
        just(Token::LBrace)
            .ignore_then(statement_parser(expr_parser.clone(), block.clone()).repeated())
            .then(
                expr_parser
                    .clone()
                    .or_not()
                    .map(|opt_expr| opt_expr.map(Box::new)),
            )
            .then_ignore(just(Token::RBrace))
            .map(|(statements, return_value)| Block {
                statements,
                return_value,
            })
    })
}

fn statement_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
    block_parser: impl Parser<Token<'input>, Block<'input>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Statement<'input>, Error = Simple<Token<'input>>> {
    // let <name>: <type> = <expr> ;
    // return <expr>? ;
    // expression ;
    // "// comment"
    choice((
        // let <name>: <type> = <expr> ;
        just(Token::Let)
            .ignore_then(identifier_parser())
            .then_ignore(just(Token::Colon).or_not())
            .then(type_parser().or_not())
            .then_ignore(just(Token::Assign))
            .then(expr_parser.clone())
            .then_ignore(just(Token::Semicolon))
            .map(|((name, tipe), expr)| {
                Statement::Let(Let {
                    name,
                    tipe: tipe.unwrap_or(Type::I32),
                    value: expr,
                })
            }),
        // return <expr>? ;
        just(Token::Return)
            .ignore_then(expr_parser.clone().or_not())
            .then_ignore(just(Token::Semicolon))
            .map(|expr| Statement::Return(expr.map(Box::new))),
        // if <expr> { <block> } (else { <block> })?
        just(Token::If)
            .ignore_then(expr_parser.clone())
            .then(block_parser.clone().map_with_span(|b, s| (b, s)))
            .then(
                just(Token::Else)
                    .ignore_then(block_parser.clone().map_with_span(|b, s| (b, s)))
                    .or_not(),
            )
            .map_with_span(|((condition, body), else_opt), span| {
                Statement::Expression(Box::new((
                    Expression::If(If {
                        condition: Box::new(condition),
                        body: Box::new((Expression::Block(body.0), body.1)),
                        else_body: else_opt.map(|b| Box::new((Expression::Block(b.0), b.1))),
                    }),
                    span,
                )))
            }),
        // while <expr> { <block> }
        just(Token::While)
            .ignore_then(expr_parser.clone())
            .then(block_parser.clone().map_with_span(|b, s| (b, s)))
            .map_with_span(|(condition, body), span| {
                Statement::Expression(Box::new((
                    Expression::While(While {
                        condition: Box::new(condition),
                        body: Box::new((Expression::Block(body.0), body.1)),
                    }),
                    span,
                )))
            }),
        // expression ;
        expr_parser
            .clone()
            .then_ignore(just(Token::Semicolon))
            .map(|expr| Statement::Expression(Box::new(expr))),
        // comment
        comment_parser().map(|c| Statement::Comment(c)),
    ))
    .then_ignore(just(Token::Semicolon).repeated())
}

fn expression_parser<'input>(
) -> impl Parser<Token<'input>, Spanned<Expression<'input>>, Error = Simple<Token<'input>>> {
    // Recursive parser for expressions
    recursive(
        |expr: Recursive<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>>>| {
            let literal: BoxedParser<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>, _>> =
                choice((
                    filter_map(|span, token| match token {
                        Token::Integer(n) => {
                            Ok(Expression::Literal(Literal::Integer(n.parse().unwrap())))
                        }
                        Token::BoolLiteral(b) => {
                            Ok(Expression::Literal(Literal::Bool(b == "true")))
                        }
                        _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
                    }),
                    filter_map(|span, token| match token {
                        Token::StrLit(s) => Ok(Expression::String(ASTString { value: s })),
                        _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
                    }),
                ))
                .map_with_span(|e, s| (e, s))
                .boxed();

            let variable: BoxedParser<
                '_,
                Token<'_>,
                Spanned<Expression<'_>>,
                Simple<Token<'_>, _>,
            > = filter_map(|span: Span, token| match token {
                Token::Identifier(ident) => Ok((
                    Expression::Variable(Variable {
                        name: ident,
                        span: span.clone(),
                    }),
                    span,
                )),
                _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
            })
            .boxed();

            let paren_expr = just(Token::LParen)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::RParen))
                .boxed();

            let block_expr: BoxedParser<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>>> =
                block_parser(expr.clone())
                    .map_with_span(|b, span| (Expression::Block(b), span))
                    .boxed();

            let if_expr: BoxedParser<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>>> =
                just(Token::If)
                    .ignore_then(expr.clone())
                    .then(block_parser(expr.clone()).map_with_span(|b, s| (b, s)))
                    .then(
                        just(Token::Else)
                            .ignore_then(block_parser(expr.clone()).map_with_span(|b, s| (b, s)))
                            .or_not(),
                    )
                    .map_with_span(|((condition, body), else_opt), span| {
                        (
                            Expression::If(If {
                                condition: Box::new(condition),
                                body: Box::new((Expression::Block(body.0), body.1)),
                                else_body: else_opt
                                    .map(|b| Box::new((Expression::Block(b.0), b.1))),
                            }),
                            span,
                        )
                    })
                    .boxed();

            let func_call: BoxedParser<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>>> =
                identifier_parser()
                    .then_ignore(just(Token::LParen))
                    .then(
                        expr.clone()
                            .separated_by(just(Token::Comma))
                            .allow_trailing(),
                    )
                    .then_ignore(just(Token::RParen))
                    .map_with_span(|(name, args), span| {
                        (Expression::FunctionCall(FunctionCall { name, args }), span)
                    })
                    .boxed();

            let atom = choice((
                func_call, literal, paren_expr, variable, block_expr, if_expr,
            ))
            .boxed();

            let unary_ops: BoxedParser<'_, Token<'_>, Spanned<Expression<'_>>, Simple<Token<'_>>> =
                choice((
                    just(Token::Plus).to(Opcode::Add),
                    just(Token::Minus).to(Opcode::Sub),
                    just(Token::Exclam).to(Opcode::Not),
                ))
                .repeated()
                .clone()
                .then(atom.clone())
                .foldr(|op, expr| (Expression::UnaryOp(op, Box::new(expr)), 0..0))
                .boxed();

            let factor = unary_ops
                .clone()
                .then(
                    choice((
                        just(Token::Star).to(Opcode::Mul),
                        just(Token::Slash).to(Opcode::Div),
                        just(Token::Percent).to(Opcode::Mod),
                    ))
                    .then(atom.clone())
                    .repeated(),
                )
                .foldl(|lhs, (op, rhs)| {
                    (
                        Expression::Op(Op {
                            lhs: Box::new(lhs),
                            op,
                            rhs: Box::new(rhs),
                        }),
                        0..0,
                    )
                });

            let expr_ops = factor
                .clone()
                .then(
                    choice((
                        just(Token::Plus).to(Opcode::Add),
                        just(Token::Minus).to(Opcode::Sub),
                    ))
                    .then(factor)
                    .repeated(),
                )
                .foldl(|lhs, (op, rhs)| {
                    (
                        Expression::Op(Op {
                            lhs: Box::new(lhs),
                            op,
                            rhs: Box::new(rhs),
                            // span: span,
                        }),
                        0..0,
                    )
                });

            let comp_ops = expr_ops
                .clone()
                .then(
                    choice((
                        just(Token::Eq).to(Opcode::Eq),
                        just(Token::Ne).to(Opcode::Ne),
                        just(Token::Le).to(Opcode::Le),
                        just(Token::Lt).to(Opcode::Lt),
                        just(Token::Ge).to(Opcode::Ge),
                        just(Token::Gt).to(Opcode::Gt),
                        just(Token::Assign).to(Opcode::Assign),
                    ))
                    .then(expr_ops)
                    .repeated(),
                )
                .foldl(|lhs, (op, rhs)| {
                    (
                        Expression::Op(Op {
                            lhs: Box::new(lhs),
                            op,
                            rhs: Box::new(rhs),
                        }),
                        0..0,
                    )
                });

            comp_ops
        },
    )
}

// Simple helper to parse identifiers from the Token stream.
fn identifier_parser<'input>(
) -> impl Parser<Token<'input>, &'input str, Error = Simple<Token<'input>>> {
    filter_map(|span, token| match token {
        Token::Identifier(s) => Ok(s),
        _ => Err(Simple::expected_input_found(
            span,
            vec![Some(Token::Identifier(""))],
            Some(token),
        )),
    })
}

// Putting it all together
pub fn parse_program(src: &str) -> Result<Program, Vec<Simple<Token<'_>>>> {
    // 1) Lex the input to tokens
    // Create a logos lexer over the source code
    let token_iter = Token::lexer(src)
        .spanned()
        // Convert logos errors into tokens. We want parsing to be recoverable and not fail at the lexing stage, so
        // we have a dedicated `Token::Error` variant that represents a token error that was previously encountered
        .map(|(tok, span)| match tok {
            // Turn the `Range<usize>` spans logos gives us into chumsky's `SimpleSpan` via `Into`, because it's easier
            // to work with
            Ok(tok) => (tok, span.into()),
            Err(()) => (Token::Error, span.into()),
        });
    // Turn the token iterator into a stream that chumsky can use for things like backtracking
    let token_stream = chumsky::Stream::from_iter(src.len()..src.len(), token_iter);

    // 2) Parse the tokens into an AST
    let now = std::time::Instant::now();
    let parser = parser();
    println!("Parser created in {:?}", now.elapsed());
    let now = std::time::Instant::now();
    let res = parser.parse(token_stream).map_err(|errs| {
        // Convert token-based errors back to char-based errors
        errs.into_iter()
            .map(|e| Simple::expected_input_found(e.span(), vec![], e.found().cloned()))
            .collect()
    });
    println!("Parsed in {:?}", now.elapsed());
    res
}
