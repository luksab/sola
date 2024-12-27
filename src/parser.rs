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
    expr_parser: impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Program<'input>, Error = Simple<Token<'input>>> {
    top_level_parser(expr_parser)
        .repeated()
        .map(|things| Program { things })
        .then_ignore(end())
}

fn top_level_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>>
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
    expr_parser: impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Function<'input>, Error = Simple<Token<'input>>> {
    // {extern} fn <identifier> ( <params> ) -> <type> { ... }
    let extern_fn = just(Token::Extern)
        .then_ignore(just(Token::Fn))
        .ignore_then(function_definition_parser())
        .map(|definition| Function {
            definition,
            body: None,
        });

    extern_fn.or(just(Token::Fn)
        .ignore_then(function_definition_parser())
        .then(block_parser(expr_parser))
        .map(|(definition, body)| Function {
            definition,
            body: Some(Box::new(Expression::Block(body))),
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
        .map(|(name, tipe)| Parameter { name, tipe })
}

fn type_parser<'input>() -> impl Parser<Token<'input>, Type<'input>, Error = Simple<Token<'input>>>
{
    choice((
        just(Token::TypeI32).to(Type::I32),
        just(Token::TypeBool).to(Type::Bool),
    ))
}

fn block_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>>
        + Clone
        + 'input,
) -> impl Parser<Token<'input>, Block<'input>, Error = Simple<Token<'input>>> {
    // { <statements> <expr>? }
    just(Token::LBrace)
        .ignore_then(statement_parser(expr_parser.clone()).repeated())
        .then(
            expr_parser
                .clone()
                .or_not()
                .map(|opt_expr| opt_expr.map(Box::new)),
        )
        .then_ignore(just(Token::RBrace))
        .map(|(statements, ret_expr)| Block {
            statements,
            return_value: ret_expr.map(|b| *b),
        })
}

fn statement_parser<'input>(
    expr_parser: impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>>
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
            .map(|expr| Statement::Return(expr)),
        // expression ;
        expr_parser
            .clone()
            .then_ignore(just(Token::Semicolon))
            .map(|expr| Statement::Expression(Box::new(*expr))),
        // comment
        comment_parser().map(|c| Statement::Comment(c)),
    ))
}

fn expression_parser<'input>(
) -> impl Parser<Token<'input>, Box<Expression<'input>>, Error = Simple<Token<'input>>> {
    // Recursive parser for expressions
    recursive(|expr| {
        let literal = choice((
            filter_map(|span, token| match token {
                Token::Integer(n) => Ok(Expression::Literal(Literal::Integer(n.parse().unwrap()))),
                Token::BoolLiteral(b) => Ok(Expression::Literal(Literal::Bool(b == "true"))),
                _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
            }),
            filter_map(|span, token| match token {
                Token::StrLit(s) => Ok(Expression::String(ASTString { value: s })),
                _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
            }),
        ))
        .boxed();

        let variable = filter_map(|span, token| match token {
            Token::Identifier(ident) => Ok(Expression::Variable(Variable { name: ident })),
            _ => Err(Simple::expected_input_found(span, vec![], Some(token))),
        })
        .boxed();

        let paren_expr = just(Token::LParen)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map(|e: Box<Expression<'_>>| *e)
            .boxed();

        let block_expr = block_parser(expr.clone()).map(Expression::Block).boxed();

        let if_expr = just(Token::If)
            .ignore_then(expr.clone())
            .then(block_parser(expr.clone()))
            .then(
                just(Token::Else)
                    .ignore_then(block_parser(expr.clone()))
                    .or_not(),
            )
            .map(|((condition, body), else_opt)| {
                Expression::If(If {
                    condition,
                    body: Box::new(Expression::Block(body)),
                    else_body: else_opt.map(|b| Box::new(Expression::Block(b))),
                })
            })
            .boxed();

        let while_expr = just(Token::While)
            .ignore_then(expr.clone())
            .then(block_parser(expr.clone()))
            .map(|(condition, body)| {
                Expression::While(While {
                    condition,
                    body: Box::new(Expression::Block(body)),
                })
            })
            .boxed();

        let func_call = identifier_parser()
            .then_ignore(just(Token::LParen))
            .then(
                expr.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing(),
            )
            .then_ignore(just(Token::RParen))
            .map(|(name, args)| Expression::FunctionCall(FunctionCall { name, args }))
            .boxed();

        let atom = choice((
            func_call, literal, paren_expr, variable, block_expr, if_expr, while_expr,
        ))
        .boxed()
        .map(Box::new);

        let factor = atom
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
            .foldl(|lhs, (op, rhs)| Box::new(Expression::Op(lhs, op, rhs)));

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
            .foldl(|lhs, (op, rhs)| Box::new(Expression::Op(lhs, op, rhs)));

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
            .foldl(|lhs, (op, rhs)| Box::new(Expression::Op(lhs, op, rhs)));

        comp_ops
    })
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
    parser().parse(token_stream).map_err(|errs| {
        // Convert token-based errors back to char-based errors
        errs.into_iter()
            .map(|e| Simple::expected_input_found(e.span(), vec![], e.found().cloned()))
            .collect()
    })
}
