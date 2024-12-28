use colored::Colorize;
use std::{
    fmt::{Debug, Display, Error},
    num::ParseIntError,
    ops::Range,
};

use crate::formatter::{Format, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolaParseError {
    NumberError(ParseIntError),
}

impl Display for SolaParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::SolaParseError::*;
        match *self {
            NumberError(ref e) => write!(fmt, "Number error: {}", e),
        }
    }
}

pub type Spanned<T> = (T, Range<usize>);

#[derive(Debug)]
pub struct Program<'input> {
    pub things: Vec<TopLevel<'input>>,
}

#[derive(Debug)]
pub enum TopLevel<'input> {
    Function(Function<'input>),
    Comment(Comment<'input>),
}

#[derive(Debug)]
pub struct Comment<'input> {
    pub text: &'input str,
}

impl<'input> Comment<'input> {
    pub fn new(text: &'input str) -> Self {
        // remove the // from the start of the comment
        let text = &text[2..];
        // remove any whitespace from the start of the comment
        let text = text.trim_start();
        Self { text }
    }
}

// function -------------------------------------------------------------------

pub type Span = Range<usize>;

#[derive(Debug)]
pub struct Function<'input> {
    pub definition: Spanned<FunctionDefinition<'input>>,
    pub body: Option<Box<Spanned<Expression<'input>>>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FunctionDefinition<'input> {
    pub name: &'input str,
    pub params: Vec<Parameter<'input>>,
    pub return_type: Option<Type<'input>>,
}

#[derive(Debug)]
pub struct Parameter<'input> {
    pub name: &'input str,
    pub tipe: Type<'input>,
    pub span: Span,
}

impl Display for Parameter<'_> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{}: {}", self.name, self.tipe)
    }
}

// statements -----------------------------------------------------------------

#[derive(Debug)]
pub enum Statement<'input> {
    Let(Let<'input>),
    Expression(Box<Spanned<Expression<'input>>>),
    Return(Option<Box<Spanned<Expression<'input>>>>),
    Comment(Comment<'input>),
    Error,
}

#[derive(Debug)]
pub struct Let<'input> {
    pub name: &'input str,
    pub tipe: Type<'input>,
    pub value: Spanned<Expression<'input>>,
}

impl Format for Let<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str_indented("let ");
        fmt.push_str(self.name);
        fmt.push_str(" = ");
        self.value.0.format(fmt);
        fmt.push_str(";\n");
    }
}

#[derive(Debug)]
pub struct FunctionCall<'input> {
    pub name: &'input str,
    pub args: Vec<Spanned<Expression<'input>>>,
}

#[derive(Debug)]
pub struct While<'input> {
    pub condition: Box<Spanned<Expression<'input>>>,
    pub body: Box<Spanned<Expression<'input>>>,
}

// expressions ----------------------------------------------------------------

#[derive(Debug)]
pub enum Expression<'input> {
    Block(Block<'input>),
    While(While<'input>),
    FunctionCall(FunctionCall<'input>),
    Variable(Variable<'input>),
    Literal(Literal<'input>),
    String(ASTString<'input>),
    If(If<'input>),
    Op(Op<'input>),
    UnaryOp(Opcode, Box<Spanned<Expression<'input>>>),
    ExpressionComment((Box<Spanned<Expression<'input>>>, Comment<'input>)),
    Error,
}

#[derive(Debug)]
pub struct Op<'input> {
    pub lhs: Box<Spanned<Expression<'input>>>,
    pub op: Opcode,
    pub rhs: Box<Spanned<Expression<'input>>>,
    // pub span: Range<usize>,
}

#[derive(Debug)]
pub enum Literal<'input> {
    Integer(i32),
    Bool(bool),
    String(&'input str),
}

#[derive(Debug)]
pub struct Block<'input> {
    pub statements: Vec<Statement<'input>>,
    pub return_value: Option<Box<Spanned<Expression<'input>>>>,
}

#[derive(Debug)]
pub struct Variable<'input> {
    pub name: &'input str,
    pub span: Span,
}

impl Display for Variable<'_> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{}", self.name)
    }
}

#[derive(Debug)]
pub struct ASTString<'input> {
    pub value: &'input str,
}

impl<'input> Display for ASTString<'input> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
        write!(fmt, "{}", self.value)
    }
}

#[derive(Debug)]
pub struct If<'input> {
    pub condition: Box<Spanned<Expression<'input>>>,
    pub body: Box<Spanned<Expression<'input>>>,
    pub else_body: Option<Box<Spanned<Expression<'input>>>>,
}

// types ----------------------------------------------------------------------
#[derive(Debug, Clone, Copy)]
pub enum Type<'input> {
    I32,
    Bool,
    Custom(&'input str),
}

impl Display for Type<'_> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::Type::*;
        match *self {
            I32 => write!(fmt, "i32"),
            Bool => write!(fmt, "bool"),
            Custom(name) => write!(fmt, "{}", name),
        }
    }
}

// math -----------------------------------------------------------------------

pub enum ExprSymbol<'input> {
    NumSymbol(&'input str),
    Op(Box<ExprSymbol<'input>>, Opcode, Box<ExprSymbol<'input>>),
    Error,
}

#[derive(Copy, Clone)]
pub enum Opcode {
    Assign,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Not,
}

impl<'input> Debug for ExprSymbol<'input> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::ExprSymbol::*;
        match *self {
            NumSymbol(n) => write!(fmt, "{:?}", n),
            Op(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
            Error => write!(fmt, "{}", "error".red()),
        }
    }
}

impl Debug for Opcode {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::Opcode::*;
        match *self {
            Assign => write!(fmt, "="),
            Mul => write!(fmt, "*"),
            Div => write!(fmt, "/"),
            Mod => write!(fmt, "%"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
            Lt => write!(fmt, "<"),
            Le => write!(fmt, "<="),
            Gt => write!(fmt, ">"),
            Ge => write!(fmt, ">="),
            Not => write!(fmt, "!"),
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::Opcode::*;
        match *self {
            Assign => write!(fmt, "="),
            Mul => write!(fmt, "*"),
            Div => write!(fmt, "/"),
            Mod => write!(fmt, "%"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
            Lt => write!(fmt, "<"),
            Le => write!(fmt, "<="),
            Gt => write!(fmt, ">"),
            Ge => write!(fmt, ">="),
            Not => write!(fmt, "!"),
        }
    }
}
