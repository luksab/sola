use colored::Colorize;
use std::fmt::{Debug, Display, Error};

use crate::formatter::{Format, Formatter};

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

#[derive(Debug)]
pub struct Function<'input> {
    pub definition: FunctionDefinition<'input>,
    pub body: Box<Expression<'input>>,
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
    Expression(Box<Expression<'input>>),
    Return(Box<Expression<'input>>),
    Comment(Comment<'input>),
    Error,
}

#[derive(Debug)]
pub struct Let<'input> {
    pub name: &'input str,
    pub value: Box<Expression<'input>>,
}

impl Format for Let<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str_indented("let ");
        fmt.push_str(self.name);
        fmt.push_str(" = ");
        self.value.format(fmt);
        fmt.push_str(";\n");
    }
}

#[derive(Debug)]
pub struct FunctionCall<'input> {
    pub name: &'input str,
    pub args: Vec<Box<Expression<'input>>>,
}

// expressions ----------------------------------------------------------------

#[derive(Debug)]
pub enum Expression<'input> {
    Expression(Box<Expression<'input>>),
    Block(Vec<Statement<'input>>),
    FunctionCall(FunctionCall<'input>),
    Variable(Variable<'input>),
    Number(i32),
    String(ASTString<'input>),
    If(If<'input>),
    Op(Box<Expression<'input>>, Opcode, Box<Expression<'input>>),
    ExpressionComment((Box<Expression<'input>>, Comment<'input>)),
    Error,
}

#[derive(Debug)]
pub struct Variable<'input> {
    pub name: &'input str,
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
    pub condition: Box<Expression<'input>>,
    pub body: Box<Expression<'input>>,
    pub else_body: Option<Box<Expression<'input>>>,
}

// types ----------------------------------------------------------------------
#[derive(Debug)]
pub enum Type<'input> {
    I32,
    Custom(&'input str),
}

impl Display for Type<'_> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::Type::*;
        match *self {
            I32 => write!(fmt, "i32"),
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
    Mul,
    Div,
    Add,
    Sub,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
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
            Mul => write!(fmt, "*"),
            Div => write!(fmt, "/"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
            Lt => write!(fmt, "<"),
            Le => write!(fmt, "<="),
            Gt => write!(fmt, ">"),
            Ge => write!(fmt, ">="),
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), Error> {
        use self::Opcode::*;
        match *self {
            Mul => write!(fmt, "*"),
            Div => write!(fmt, "/"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
            Lt => write!(fmt, "<"),
            Le => write!(fmt, "<="),
            Gt => write!(fmt, ">"),
            Ge => write!(fmt, ">="),
        }
    }
}
