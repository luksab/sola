//! resolve variables and types in base_ast

use id_collections::{id_type, IdVec};
use ustr::ustr;
use ustr::Ustr;

use crate::base_ast::Spanned;
use crate::base_ast::{self, Span};
use crate::helpers::CompilerLocation;
use std::fmt::Display;

pub struct ResolverError {
    pub message: String,
    pub span: Span,
    pub compiler_location: CompilerLocation,
}

type RResult<T> = std::result::Result<T, ResolverError>;

pub fn resolve(program: &base_ast::Program) -> RResult<Program> {
    Program::resolve(program)
}

pub struct Resolver {
    pub all_variables: IdVec<VariableId, Variable>,
    pub scope: Vec<Vec<VariableId>>,
    pub all_functions: IdVec<FunctionId, Function>,
}

impl Default for Resolver {
    fn default() -> Self {
        Resolver {
            all_variables: IdVec::new(),
            scope: Vec::new(),
            all_functions: IdVec::new(),
        }
    }
}

pub struct ResolverPrinter {
    pub indent: usize,
}

impl ResolverPrinter {
    pub fn new() -> Self {
        ResolverPrinter { indent: 0 }
    }

    pub fn print(&mut self, resolver: &Resolver) {
        let functions: Vec<_> = resolver.all_functions.iter().collect();
        for (_id, function) in functions {
            function.print(self, resolver);
        }
    }

    fn print_indent(&self) {
        print!("{}", "    ".repeat(self.indent));
    }
}

#[id_type]
pub struct VariableId(u32);

#[id_type]
pub struct FunctionId(u32);

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Int(IntegerType),
    Bool,
    Float(FloatType),
    // Struct(StructType),
    // Enum(EnumType),
    Pointer(Box<Type>),
}

impl Display for Type {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Type::Int(int) => write!(fmt, "{}", int),
            Type::Bool => write!(fmt, "bool"),
            Type::Float(float) => write!(fmt, "{}", float),
            Type::Pointer(tipe) => write!(fmt, "*{}", tipe),
        }
    }
}

impl Type {
    pub fn can_convert_to(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Type::Int(lhs), Type::Int(rhs)) => lhs.can_convert_to(rhs),
            (Type::Float(lhs), Type::Float(rhs)) => lhs.can_convert_to(rhs),
            (Type::Int(_), Type::Float(_)) => true,
            _ => false,
        }
    }
}

impl IntegerType {
    fn can_convert_to(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        use IntegerType::*;

        match (self, other) {
            (I8, I16) | (I8, I32) | (I8, I64) | (I8, I128) => true,
            (U8, I16) | (U8, I32) | (U8, I64) | (U8, I128) => true,
            (U8, U16) | (U8, U32) | (U8, U64) | (U8, U128) => true,
            (I16, I32) | (I16, I64) | (I16, I128) => true,
            (U16, I32) | (U16, I64) | (U16, I128) => true,
            (U16, U32) | (U16, U64) | (U16, U128) => true,
            (I32, I64) | (I32, I128) => true,
            (U32, I64) | (U32, I128) => true,
            (U32, U64) | (U32, U128) => true,
            (I64, I128) => true,
            (U64, I128) => true,
            _ => false,
        }
    }
}

impl FloatType {
    fn can_convert_to(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        use FloatType::*;

        match (self, other) {
            (F32, F64) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum IntegerType {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    I128,
    U128,
}

impl Display for IntegerType {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        use IntegerType::*;
        write!(
            fmt,
            "{}",
            match self {
                I8 => "i8",
                U8 => "u8",
                I16 => "i16",
                U16 => "u16",
                I32 => "i32",
                U32 => "u32",
                I64 => "i64",
                U64 => "u64",
                I128 => "i128",
                U128 => "u128",
            }
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FloatType {
    F32,
    F64,
}

impl Display for FloatType {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        use FloatType::*;
        write!(
            fmt,
            "{}",
            match self {
                F32 => "f32",
                F64 => "f64",
            }
        )
    }
}

impl Type {
    fn resolve(_resolver: &mut Resolver, tipe: Spanned<&base_ast::Type<'_>>) -> RResult<Type> {
        match tipe.0 {
            base_ast::Type::I8 => Ok(Type::Int(IntegerType::I8)),
            base_ast::Type::U8 => Ok(Type::Int(IntegerType::U8)),
            base_ast::Type::I16 => Ok(Type::Int(IntegerType::I16)),
            base_ast::Type::U16 => Ok(Type::Int(IntegerType::U16)),
            base_ast::Type::I32 => Ok(Type::Int(IntegerType::I32)),
            base_ast::Type::U32 => Ok(Type::Int(IntegerType::U32)),
            base_ast::Type::I64 => Ok(Type::Int(IntegerType::I64)),
            base_ast::Type::U64 => Ok(Type::Int(IntegerType::U64)),
            base_ast::Type::I128 => Ok(Type::Int(IntegerType::I128)),
            base_ast::Type::U128 => Ok(Type::Int(IntegerType::U128)),
            base_ast::Type::Bool => Ok(Type::Bool),
            base_ast::Type::F32 => Ok(Type::Float(FloatType::F32)),
            base_ast::Type::F64 => Ok(Type::Float(FloatType::F64)),
            base_ast::Type::Custom(name) => Err(ResolverError {
                message: format!("custom types are not supported yet: {}", name),
                span: tipe.1.clone(),
                compiler_location: compiler_location!(),
            }),
        }
    }
}

pub struct Program {
    pub things: Vec<TopLevel>,
    pub resolver: Resolver,
}
impl Program {
    fn resolve(program: &base_ast::Program<'_>) -> RResult<Program> {
        let mut resolver = Resolver::default();

        let mut things = Vec::new();
        for top_level in &program.things {
            match top_level {
                base_ast::TopLevel::Function(function) => {
                    things.push(TopLevel::Function(Function::resolve(
                        &mut resolver,
                        function,
                    )?));
                }
                base_ast::TopLevel::Comment(_) => {}
            }
        }
        Ok(Program { things, resolver })
    }

    pub fn print(&self) {
        let mut printer = ResolverPrinter::new();
        printer.print(&self.resolver);
    }
}

pub enum TopLevel {
    Function(FunctionId),
    // Import(Import),
    // Struct(Struct),
    // Enum(Enum),
    // GlobalVariable(GlobalVariable),
}

pub struct Function {
    pub definition: FunctionDefinition,
    pub body: Option<Expression>,
    pub span: Span,
}
impl Function {
    fn resolve(resolver: &mut Resolver, function: &base_ast::Function<'_>) -> RResult<FunctionId> {
        resolver.scope.push(vec![]);
        let definition = FunctionDefinition::resolve(resolver, &function.definition)?;
        let mut body = function
            .body
            .as_ref()
            .map(|body| Expression::resolve(resolver, (&body.0, body.1.clone())))
            .transpose()?;

        resolver.scope.pop();

        if body.is_some() {
            let body_return_type = &body.as_ref().unwrap().return_type;
            let definition_return_type = &definition.return_type;
            match (body_return_type, definition_return_type) {
                (None, Some(_)) => {
                    return Err(ResolverError {
                        message: format!(
                            "function {} should return something, but it doesn't",
                            definition.name
                        ),
                        span: function.span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
                (Some(_), None) => {
                    return Err(ResolverError {
                        message: format!(
                            "function {} should not return anything, but it does",
                            definition.name
                        ),
                        span: function.span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
                (Some(body_ret), Some(def_ret)) if body_ret != def_ret => {
                    if body_ret.can_convert_to(def_ret) {
                        // cast the return type
                        body = Some(Expression {
                            span: body.as_ref().unwrap().span.clone(),
                            expression: InnerExpression::Cast(
                                def_ret.clone(),
                                Box::new(body.unwrap()),
                            ),
                            return_type: Some(def_ret.clone()),
                        });
                    } else {
                        return Err(ResolverError {
                            message: format!(
                                "function {} has a body with a return type of {} but the function's return type is {}",
                                definition.name,
                                body_ret,
                                def_ret
                            ),
                            span: function.span.clone(),
                            compiler_location: compiler_location!()
                        });
                    }
                }
                _ => {
                    // everything is fine. Either the function doesn't return anything or the return types match
                }
            }
        }

        Ok(resolver.all_functions.push(Function {
            definition,
            body,
            span: function.span.clone(),
        }))
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        printer.print_indent();
        print!("fn {}(", self.definition.name);
        printer.indent += 1;
        for param in &self.definition.params {
            let var = &resolver.all_variables[*param];
            print!("{}: {}", var.name, var.type_);
        }
        printer.indent -= 1;
        print!(
            ") -> {}",
            self.definition
                .return_type
                .as_ref()
                .map(|tipe| tipe.to_string())
                .unwrap_or("void".to_string())
        );
        if let Some(body) = &self.body {
            print!(" ");
            body.print(printer, resolver);
            println!();
        } else {
            println!(";");
        }
    }
}

pub struct FunctionDefinition {
    pub name: Ustr,
    pub params: Vec<VariableId>,
    pub return_type: Option<Type>,
    pub span: Span,
}
impl FunctionDefinition {
    fn resolve(
        resolver: &mut Resolver,
        definition: &(base_ast::FunctionDefinition<'_>, std::ops::Range<usize>),
    ) -> RResult<Self> {
        let span = definition.1.clone();
        let definition = &definition.0;
        let name = ustr(definition.name);
        let params = definition
            .params
            .iter()
            .map(|param| Variable::add_param(resolver, param))
            .collect::<RResult<_>>()?;
        let return_type = definition
            .return_type
            .map(|tipe| Type::resolve(resolver, (&tipe, span.clone())))
            .transpose()?;

        Ok(FunctionDefinition {
            name,
            params,
            return_type,
            span,
        })
    }
}

pub struct Variable {
    pub name: Ustr,
    pub type_: Type,
    pub span: Span,
}
impl Variable {
    fn add_param(
        resolver: &mut Resolver,
        variable: &base_ast::Parameter<'_>,
    ) -> RResult<VariableId> {
        let span = variable.span.clone();
        let name = ustr(variable.name);
        let type_ = Type::resolve(resolver, (&variable.tipe, span.clone()))?;
        let var = Variable { name, type_, span };
        let slf = resolver.all_variables.push(var);
        resolver.scope.last_mut().unwrap().push(slf);
        Ok(slf)
    }

    fn add_var(resolver: &mut Resolver, variable: &base_ast::Let<'_>) -> RResult<VariableId> {
        let span = variable.value.1.clone();
        let name = ustr(variable.name);
        let type_ = Type::resolve(resolver, (&variable.tipe, span.clone()))?;
        let var = Variable { name, type_, span };
        let slf = resolver.all_variables.push(var);
        resolver.scope.last_mut().unwrap().push(slf);
        Ok(slf)
    }

    fn resolve_var(resolver: &mut Resolver, var: &base_ast::Variable<'_>) -> RResult<VariableId> {
        let name = ustr(var.name);
        // look for the variable in the scopes
        resolver
            .scope
            .iter()
            .rev()
            .find_map(|scope| {
                scope
                    .iter()
                    .find(|id| resolver.all_variables[*id].name == name)
            })
            .copied()
            .ok_or_else(|| ResolverError {
                message: format!("variable {} not found in scope", name),
                span: var.span.clone(),
                compiler_location: compiler_location!(),
            })
    }
}

pub struct Block {
    pub statements: Vec<Statement>,
    pub return_value: Option<Box<Expression>>,
    pub span: Span,
}
impl Block {
    fn resolve(resolver: &mut Resolver, block: Spanned<&base_ast::Block<'_>>) -> RResult<Block> {
        resolver.scope.push(vec![]);

        let (block, span) = block;
        let statements = block
            .statements
            .iter()
            .flat_map(|statement| Statement::resolve(resolver, statement).transpose())
            .collect::<RResult<_>>()?;
        let return_value = if let Some(expr) = &block.return_value {
            Some(Box::new(Expression::resolve(
                resolver,
                (&expr.0, expr.1.clone()),
            )?))
        } else {
            None
        };

        resolver.scope.pop();

        Ok(Block {
            statements,
            return_value,
            span,
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        println!("{{");
        printer.indent += 1;
        for statement in &self.statements {
            statement.print(printer, resolver);
        }
        if let Some(return_value) = &self.return_value {
            printer.print_indent();
            return_value.print(printer, resolver);
            println!("");
        }
        printer.indent -= 1;
        printer.print_indent();
        print!("}}");
    }
}

pub struct Expression {
    pub expression: InnerExpression,
    pub return_type: Option<Type>,
    pub span: Span,
}

impl Expression {
    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        match &self.expression {
            InnerExpression::Block(block) => {
                block.print(printer, resolver);
            }
            InnerExpression::While(while_) => {
                while_.print(printer, resolver);
            }
            InnerExpression::FunctionCall(call) => {
                call.print(printer, resolver);
            }
            InnerExpression::Variable(var) => {
                let var = &resolver.all_variables[*var];
                print!("{}", var.name);
            }
            InnerExpression::Literal(lit) => {
                print!("{}{}", lit.inner, lit.type_);
            }
            InnerExpression::If(if_) => {
                if_.print(printer, resolver);
            }
            InnerExpression::Op(op) => {
                op.print(printer, resolver);
            }
            InnerExpression::UnaryOp(op, expr) => {
                print!("{:?}", op);
                expr.print(printer, resolver);
            }
            InnerExpression::Cast(tipe, expr) => {
                print!("(");
                expr.print(printer, resolver);
                print!(") as {}", tipe);
            }
        }
    }
}

pub enum InnerExpression {
    Cast(Type, Box<Expression>),
    Block(Block),
    While(While),
    FunctionCall(FunctionCall),
    Variable(VariableId),
    Literal(Literal),
    If(If),
    Op(Op),
    UnaryOp(base_ast::Opcode, Box<Expression>),
}

impl Expression {
    fn resolve(
        resolver: &mut Resolver,
        expression: Spanned<&base_ast::Expression<'_>>,
    ) -> RResult<Expression> {
        let span = expression.1.clone();
        Ok(match &expression.0 {
            base_ast::Expression::Block(block) => {
                let block = Block::resolve(resolver, (block, span.clone()))?;
                Expression {
                    return_type: block
                        .return_value
                        .as_ref()
                        .and_then(|val| val.return_type.clone()),
                    expression: InnerExpression::Block(block),
                    span,
                }
            }
            base_ast::Expression::While(while_) => Expression {
                expression: InnerExpression::While(While::resolve(
                    resolver,
                    (while_, span.clone()),
                )?),
                return_type: None,
                span,
            },
            base_ast::Expression::FunctionCall(call) => {
                let call = FunctionCall::resolve(resolver, (call, span.clone()))?;
                Expression {
                    return_type: call.return_type.as_ref().map(|tipe| tipe.clone()),
                    expression: InnerExpression::FunctionCall(call),
                    span,
                }
            }
            base_ast::Expression::Variable(var) => {
                let var = Variable::resolve_var(resolver, var)?;
                Expression {
                    expression: InnerExpression::Variable(var),
                    return_type: Some(resolver.all_variables[var].type_.clone()),
                    span,
                }
            }
            base_ast::Expression::Literal(lit) => {
                let resolved_literal = Literal::resolve(lit)?;
                Expression {
                    return_type: Some(resolved_literal.type_.clone()),
                    expression: InnerExpression::Literal(resolved_literal),
                    span,
                }
            }
            base_ast::Expression::If(if_) => {
                let if_ = If::resolve(resolver, (if_, span.clone()))?;
                Expression {
                    return_type: if_
                        .else_body
                        .as_ref()
                        .and_then(|else_| else_.return_type.clone()),
                    expression: InnerExpression::If(if_),
                    span,
                }
            }
            base_ast::Expression::Op(op) => {
                let op = Op::resolve(resolver, (op, span.clone()))?;
                Expression {
                    return_type: Some(op.return_type.clone()),
                    expression: InnerExpression::Op(op),
                    span,
                }
            }
            base_ast::Expression::UnaryOp(op, expr) => {
                let expr = Box::new(Expression::resolve(resolver, (&expr.0, expr.1.clone()))?);
                Expression {
                    return_type: expr.return_type.clone(),
                    expression: InnerExpression::UnaryOp(*op, expr),
                    span,
                }
            }

            base_ast::Expression::Error | base_ast::Expression::ExpressionComment(_) => {
                unimplemented!("I think I should handle this error in an earlier pass")
            }
        })
    }
}

pub struct While {
    pub condition: Box<Expression>,
    pub body: Box<Expression>,
    pub span: Span,
}
impl While {
    fn resolve(resolver: &mut Resolver, while_: Spanned<&base_ast::While<'_>>) -> RResult<While> {
        let (while_, span) = while_;
        let (condition_expr, condition_span) = &*while_.condition;
        let condition = Box::new(Expression::resolve(
            resolver,
            (condition_expr, condition_span.clone()),
        )?);
        let (body_expr, body_span) = &*while_.body;
        let body = Box::new(Expression::resolve(
            resolver,
            (&body_expr, body_span.clone()),
        )?);

        Ok(While {
            condition,
            body,
            span: span.clone(),
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        print!("while (");
        self.condition.print(printer, resolver);
        print!(") ");
        self.body.print(printer, resolver);
    }
}

pub struct FunctionCall {
    pub function: FunctionId,
    pub args: Vec<Expression>,
    pub return_type: Option<Type>,
    pub span: Span,
}
impl FunctionCall {
    fn resolve(
        resolver: &mut Resolver,
        span: (&base_ast::FunctionCall<'_>, std::ops::Range<usize>),
    ) -> RResult<FunctionCall> {
        let (call, span) = span;
        let function_id = resolver
            .all_functions
            .iter()
            .find(|(_, function)| function.definition.name == ustr(call.name))
            .map(|(id, _)| id)
            .ok_or_else(|| ResolverError {
                message: format!("function {} not found", call.name),
                span: span.clone(),
                compiler_location: compiler_location!(),
            })?;
        let function_definition = &resolver.all_functions[function_id].definition;
        let return_type = function_definition.return_type.clone();

        let mut args = Vec::new();

        for (i, arg) in call.args.iter().enumerate() {
            let mut arg = Expression::resolve(resolver, (&arg.0, arg.1.clone()))?;
            let param = resolver.all_functions[function_id]
                .definition
                .params
                .get(i)
                .unwrap();
            let param = &resolver.all_variables[param];
            if arg.return_type != Some(param.type_.clone()) {
                if arg
                    .return_type
                    .as_ref()
                    .unwrap()
                    .can_convert_to(&param.type_)
                {
                    arg = Expression {
                        span: arg.span.clone(),
                        expression: InnerExpression::Cast(param.type_.clone(), Box::new(arg)),
                        return_type: Some(param.type_.clone()),
                    };
                } else {
                    return Err(ResolverError {
                        message: format!(
                            "argument {} should be of type {} but it is of type {}",
                            i,
                            param.type_,
                            arg.return_type.as_ref().unwrap()
                        ),
                        span: arg.span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
            }
            args.push(arg);
        }

        Ok(FunctionCall {
            function: function_id,
            args,
            return_type,
            span: span.clone(),
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        let function = &resolver.all_functions[self.function];
        print!("{}(", function.definition.name);
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                print!(", ");
            }
            arg.print(printer, resolver);
        }
        print!(")");
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Literal {
    pub inner: InnerLiteral,
    pub type_: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum InnerLiteral {
    Integer(i128),
    Bool(bool),
    Float(f64),
    String(String),
}
impl Literal {
    fn resolve(lit: &base_ast::Literal<'_>) -> RResult<Literal> {
        match lit {
            base_ast::Literal::Integer(integer, None) => {
                let integer = *integer;
                let type_ = if integer >= i8::MIN as i128 && integer <= i8::MAX as i128 {
                    Type::Int(IntegerType::I8)
                } else if integer >= u8::MIN as i128 && integer <= u8::MAX as i128 {
                    Type::Int(IntegerType::U8)
                } else if integer >= i16::MIN as i128 && integer <= i16::MAX as i128 {
                    Type::Int(IntegerType::I16)
                } else if integer >= u16::MIN as i128 && integer <= u16::MAX as i128 {
                    Type::Int(IntegerType::U16)
                } else if integer >= i32::MIN as i128 && integer <= i32::MAX as i128 {
                    Type::Int(IntegerType::I32)
                } else if integer >= u32::MIN as i128 && integer <= u32::MAX as i128 {
                    Type::Int(IntegerType::U32)
                } else if integer >= i64::MIN as i128 && integer <= i64::MAX as i128 {
                    Type::Int(IntegerType::I64)
                } else if integer >= u64::MIN as i128 && integer <= u64::MAX as i128 {
                    Type::Int(IntegerType::U64)
                } else if integer >= i128::MIN as i128 && integer <= i128::MAX as i128 {
                    Type::Int(IntegerType::I128)
                } else {
                    Type::Int(IntegerType::U128)
                };

                Ok(Literal {
                    inner: InnerLiteral::Integer(integer),
                    type_,
                })
            }
            base_ast::Literal::Integer(num, Some(type_)) => Ok(Literal {
                inner: InnerLiteral::Integer(*num),
                type_: Type::Int(type_.clone()),
            }),
            base_ast::Literal::Bool(b) => Ok(Literal {
                inner: InnerLiteral::Bool(*b),
                type_: Type::Bool,
            }),
            base_ast::Literal::Float(float, None) => {
                let float = *float;
                let type_ = if float >= f32::MIN as f64 && float <= f32::MAX as f64 {
                    Type::Float(FloatType::F32)
                } else {
                    Type::Float(FloatType::F64)
                };

                Ok(Literal {
                    inner: InnerLiteral::Float(float),
                    type_,
                })
            }
            base_ast::Literal::Float(num, Some(type_)) => Ok(Literal {
                inner: InnerLiteral::Float(*num),
                type_: Type::Float(type_.clone()),
            }),
            base_ast::Literal::String(_) => unimplemented!(),
        }
    }
}

impl Display for InnerLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match &self {
            InnerLiteral::Integer(num) => write!(f, "{}", num),
            InnerLiteral::Bool(b) => write!(f, "{}", b),
            InnerLiteral::Float(num) => write!(f, "{}", num),
            InnerLiteral::String(s) => write!(f, "\"{}\"", s),
        }
    }
}

pub struct If {
    pub condition: Box<Expression>,
    pub body: Box<Expression>,
    pub else_body: Option<Box<Expression>>,
    pub span: Span,
}
impl If {
    fn resolve(
        resolver: &mut Resolver,
        span: (&base_ast::If<'_>, std::ops::Range<usize>),
    ) -> RResult<If> {
        let (if_, span) = span;
        let (condition_expr, condition_span) = &*if_.condition;
        let condition = Box::new(Expression::resolve(
            resolver,
            (condition_expr, condition_span.clone()),
        )?);
        let (body_expr, body_span) = &*if_.body;
        let body = Box::new(Expression::resolve(
            resolver,
            (&body_expr, body_span.clone()),
        )?);
        let else_body = if_
            .else_body
            .as_ref()
            .map(|else_| {
                let (else_expr, else_span) = &**else_;
                Expression::resolve(resolver, (&else_expr, else_span.clone()))
            })
            .transpose()?
            .map(Box::new);

        Ok(If {
            condition,
            body,
            else_body,
            span: span.clone(),
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        print!("if (");
        self.condition.print(printer, resolver);
        print!(") ");
        self.body.print(printer, resolver);
        if let Some(else_body) = &self.else_body {
            print!(" else ");
            else_body.print(printer, resolver);
        }
    }
}

pub struct Op {
    pub lhs: Box<Expression>,
    pub op: base_ast::Opcode,
    pub rhs: Box<Expression>,
    pub return_type: Type,
    pub span: Span,
}
impl Op {
    fn resolve(
        resolver: &mut Resolver,
        span: (&base_ast::Op<'_>, std::ops::Range<usize>),
    ) -> RResult<Op> {
        let (op, span) = span;
        let (lhs_expr, lhs_span) = &*op.lhs;
        let mut lhs = Box::new(Expression::resolve(resolver, (lhs_expr, lhs_span.clone()))?);
        let (rhs_expr, rhs_span) = &*op.rhs;
        let mut rhs = Box::new(Expression::resolve(resolver, (rhs_expr, rhs_span.clone()))?);

        let return_type = match op.op {
            base_ast::Opcode::Add
            | base_ast::Opcode::Sub
            | base_ast::Opcode::Mul
            | base_ast::Opcode::Div
            | base_ast::Opcode::Mod => {
                // delete all types that are lower than the other one's type
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                if lhs_type == rhs_type {
                    lhs_type
                } else if lhs_type.can_convert_to(&rhs_type) {
                    // cast lhs to rhs
                    lhs = Box::new(Expression {
                        expression: InnerExpression::Cast(rhs_type.clone(), lhs),
                        return_type: Some(rhs_type.clone()),
                        span: lhs_span.clone(),
                    });
                    rhs_type
                } else if rhs_type.can_convert_to(&lhs_type) {
                    // cast rhs to lhs
                    rhs = Box::new(Expression {
                        expression: InnerExpression::Cast(lhs_type.clone(), rhs),
                        return_type: Some(lhs_type.clone()),
                        span: rhs_span.clone(),
                    });
                    lhs_type
                } else {
                    return Err(ResolverError {
                        message: format!(
                            "Cant apply operator \"{}\" to types {:?} and {:?}",
                            op.op, lhs.return_type, rhs.return_type
                        ),
                        span: span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
            }
            base_ast::Opcode::Assign => {
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                if lhs_type == rhs_type {
                    lhs_type
                } else if rhs_type.can_convert_to(&lhs_type) {
                    // cast rhs to lhs
                    rhs = Box::new(Expression {
                        expression: InnerExpression::Cast(lhs_type.clone(), rhs),
                        return_type: Some(lhs_type.clone()),
                        span: rhs_span.clone(),
                    });
                    lhs_type
                } else {
                    return Err(ResolverError {
                        message: format!(
                            "Cant assign type {:?} to variable of type {:?}",
                            rhs_type, lhs_type
                        ),
                        span: span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
            }
            base_ast::Opcode::Eq
            | base_ast::Opcode::Ne
            | base_ast::Opcode::Lt
            | base_ast::Opcode::Le
            | base_ast::Opcode::Gt
            | base_ast::Opcode::Ge
            | base_ast::Opcode::Not => {
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                if lhs_type == rhs_type {
                    Type::Bool
                } else if lhs_type.can_convert_to(&rhs_type) {
                    // cast lhs to rhs
                    lhs = Box::new(Expression {
                        expression: InnerExpression::Cast(rhs_type.clone(), lhs),
                        return_type: Some(rhs_type.clone()),
                        span: lhs_span.clone(),
                    });
                    Type::Bool
                } else if rhs_type.can_convert_to(&lhs_type) {
                    // cast rhs to lhs
                    rhs = Box::new(Expression {
                        expression: InnerExpression::Cast(lhs_type.clone(), rhs),
                        return_type: Some(lhs_type.clone()),
                        span: rhs_span.clone(),
                    });
                    Type::Bool
                } else {
                    return Err(ResolverError {
                        message: format!(
                            "Cant compare types {:?} and {:?}",
                            lhs.return_type, rhs.return_type
                        ),
                        span: span.clone(),
                        compiler_location: compiler_location!(),
                    });
                }
            }
        };

        Ok(Op {
            lhs,
            op: op.op,
            rhs,
            span: span.clone(),
            return_type,
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        self.lhs.print(printer, resolver);
        print!(" {} ", self.op);
        self.rhs.print(printer, resolver);
    }
}

pub enum Statement {
    Let(Let),
    Expression(Expression),
    Return(Option<Box<Expression>>),
}

impl Statement {
    fn resolve(
        resolver: &mut Resolver,
        statement: &base_ast::Statement<'_>,
    ) -> RResult<Option<Statement>> {
        match statement {
            base_ast::Statement::Let(let_) => {
                Ok(Some(Statement::Let(Let::resolve(resolver, let_)?)))
            }
            base_ast::Statement::Expression(expr) => Ok(Some(Statement::Expression(
                Expression::resolve(resolver, (&expr.0, expr.1.clone()))?,
            ))),
            base_ast::Statement::Return(expr) => {
                let expr = expr
                    .as_ref()
                    .map(|expr| Expression::resolve(resolver, (&expr.0, expr.1.clone())))
                    .transpose()?;
                let expr = expr.map(Box::new);
                Ok(Some(Statement::Return(expr)))
            }
            base_ast::Statement::Comment(_) => Ok(None),
            base_ast::Statement::Error => {
                unimplemented!("I think I should handle this error in an earlier pass")
            }
        }
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        printer.print_indent();
        match self {
            Statement::Let(let_) => {
                let_.print(printer, resolver);
            }
            Statement::Expression(expr) => {
                expr.print(printer, resolver);
            }
            Statement::Return(expr) => {
                print!("return ");
                if let Some(expr) = expr {
                    expr.print(printer, resolver);
                }
            }
        }
        println!(";");
    }
}

pub struct Let {
    pub name: Ustr,
    pub id: VariableId,
    pub value: Box<Expression>,
    pub type_: Type,
    // pub span: Span,
}

impl Let {
    fn resolve(resolver: &mut Resolver, let_: &base_ast::Let<'_>) -> RResult<Let> {
        let name = ustr(let_.name);
        let mut value = Box::new(Expression::resolve(
            resolver,
            (&let_.value.0, let_.value.1.clone()),
        )?);
        let type_ = Type::resolve(resolver, (&let_.tipe, let_.value.1.clone()))?;

        if value.return_type.is_none() {
            return Err(ResolverError {
                message: "you can't assign nothing to a variable".to_string(),
                span: let_.value.1.clone(),
                compiler_location: compiler_location!(),
            });
        } else if value.return_type.as_ref().unwrap().can_convert_to(&type_) {
            // cast value to type_
            value = Box::new(Expression {
                expression: InnerExpression::Cast(type_.clone(), value),
                return_type: Some(type_.clone()),
                span: let_.value.1.clone(),
            });
        } else if !type_.can_convert_to(value.return_type.as_ref().unwrap()) {
            return Err(ResolverError {
                message: format!(
                    "variable {} should be of type {} but it is of type {}",
                    name,
                    type_,
                    value.return_type.as_ref().unwrap()
                ),
                span: let_.value.1.clone(),
                compiler_location: compiler_location!(),
            });
        }

        let id = Variable::add_var(resolver, let_)?;

        Ok(Let {
            name,
            id,
            value,
            type_,
        })
    }

    fn print(&self, printer: &mut ResolverPrinter, resolver: &Resolver) {
        print!("let {}: {} = ", self.name, self.type_);
        self.value.print(printer, resolver);
    }
}
