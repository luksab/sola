//! resolve variables and types in base_ast

use id_collections::{id_type, IdVec};
use ustr::ustr;
use ustr::Ustr;

use crate::base_ast::Spanned;
use crate::base_ast::{self, Span};
use std::cmp::Ordering;
use std::fmt::Display;

pub fn resolve(program: &base_ast::Program) -> Program {
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

#[id_type]
pub struct VariableId(u32);

#[id_type]
pub struct FunctionId(u32);

// #[derive(Clone)]
// pub struct PossibleTypes {
//     pub types: Vec<Type>,
// }

// impl PossibleTypes {
//     fn new_empty() -> Self {
//         PossibleTypes { types: Vec::new() }
//     }

//     fn new_single(tipe: Type) -> Self {
//         PossibleTypes { types: vec![tipe] }
//     }

//     fn new_floats() -> Self {
//         PossibleTypes {
//             types: vec![Type::Float(FloatType::F32), Type::Float(FloatType::F64)],
//         }
//     }

//     fn new_ints_and_floats() -> Self {
//         PossibleTypes {
//             types: vec![
//                 Type::Int(IntegerType::I8),
//                 Type::Int(IntegerType::U8),
//                 Type::Int(IntegerType::I16),
//                 Type::Int(IntegerType::U16),
//                 Type::Int(IntegerType::I32),
//                 Type::Int(IntegerType::U32),
//                 Type::Int(IntegerType::I64),
//                 Type::Int(IntegerType::U64),
//                 Type::Int(IntegerType::I128),
//                 Type::Int(IntegerType::U128),
//                 Type::Float(FloatType::F32),
//                 Type::Float(FloatType::F64),
//             ],
//         }
//     }
// }

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Int(IntegerType),
    Bool,
    Float(FloatType),
    // Struct(StructType),
    // Enum(EnumType),
    Pointer(Box<Type>),
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Type::Float(_), Type::Int(_)) => Some(Ordering::Greater),
            (Type::Int(_), Type::Float(_)) => Some(Ordering::Less),
            (Type::Float(lhs), Type::Float(rhs)) => lhs.partial_cmp(rhs),
            (Type::Int(lhs), Type::Int(rhs)) => lhs.partial_cmp(rhs),
            (Type::Bool, Type::Bool) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl PartialOrd for IntegerType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use IntegerType::*;

        let rank = |int_type: &IntegerType| match int_type {
            I8 => (true, 1),
            U8 => (false, 1),
            I16 => (true, 2),
            U16 => (false, 2),
            I32 => (true, 3),
            U32 => (false, 3),
            I64 => (true, 4),
            U64 => (false, 4),
            I128 => (true, 5),
            U128 => (false, 5),
        };

        match (rank(self), rank(other)) {
            ((signed1, rank1), (signed2, rank2)) => {
                if signed1 == signed2 {
                    rank1.partial_cmp(&rank2)
                } else if signed1 {
                    if rank1 > rank2 {
                        Some(Ordering::Greater)
                    } else if rank1 < rank2 {
                        Some(Ordering::Less)
                    } else {
                        None
                    }
                } else {
                    if rank1 > rank2 {
                        Some(Ordering::Less)
                    } else if rank1 < rank2 {
                        Some(Ordering::Greater)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

impl PartialOrd for FloatType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use FloatType::*;

        let rank = |float_type: &FloatType| match float_type {
            F32 => 1,
            F64 => 2,
        };

        rank(self).partial_cmp(&rank(other))
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
    fn resolve(_resolver: &mut Resolver, tipe: &base_ast::Type<'_>) -> Type {
        match tipe {
            base_ast::Type::I8 => Type::Int(IntegerType::I8),
            base_ast::Type::U8 => Type::Int(IntegerType::U8),
            base_ast::Type::I16 => Type::Int(IntegerType::I16),
            base_ast::Type::U16 => Type::Int(IntegerType::U16),
            base_ast::Type::I32 => Type::Int(IntegerType::I32),
            base_ast::Type::U32 => Type::Int(IntegerType::U32),
            base_ast::Type::I64 => Type::Int(IntegerType::I64),
            base_ast::Type::U64 => Type::Int(IntegerType::U64),
            base_ast::Type::I128 => Type::Int(IntegerType::I128),
            base_ast::Type::U128 => Type::Int(IntegerType::U128),
            base_ast::Type::Bool => Type::Bool,
            base_ast::Type::F32 => Type::Float(FloatType::F32),
            base_ast::Type::F64 => Type::Float(FloatType::F64),
            base_ast::Type::Custom(_) => unimplemented!(),
        }
    }
}

pub struct Program {
    pub things: Vec<TopLevel>,
    pub resolver: Resolver,
}
impl Program {
    fn resolve(program: &base_ast::Program<'_>) -> Program {
        let mut resolver = Resolver::default();

        let mut things = Vec::new();
        for top_level in &program.things {
            match top_level {
                base_ast::TopLevel::Function(function) => {
                    things.push(TopLevel::Function(Function::resolve(
                        &mut resolver,
                        function,
                    )));
                }
                base_ast::TopLevel::Comment(_) => {}
            }
        }
        Program { things, resolver }
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
    fn resolve(resolver: &mut Resolver, function: &base_ast::Function<'_>) -> FunctionId {
        resolver.scope.push(vec![]);
        let definition = FunctionDefinition::resolve(resolver, &function.definition);
        let body = function
            .body
            .as_ref()
            .map(|body| Expression::resolve(resolver, (&body.0, body.1.clone())));

        resolver.scope.pop();

        resolver.all_functions.push(Function {
            definition,
            body,
            span: function.span.clone(),
        })
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
    ) -> Self {
        let span = definition.1.clone();
        let definition = &definition.0;
        let name = ustr(definition.name);
        let params = definition
            .params
            .iter()
            .map(|param| Variable::add_param(resolver, param))
            .collect();
        let return_type = definition
            .return_type
            .map(|tipe| Type::resolve(resolver, &tipe));

        FunctionDefinition {
            name,
            params,
            return_type,
            span,
        }
    }
}

pub struct Variable {
    pub name: Ustr,
    pub type_: Type,
    pub span: Span,
}
impl Variable {
    fn add_param(resolver: &mut Resolver, variable: &base_ast::Parameter<'_>) -> VariableId {
        let span = variable.span.clone();
        let name = ustr(variable.name);
        let type_ = Type::resolve(resolver, &variable.tipe);
        let var = Variable { name, type_, span };
        let slf = resolver.all_variables.push(var);
        resolver.scope.last_mut().unwrap().push(slf);
        slf
    }

    fn add_var(resolver: &mut Resolver, variable: &base_ast::Let<'_>) -> VariableId {
        let span = variable.value.1.clone();
        let name = ustr(variable.name);
        let type_ = Type::resolve(resolver, &variable.tipe);
        let var = Variable { name, type_, span };
        let slf = resolver.all_variables.push(var);
        resolver.scope.last_mut().unwrap().push(slf);
        slf
    }

    fn resolve_var(resolver: &mut Resolver, var: &base_ast::Variable<'_>) -> VariableId {
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
            .unwrap_or_else(|| {
                panic!("variable {} not found in scope", name);
            })
    }
}

pub struct Block {
    pub statements: Vec<Statement>,
    pub return_value: Option<Box<Expression>>,
    pub span: Span,
}
impl Block {
    fn resolve(resolver: &mut Resolver, block: Spanned<&base_ast::Block<'_>>) -> Block {
        resolver.scope.push(vec![]);

        let (block, span) = block;
        let statements = block
            .statements
            .iter()
            .map(|statement| Statement::resolve(resolver, statement))
            .collect();
        let return_value = block
            .return_value
            .as_ref()
            .map(|expr| Box::new(Expression::resolve(resolver, (&expr.0, expr.1.clone()))));

        resolver.scope.pop();

        Block {
            statements,
            return_value,
            span,
        }
    }
}

pub struct Expression {
    pub expression: InnerExpression,
    pub return_type: Option<Type>,
    pub span: Span,
}

pub enum InnerExpression {
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
    ) -> Expression {
        let span = expression.1.clone();
        match &expression.0 {
            base_ast::Expression::Block(block) => {
                let block = Block::resolve(resolver, (block, span.clone()));
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
                )),
                return_type: None,
                span,
            },
            base_ast::Expression::FunctionCall(call) => {
                let call = FunctionCall::resolve(resolver, (call, span.clone()));
                Expression {
                    return_type: call.return_type.as_ref().map(|tipe| tipe.clone()),
                    expression: InnerExpression::FunctionCall(call),
                    span,
                }
            }
            base_ast::Expression::Variable(var) => {
                let var = Variable::resolve_var(resolver, var);
                Expression {
                    expression: InnerExpression::Variable(var),
                    return_type: Some(resolver.all_variables[var].type_.clone()),
                    span,
                }
            }
            base_ast::Expression::Literal(lit) => Expression {
                expression: InnerExpression::Literal(Literal::resolve(lit)),
                return_type: Some(match lit {
                    base_ast::Literal::Integer(integer, None) => {
                        let integer = *integer;
                        if integer >= i8::MIN as i128 && integer <= i8::MAX as i128 {
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
                        }
                    }
                    base_ast::Literal::Integer(_, Some(type_)) => Type::Int(type_.clone()),
                    base_ast::Literal::Bool(_) => Type::Bool,
                    base_ast::Literal::Float(float, None) => {
                        let float = *float;
                        if float >= f32::MIN as f64 && float <= f32::MAX as f64 {
                            Type::Float(FloatType::F32)
                        } else {
                            Type::Float(FloatType::F64)
                        }
                    }
                    base_ast::Literal::Float(_, Some(type_)) => Type::Float(type_.clone()),
                    base_ast::Literal::String(_) => unimplemented!(),
                }),
                span,
            },
            base_ast::Expression::If(if_) => {
                let if_ = If::resolve(resolver, (if_, span.clone()));
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
                let op = Op::resolve(resolver, (op, span.clone()));
                Expression {
                    return_type: Some(op.return_type.clone()),
                    expression: InnerExpression::Op(op),
                    span,
                }
            }
            base_ast::Expression::UnaryOp(op, expr) => {
                let expr = Box::new(Expression::resolve(resolver, (&expr.0, expr.1.clone())));
                Expression {
                    return_type: expr.return_type.clone(),
                    expression: InnerExpression::UnaryOp(*op, expr),
                    span,
                }
            }

            base_ast::Expression::Error | base_ast::Expression::ExpressionComment(_) => {
                unimplemented!("I think I should handle this error in an earlier pass")
            }
        }
    }
}

pub struct While {
    pub condition: Box<Expression>,
    pub body: Box<Expression>,
    pub span: Span,
}
impl While {
    fn resolve(resolver: &mut Resolver, while_: Spanned<&base_ast::While<'_>>) -> While {
        let (while_, span) = while_;
        let (condition_expr, condition_span) = &*while_.condition;
        let condition = Box::new(Expression::resolve(
            resolver,
            (condition_expr, condition_span.clone()),
        ));
        let (body_expr, body_span) = &*while_.body;
        let body = Box::new(Expression::resolve(
            resolver,
            (&body_expr, body_span.clone()),
        ));

        While {
            condition,
            body,
            span: span.clone(),
        }
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
    ) -> FunctionCall {
        let (call, span) = span;
        let function = resolver
            .all_functions
            .iter()
            .find(|(_, function)| function.definition.name == ustr(call.name))
            .map(|(id, _)| id)
            .unwrap_or_else(|| {
                panic!("function {} not found", call.name);
            });
        let args: Vec<_> = call
            .args
            .iter()
            .map(|arg| Expression::resolve(resolver, (&arg.0, arg.1.clone())))
            .collect();

        let return_type = resolver.all_functions[function]
            .definition
            .return_type
            .clone();

        FunctionCall {
            function,
            args,
            return_type,
            span: span.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Integer(i128),
    Bool(bool),
    Float(f64),
    String(String),
}
impl Literal {
    fn resolve(lit: &base_ast::Literal<'_>) -> Literal {
        match lit {
            base_ast::Literal::Integer(num, _) => Literal::Integer(*num),
            base_ast::Literal::Bool(b) => Literal::Bool(*b),
            base_ast::Literal::Float(num, _) => Literal::Float(*num),
            base_ast::Literal::String(s) => Literal::String(s.to_string()),
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
    fn resolve(resolver: &mut Resolver, span: (&base_ast::If<'_>, std::ops::Range<usize>)) -> If {
        let (if_, span) = span;
        let (condition_expr, condition_span) = &*if_.condition;
        let condition = Box::new(Expression::resolve(
            resolver,
            (condition_expr, condition_span.clone()),
        ));
        let (body_expr, body_span) = &*if_.body;
        let body = Box::new(Expression::resolve(
            resolver,
            (&body_expr, body_span.clone()),
        ));
        let else_body = if_.else_body.as_ref().map(|else_| {
            let (else_expr, else_span) = &**else_;
            Box::new(Expression::resolve(
                resolver,
                (&else_expr, else_span.clone()),
            ))
        });

        If {
            condition,
            body,
            else_body,
            span: span.clone(),
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
    fn resolve(resolver: &mut Resolver, span: (&base_ast::Op<'_>, std::ops::Range<usize>)) -> Op {
        let (op, span) = span;
        let (lhs_expr, lhs_span) = &*op.lhs;
        let lhs = Box::new(Expression::resolve(resolver, (lhs_expr, lhs_span.clone())));
        let (rhs_expr, rhs_span) = &*op.rhs;
        let rhs = Box::new(Expression::resolve(resolver, (rhs_expr, rhs_span.clone())));

        let return_type = match op.op {
            base_ast::Opcode::Add
            | base_ast::Opcode::Sub
            | base_ast::Opcode::Mul
            | base_ast::Opcode::Div => {
                // delete all types that are lower than the other one's type
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                match lhs_type.partial_cmp(&rhs_type) {
                    Some(Ordering::Greater) => lhs_type,
                    Some(Ordering::Less) => rhs_type,
                    Some(Ordering::Equal) => lhs_type,
                    None => unimplemented!("This should use a type inference system"),
                }
            }
            base_ast::Opcode::Assign => {
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                if lhs_type >= rhs_type {
                    lhs_type
                } else {
                    println!("lhs: {:?}, rhs: {:?}", lhs_type, rhs_type);
                    unimplemented!("This should be a type error")
                }
            }
            base_ast::Opcode::Mod => {
                let lhs_type = lhs.return_type.clone().unwrap();
                let rhs_type = rhs.return_type.clone().unwrap();
                if matches!(lhs_type, Type::Int(_) | Type::Float(_))
                    && matches!(rhs_type, Type::Int(_))
                {
                    lhs_type
                } else {
                    unimplemented!("This should be a type error")
                }
            }
            base_ast::Opcode::Eq
            | base_ast::Opcode::Ne
            | base_ast::Opcode::Lt
            | base_ast::Opcode::Le
            | base_ast::Opcode::Gt
            | base_ast::Opcode::Ge
            | base_ast::Opcode::Not => Type::Bool,
        };

        Op {
            lhs,
            op: op.op,
            rhs,
            span: span.clone(),
            return_type,
        }
    }
}

pub enum Statement {
    Let(Let),
    Expression(Expression),
    Return(Option<Box<Expression>>),
}

impl Statement {
    fn resolve(resolver: &mut Resolver, statement: &base_ast::Statement<'_>) -> Statement {
        match statement {
            base_ast::Statement::Let(let_) => Statement::Let(Let::resolve(resolver, let_)),
            base_ast::Statement::Expression(expr) => {
                Statement::Expression(Expression::resolve(resolver, (&expr.0, expr.1.clone())))
            }
            base_ast::Statement::Return(expr) => {
                let expr = expr
                    .as_ref()
                    .map(|expr| Box::new(Expression::resolve(resolver, (&expr.0, expr.1.clone()))));
                Statement::Return(expr)
            }
            base_ast::Statement::Comment(_) | base_ast::Statement::Error => {
                unimplemented!("I think I should handle this error in an earlier pass")
            }
        }
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
    fn resolve(resolver: &mut Resolver, let_: &base_ast::Let<'_>) -> Let {
        let name = ustr(let_.name);
        let value = Box::new(Expression::resolve(
            resolver,
            (&let_.value.0, let_.value.1.clone()),
        ));
        let type_ = Type::resolve(resolver, &let_.tipe);

        let id = Variable::add_var(resolver, let_);

        Let {
            name,
            id,
            value,
            type_,
        }
    }
}
