use std::collections::HashMap;

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    types::BasicMetadataTypeEnum,
    values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};
use ustr::Ustr;

use crate::resolver::{
    self, Expression, FloatType, Function, FunctionDefinition, InnerExpression, Program, Resolver,
    Statement, TopLevel, Type,
};
use crate::{base_ast::Span, resolver::IntegerType};

pub struct CompileError {
    pub message: String,
    pub span: Span,
}

pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,

    resolver: &'a Resolver,

    variables: HashMap<Ustr, (PointerValue<'ctx>, Type)>,
    fn_value_opt: Option<FunctionValue<'ctx>>,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    /// Gets a defined function given its name.
    #[inline]
    fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    /// Returns the `FunctionValue` representing the function being compiled.
    #[inline]
    fn fn_value(&self) -> FunctionValue<'ctx> {
        self.fn_value_opt.unwrap()
    }

    /// Creates a new stack allocation instruction in the entry block of the function.
    fn create_entry_block_alloca(&self, name: &str, tipe: &Type) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.fn_value().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        match tipe {
            Type::Int(IntegerType::I8 | IntegerType::U8) => {
                builder.build_alloca(self.context.i8_type(), name).unwrap()
            }
            Type::Int(IntegerType::I16 | IntegerType::U16) => {
                builder.build_alloca(self.context.i16_type(), name).unwrap()
            }
            Type::Int(IntegerType::I32 | IntegerType::U32) => {
                builder.build_alloca(self.context.i32_type(), name).unwrap()
            }
            Type::Int(IntegerType::I64 | IntegerType::U64) => {
                builder.build_alloca(self.context.i64_type(), name).unwrap()
            }
            Type::Int(IntegerType::I128 | IntegerType::U128) => builder
                .build_alloca(self.context.i128_type(), name)
                .unwrap(),
            Type::Float(FloatType::F32) => {
                builder.build_alloca(self.context.f32_type(), name).unwrap()
            }
            Type::Float(FloatType::F64) => {
                builder.build_alloca(self.context.f64_type(), name).unwrap()
            }
            Type::Bool => builder
                .build_alloca(self.context.bool_type(), name)
                .unwrap(),
            _ => unimplemented!(),
        }
    }

    pub fn build_load(
        &self,
        ptr: PointerValue<'ctx>,
        name: &str,
        tipe: Type,
    ) -> BasicValueEnum<'ctx> {
        match tipe {
            Type::Int(IntegerType::I8 | IntegerType::U8) => self
                .builder
                .build_load(self.context.i8_type(), ptr, name)
                .unwrap(),
            Type::Int(IntegerType::I16 | IntegerType::U16) => self
                .builder
                .build_load(self.context.i16_type(), ptr, name)
                .unwrap(),
            Type::Int(IntegerType::I32 | IntegerType::U32) => self
                .builder
                .build_load(self.context.i32_type(), ptr, name)
                .unwrap(),
            Type::Int(IntegerType::I64 | IntegerType::U64) => self
                .builder
                .build_load(self.context.i64_type(), ptr, name)
                .unwrap(),
            Type::Int(IntegerType::I128 | IntegerType::U128) => self
                .builder
                .build_load(self.context.i128_type(), ptr, name)
                .unwrap(),
            Type::Float(FloatType::F32) => self
                .builder
                .build_load(self.context.f32_type(), ptr, name)
                .unwrap(),
            Type::Float(FloatType::F64) => self
                .builder
                .build_load(self.context.f64_type(), ptr, name)
                .unwrap(),
            Type::Bool => self
                .builder
                .build_load(self.context.bool_type(), ptr, name)
                .unwrap(),
            _ => unimplemented!(),
        }
    }

    /// Compiles the specified `Function` in the given `Context` and using the specified `Builder` and `Module`.
    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
        program: &'a Program,
    ) -> Result<(), CompileError> {
        // let context = Context::create();
        // let module = context.create_module("ret");
        // let builder = context.create_builder();
        // let i32_type = context.i32_type();
        // let arg_types = [i32_type.into()];
        // let fn_type = i32_type.fn_type(&arg_types, false);
        // let fn_value = module.add_function("ret", fn_type, None);
        // let entry = context.append_basic_block(fn_value, "entry");
        // let i32_arg = fn_value.get_first_param().unwrap();

        // builder.position_at_end(entry);
        // builder.build_return(Some(&i32_arg)).unwrap();

        // println!("{}", module.print_to_string().to_string());
        // return Err("Not implemented".to_string())
        let resolver = &program.resolver;
        let mut compiler = Compiler {
            context,
            builder,
            module,
            resolver,
            fn_value_opt: None,
            variables: HashMap::new(),
        };

        compiler.compile_program(program)
    }

    fn compile_program(&mut self, program: &Program) -> Result<(), CompileError> {
        for thing in &program.things {
            match thing {
                TopLevel::Function(function) => {
                    let function = &self.resolver.all_functions[function];
                    self.compile_function(function)?;
                }
            }
        }

        Ok(())
    }

    fn compile_function(
        &mut self,
        function: &Function,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let function_val = self.compile_fn_definition(&function.definition)?;

        // got external function, returning only compiled prototype
        if function.body.is_none() {
            return Ok(function_val);
        }

        let entry = self.context.append_basic_block(function_val, "entry");

        self.builder.position_at_end(entry);

        // update fn field
        self.fn_value_opt = Some(function_val);

        // build variables map
        self.variables.reserve(function.definition.params.len());

        for (i, arg) in function_val.get_param_iter().enumerate() {
            let resolved_variable = &self.resolver.all_variables[function.definition.params[i]];
            let arg_name = resolved_variable.name;
            let alloca = self.create_entry_block_alloca(&arg_name, &resolved_variable.type_);

            self.builder.build_store(alloca, arg).unwrap();

            self.variables
                .insert(arg_name, (alloca, resolved_variable.type_.clone()));
        }

        // compile body
        let body = self.compile_expr(
            function
                .body
                .as_ref()
                .expect("We should have returned earlier if this was None"),
        )?;

        self.builder
            .build_return(body.as_ref().map(|b| b as &dyn BasicValue))
            .unwrap();

        // return the whole thing after verification and optimization
        if function_val.verify(true) {
            Ok(function_val)
        } else {
            // println to stderr to add a newline after the error message from LLVM
            eprintln!();
            unsafe {
                function_val.delete();
            }

            Err(CompileError {
                message: "Invalid generated function.".to_string(),
                span: function.span.clone(), // Replace with the appropriate span
            })
        }
    }

    fn compile_fn_definition(
        &self,
        proto: &FunctionDefinition,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let args_types = proto
            .params
            .iter()
            .map(|f| {
                let resolved_variable = &self.resolver.all_variables[f];
                match resolved_variable.type_ {
                    resolver::Type::Int(IntegerType::I8 | IntegerType::U8) => {
                        Ok(self.context.i8_type().into())
                    }
                    resolver::Type::Int(IntegerType::I16 | IntegerType::U16) => {
                        Ok(self.context.i16_type().into())
                    }
                    resolver::Type::Int(IntegerType::I32 | IntegerType::U32) => {
                        Ok(self.context.i32_type().into())
                    }
                    resolver::Type::Int(IntegerType::I64 | IntegerType::U64) => {
                        Ok(self.context.i64_type().into())
                    }
                    resolver::Type::Int(IntegerType::I128 | IntegerType::U128) => {
                        Ok(self.context.i128_type().into())
                    }
                    resolver::Type::Float(FloatType::F32) => Ok(self.context.f32_type().into()),
                    resolver::Type::Float(FloatType::F64) => Ok(self.context.f64_type().into()),
                    resolver::Type::Bool => Ok(self.context.bool_type().into()),
                    _ => Err(CompileError {
                        message: "Unsupported argument type.".to_string(),
                        span: resolved_variable.span.clone(),
                    }),
                }
            })
            .collect::<Result<Vec<BasicMetadataTypeEnum>, CompileError>>()?;
        let args_types = args_types.as_slice();

        let fn_type = match proto.return_type {
            Some(Type::Int(IntegerType::I8) | Type::Int(IntegerType::U8)) => {
                self.context.i8_type().fn_type(args_types, false)
            }
            Some(Type::Int(IntegerType::I16) | Type::Int(IntegerType::U16)) => {
                self.context.i16_type().fn_type(args_types, false)
            }
            Some(Type::Int(IntegerType::I32) | Type::Int(IntegerType::U32)) => {
                self.context.i32_type().fn_type(args_types, false)
            }
            Some(Type::Int(IntegerType::I64) | Type::Int(IntegerType::U64)) => {
                self.context.i64_type().fn_type(args_types, false)
            }
            Some(Type::Int(IntegerType::I128) | Type::Int(IntegerType::U128)) => {
                self.context.i128_type().fn_type(args_types, false)
            }
            Some(Type::Float(FloatType::F32)) => self.context.f32_type().fn_type(args_types, false),
            Some(Type::Float(FloatType::F64)) => self.context.f64_type().fn_type(args_types, false),
            Some(Type::Bool) => self.context.bool_type().fn_type(args_types, false),
            None => self.context.void_type().fn_type(args_types, false),
            Some(_) => todo!(),
        };
        let fn_val = self.module.add_function(&proto.name, fn_type, None);

        // set arguments names
        for (i, arg) in fn_val.get_param_iter().enumerate() {
            let resolved_variable = &self.resolver.all_variables[&proto.params[i]];
            match arg {
                BasicValueEnum::IntValue(int_value) => int_value.set_name(&resolved_variable.name),
                BasicValueEnum::ArrayValue(array_value) => {
                    array_value.set_name(&resolved_variable.name)
                }
                BasicValueEnum::FloatValue(float_value) => {
                    float_value.set_name(&resolved_variable.name)
                }
                BasicValueEnum::PointerValue(pointer_value) => {
                    pointer_value.set_name(&resolved_variable.name)
                }
                BasicValueEnum::StructValue(struct_value) => {
                    struct_value.set_name(&resolved_variable.name)
                }
                BasicValueEnum::VectorValue(vector_value) => {
                    vector_value.set_name(&resolved_variable.name)
                }
            }
        }

        // finally return built prototype
        Ok(fn_val)
    }

    fn compile_expr(
        &mut self,
        expression: &Expression,
    ) -> Result<Option<BasicValueEnum<'ctx>>, CompileError> {
        match &expression.expression {
            InnerExpression::Block(block) => {
                for (i, statement) in block.statements.iter().enumerate() {
                    match statement {
                        Statement::Let(let_) => {
                            let alloca = self.create_entry_block_alloca(&let_.name, &let_.type_);
                            let value = self.compile_expr(&let_.value)?;

                            if let Some(value) = value {
                                self.builder.build_store(alloca, value).unwrap();
                                self.variables
                                    .insert(let_.name, (alloca, let_.type_.clone()));
                            } else {
                                return Err(CompileError {
                                    message: "Error compiling let statement. Expression is None."
                                        .to_string(),
                                    span: expression.span.clone(),
                                });
                            }
                        }
                        Statement::Expression(expr) => {
                            self.compile_expr(&expr)?;
                        }
                        Statement::Return(expr) => {
                            // emit warning if there are more statements after return
                            if i < block.statements.len() - 1 {
                                eprintln!("Warning: Unreachable code after return statement.");
                            }
                            // check, if there is a return value
                            if let Some(_return_value) = &block.return_value {
                                eprintln!("Warning: Unreachable code after return statement.");
                            }
                            if let Some(return_value) = expr {
                                return Ok(self.compile_expr(&return_value)?);
                            } else {
                                return Ok(None);
                            }
                        }
                    }
                }

                if let Some(return_value) = &block.return_value {
                    Ok(self.compile_expr(return_value)?)
                } else {
                    Ok(None)
                }
            }
            InnerExpression::FunctionCall(function_call) => {
                let function = &self.resolver.all_functions[function_call.function];
                match self.get_function(&function.definition.name) {
                    Some(fun) => {
                        let compiled_args: Vec<BasicValueEnum> = function_call
                            .args
                            .iter()
                            .map(|arg_expr| {
                                self.compile_expr(arg_expr).and_then(|value| {
                                    value.ok_or_else(|| CompileError {
                                        message: "Error compiling function call. Argument expr doesn't return anything."
                                            .to_string(),
                                        span: expression.span.clone(),
                                    })
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?;

                        let argsv: Vec<BasicMetadataValueEnum> = compiled_args
                            .iter()
                            .by_ref()
                            .map(|&val| val.into())
                            .collect();

                        match self
                            .builder
                            .build_call(fun, argsv.as_slice(), "tmp")
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                        {
                            Some(value) => Ok(Some(value)),
                            None => Ok(None),
                        }
                    }
                    None => Err(CompileError {
                        message: "Unknown function.".to_string(),
                        span: expression.span.clone(),
                    }),
                }
            }
            InnerExpression::Variable(variable_id) => {
                let variable = &self.resolver.all_variables[variable_id];
                match self.variables.get(&variable.name) {
                    Some(var) => Ok(Some(self.build_load(var.0, &variable.name, var.1.clone()))),
                    None => Err(CompileError {
                        message: format!("Undefined variable: {}", variable.name),
                        span: expression.span.clone(),
                    }),
                }
            }
            InnerExpression::Literal(lit) => {
                use resolver::InnerLiteral::*;
                match (&lit.inner, &expression.return_type) {
                    // Integer(num) => Ok(Some(BasicValueEnum::IntValue(
                    //     self.context.i32_type().const_int(*num as u64, false),
                    // ))),
                    // Float(num) => Ok(Some(BasicValueEnum::FloatValue(
                    //     self.context.f64_type().const_float(*num),
                    // ))),
                    // Bool(b) => Ok(Some(BasicValueEnum::IntValue(
                    //     self.context.bool_type().const_int(*b as u64, false),
                    // ))),
                    // String(_) => todo!(),
                    (Integer(num), Some(Type::Int(IntegerType::I8))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i8_type().const_int(*num as u64, false),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::U8))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i8_type().const_int(*num as u64, true),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::I16))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i16_type().const_int(*num as u64, false),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::U16))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i16_type().const_int(*num as u64, true),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::I32))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i32_type().const_int(*num as u64, false),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::U32))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i32_type().const_int(*num as u64, true),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::I64))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i64_type().const_int(*num as u64, false),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::U64))) => {
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context.i64_type().const_int(*num as u64, true),
                        )))
                    }
                    (Integer(num), Some(Type::Int(IntegerType::I128 | IntegerType::U128))) => {
                        let high_bits = (*num >> 64) as u64;
                        let low_bits = *num as u64;
                        Ok(Some(BasicValueEnum::IntValue(
                            self.context
                                .i128_type()
                                .const_int_arbitrary_precision(&[high_bits, low_bits]),
                        )))
                    }

                    (Float(num), Some(Type::Float(FloatType::F32))) => Ok(Some(
                        BasicValueEnum::FloatValue(self.context.f32_type().const_float(*num)),
                    )),
                    (Float(num), Some(Type::Float(FloatType::F64))) => Ok(Some(
                        BasicValueEnum::FloatValue(self.context.f64_type().const_float(*num)),
                    )),

                    (Bool(b), Some(Type::Bool)) => Ok(Some(BasicValueEnum::IntValue(
                        self.context.bool_type().const_int(*b as u64, false),
                    ))),

                    a => todo!("Handle all cases, then throw an error: {:?}", a),
                }
            }
            InnerExpression::If(if_expr) => {
                let (condition, body, else_body) =
                    (&if_expr.condition, &if_expr.body, &if_expr.else_body);
                let parent = self.fn_value();

                // create condition by comparing without 0.0 and returning an int
                let cond = self.compile_expr(condition)?;
                let cond = match cond {
                    Some(BasicValueEnum::FloatValue(float_value)) => self
                        .builder
                        .build_float_compare(
                            inkwell::FloatPredicate::ONE,
                            float_value,
                            self.context.f64_type().const_float(0.0),
                            "if.cond",
                        )
                        .unwrap(),

                    Some(BasicValueEnum::IntValue(int_value)) => self
                        .builder
                        .build_int_compare(
                            inkwell::IntPredicate::NE,
                            int_value,
                            self.context.bool_type().const_int(0, false),
                            "if.cond",
                        )
                        .unwrap(),
                    Some(_) => todo!(),
                    None => todo!(),
                };

                // build branch
                let then_bb = self.context.append_basic_block(parent, "if.then");
                let else_bb = self.context.append_basic_block(parent, "if.else");
                let cont_bb = self.context.append_basic_block(parent, "if.cont");

                self.builder
                    .build_conditional_branch(cond, then_bb, else_bb)
                    .unwrap();

                // build then block
                self.builder.position_at_end(then_bb);
                let then_val = self.compile_expr(body)?;
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                let then_bb = self.builder.get_insert_block().unwrap();

                // build else block
                self.builder.position_at_end(else_bb);
                let else_val = match else_body {
                    Some(else_body) => self.compile_expr(else_body)?,
                    None => None,
                };
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                let else_bb = self.builder.get_insert_block().unwrap();

                // emit merge block
                self.builder.position_at_end(cont_bb);

                match (then_val, else_val) {
                    (Some(then_val), Some(else_val)) => {
                        let phi_type = match (then_val, else_val) {
                            (BasicValueEnum::IntValue(_), BasicValueEnum::IntValue(_)) => {
                                self.context.i32_type()
                            }
                            _ => todo!(),
                        };

                        let phi = self.builder.build_phi(phi_type, "iftmp").unwrap();

                        phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);

                        Ok(Some(phi.as_basic_value()))
                    }
                    _ => Ok(None),
                }
            }
            InnerExpression::While(while_) => {
                let parent = self.fn_value();

                let cond_bb = self.context.append_basic_block(parent, "while.cond");
                let body_bb = self.context.append_basic_block(parent, "while.body");
                let cont_bb = self.context.append_basic_block(parent, "while.cont");

                self.builder.build_unconditional_branch(cond_bb).unwrap();

                // build condition block
                self.builder.position_at_end(cond_bb);
                let cond = self.compile_expr(&while_.condition)?;
                let cond = match cond {
                    Some(BasicValueEnum::FloatValue(float_value)) => self
                        .builder
                        .build_float_compare(
                            inkwell::FloatPredicate::ONE,
                            float_value,
                            self.context.f64_type().const_float(0.0),
                            "while.cond",
                        )
                        .unwrap(),

                    Some(BasicValueEnum::IntValue(int_value)) => self
                        .builder
                        .build_int_compare(
                            inkwell::IntPredicate::NE,
                            int_value,
                            self.context.bool_type().const_int(0, false),
                            "while.cond",
                        )
                        .unwrap(),
                    Some(_) => todo!(),
                    None => todo!(),
                };

                self.builder
                    .build_conditional_branch(cond, body_bb, cont_bb)
                    .unwrap();

                // build body block
                self.builder.position_at_end(body_bb);
                let _ = self.compile_expr(&while_.body)?;
                self.builder.build_unconditional_branch(cond_bb).unwrap();

                // emit merge block
                self.builder.position_at_end(cont_bb);

                Ok(None)
            }
            InnerExpression::Op(op) => {
                let (left, opcode, right) = (&op.lhs, &op.op, &op.rhs);
                let lhs = self
                    .compile_expr(left)?
                    .expect("Left side of binary operation must return a value.");
                let rhs = self
                    .compile_expr(right)?
                    .expect("Right side of binary operation must return a value.");

                use crate::base_ast::Opcode::*;
                match (lhs, rhs) {
                    (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                        match opcode {
                            Add => Ok(Some(BasicValueEnum::IntValue(
                                self.builder.build_int_add(lhs, rhs, "tmpadd").unwrap(),
                            ))),
                            Sub => Ok(Some(BasicValueEnum::IntValue(
                                self.builder.build_int_sub(lhs, rhs, "tmpsub").unwrap(),
                            ))),
                            Mul => Ok(Some(BasicValueEnum::IntValue(
                                self.builder.build_int_mul(lhs, rhs, "tmpmul").unwrap(),
                            ))),
                            Mod => Ok(Some(BasicValueEnum::IntValue(
                                self.builder
                                    .build_int_signed_rem(lhs, rhs, "tmpmod")
                                    .unwrap(),
                            ))),
                            Div => Ok(Some(BasicValueEnum::IntValue(
                                self.builder
                                    .build_int_signed_div(lhs, rhs, "tmpdiv")
                                    .unwrap(),
                            ))),
                            Lt => Ok(Some(BasicValueEnum::IntValue(
                                self.builder
                                    .build_int_compare(
                                        inkwell::IntPredicate::SLT,
                                        lhs,
                                        rhs,
                                        "tmpcmp",
                                    )
                                    .unwrap(),
                            ))),
                            Gt => Ok(Some(BasicValueEnum::IntValue(
                                self.builder
                                    .build_int_compare(
                                        inkwell::IntPredicate::SGT,
                                        lhs,
                                        rhs,
                                        "tmpcmp",
                                    )
                                    .unwrap(),
                            ))),
                            Eq => Ok(Some(BasicValueEnum::IntValue(
                                self.builder
                                    .build_int_compare(
                                        inkwell::IntPredicate::EQ,
                                        lhs,
                                        rhs,
                                        "tmpcmp",
                                    )
                                    .unwrap(),
                            ))),
                            Assign => {
                                // handle assignment
                                let sola_var = match left.expression {
                                    InnerExpression::Variable(ref var_name) => var_name,
                                    _ => return Err(CompileError {
                                        message:
                                            "Expected variable as left-hand operator of assignment."
                                                .to_string(),
                                        span: left.span.clone(),
                                    }),
                                };
                                let sola_var =
                                    self.resolver.all_variables.get(sola_var).expect(
                                        "Variable should have been resolved by the resolver.",
                                    );

                                let var_val = self.compile_expr(right)?;
                                let var =
                                    self.variables.get(&sola_var.name).ok_or(CompileError {
                                        message: format!("Undefined variable: {}", sola_var.name),
                                        span: sola_var.span.clone(),
                                    })?;

                                // check that the types match
                                if sola_var.type_ != *right.return_type.as_ref().unwrap() {
                                    return Err(CompileError {
                                            message: format!(
                                                "Cannot assign value of type {:?} to variable of type {:?}.",
                                                right.return_type.as_ref().unwrap(),
                                                sola_var.type_
                                            ),
                                            span: right.span.clone(),
                                        });
                                }

                                self.builder
                                    .build_store(
                                        var.0,
                                        var_val
                                            .expect("Assignment expression must return a value."),
                                    )
                                    .unwrap();

                                Ok(var_val)
                            }
                            _ => todo!(),
                            // custom => {
                            //     let mut name = String::from("binary");

                            //     name.push(custom);

                            //     match self.get_function(name.as_str()) {
                            //         Some(fun) => {
                            //             match self
                            //                 .builder
                            //                 .build_call(fun, &[lhs.into(), rhs.into()], "tmpbin")
                            //                 .unwrap()
                            //                 .try_as_basic_value()
                            //                 .left()
                            //             {
                            //                 Some(value) => Ok(value.into_float_value()),
                            //                 None => Err("Invalid call produced."),
                            //             }
                            //         }

                            //         None => Err("Undefined binary operator."),
                            //     }
                            // }
                        }
                    }
                    _ => todo!(),
                }
            }
            InnerExpression::UnaryOp(opcode, expr) => {
                let expr = self
                    .compile_expr(&expr)?
                    .expect("Unary operation must return a value.");

                use crate::base_ast::Opcode::*;
                match expr {
                    BasicValueEnum::IntValue(expr) => match opcode {
                        Sub => Ok(Some(BasicValueEnum::IntValue(
                            self.builder.build_int_neg(expr, "tmpneg").unwrap(),
                        ))),
                        Not => Ok(Some(BasicValueEnum::IntValue(
                            self.builder.build_not(expr, "tmpnot").unwrap(),
                        ))),
                        _ => todo!(),
                    },
                    _ => todo!(),
                }
            }
            InnerExpression::Cast(return_type, expr) => {
                let expr = self
                    .compile_expr(&expr)?
                    .expect("Cast expression must return a value to be cast.");

                Ok(Some(self.cast_value_to_type(expr, return_type)))
            }
        }
    }

    fn cast_value_to_type(
        &mut self,
        value: BasicValueEnum<'ctx>,
        return_type: &Type,
    ) -> BasicValueEnum<'ctx> {
        println!(
            "Casting value from type {} to type: {:?}",
            value.get_type(),
            return_type
        );
        match value {
            BasicValueEnum::IntValue(lhs) => match &return_type {
                Type::Int(IntegerType::I8) => inkwell::values::BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i8_type(), true, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::U8) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i8_type(), false, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::I16) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i16_type(), true, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::U16) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i16_type(), false, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::I32) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i32_type(), true, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::U32) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i32_type(), false, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::I64) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i64_type(), true, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::U64) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i64_type(), false, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::I128) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i128_type(), true, "tmp")
                        .unwrap(),
                ),
                Type::Int(IntegerType::U128) => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.i128_type(), false, "tmp")
                        .unwrap(),
                ),
                Type::Bool => BasicValueEnum::IntValue(
                    self.builder
                        .build_int_cast_sign_flag(lhs, self.context.bool_type(), false, "tmp")
                        .unwrap(),
                ),
                type_ => todo!("{:?}", type_),
            },
            BasicValueEnum::FloatValue(lhs) => match &return_type {
                Type::Float(FloatType::F32) => BasicValueEnum::FloatValue(
                    self.builder
                        .build_float_cast(lhs, self.context.f32_type(), "tmp")
                        .unwrap(),
                ),
                Type::Float(FloatType::F64) => BasicValueEnum::FloatValue(
                    self.builder
                        .build_float_cast(lhs, self.context.f64_type(), "tmp")
                        .unwrap(),
                ),
                _ => todo!(),
            },
            _ => todo!(),
        }
    }
}
