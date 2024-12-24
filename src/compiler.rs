use std::{borrow::Borrow, collections::HashMap};

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    types::BasicMetadataTypeEnum,
    values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue, PointerValue},
};

use crate::base_ast::{Expression, Function, FunctionDefinition, Program, Type};

pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,

    variables: HashMap<String, (PointerValue<'ctx>, Type<'ctx>)>,
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
    fn create_entry_block_alloca(&self, name: &str, tipe: Type) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.fn_value().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        match tipe {
            Type::I32 => builder.build_alloca(self.context.i32_type(), name).unwrap(),
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
            Type::I32 => self
                .builder
                .build_load(self.context.i32_type(), ptr, name)
                .unwrap(),
            _ => unimplemented!(),
        }
    }

    /// Compiles the specified `Function` in the given `Context` and using the specified `Builder` and `Module`.
    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
        program: &'a Program<'ctx>,
    ) -> Result<(), String> {
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
        let mut compiler = Compiler {
            context,
            builder,
            module,
            fn_value_opt: None,
            variables: HashMap::new(),
        };

        compiler.compile_program(program)
    }

    fn compile_program(&mut self, program: &Program<'ctx>) -> Result<(), String> {
        for thing in &program.things {
            match thing {
                crate::base_ast::TopLevel::Function(function) => {
                    self.compile_function(function)?;
                }
                crate::base_ast::TopLevel::Comment(_comment) => (),
            }
        }

        Ok(())
    }

    fn compile_function(
        &mut self,
        function: &Function<'ctx>,
    ) -> Result<FunctionValue<'ctx>, String> {
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
            let arg_name = function.definition.params[i].name;
            let tipe = function.definition.params[i].tipe;
            let alloca = self.create_entry_block_alloca(arg_name, tipe);

            self.builder.build_store(alloca, arg).unwrap();

            self.variables.insert(arg_name.to_string(), (alloca, tipe));
        }

        // compile body
        let body = self.compile_expr(function.body.as_ref().unwrap())?;

        let body = match body {
            Some(body) => body,
            None => {
                return Err(
                    "Error compiling function body. Body does not return anything.".to_string(),
                )
            }
        };

        self.builder.build_return(Some(&body)).unwrap();

        // return the whole thing after verification and optimization
        if function_val.verify(true) {
            Ok(function_val)
        } else {
            unsafe {
                function_val.delete();
            }

            Err("Invalid generated function.".to_string())
        }
    }

    fn compile_fn_definition(
        &self,
        proto: &FunctionDefinition,
    ) -> Result<FunctionValue<'ctx>, String> {
        let args_types = proto
            .params
            .iter()
            .map(|f| match f.tipe {
                crate::base_ast::Type::I32 => self.context.i32_type().into(),
                _ => unimplemented!(),
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();
        let args_types = args_types.as_slice();

        let fn_type = match proto.return_type {
            Some(Type::I32) => self.context.i32_type().fn_type(args_types, false),
            Some(Type::Bool) => self.context.bool_type().fn_type(args_types, false),
            None => self.context.void_type().fn_type(args_types, false),
            Some(_) => todo!(),
        };
        let fn_val = self.module.add_function(proto.name, fn_type, None);

        // set arguments names
        for (i, arg) in fn_val.get_param_iter().enumerate() {
            match arg {
                BasicValueEnum::IntValue(int_value) => int_value.set_name(proto.params[i].name),
                BasicValueEnum::ArrayValue(array_value) => {
                    array_value.set_name(proto.params[i].name)
                }
                BasicValueEnum::FloatValue(float_value) => {
                    float_value.set_name(proto.params[i].name)
                }
                BasicValueEnum::PointerValue(pointer_value) => {
                    pointer_value.set_name(proto.params[i].name)
                }
                BasicValueEnum::StructValue(struct_value) => {
                    struct_value.set_name(proto.params[i].name)
                }
                BasicValueEnum::VectorValue(vector_value) => {
                    vector_value.set_name(proto.params[i].name)
                }
            }
        }

        // finally return built prototype
        Ok(fn_val)
    }

    fn compile_expr(
        &mut self,
        expression: &Expression<'ctx>,
    ) -> Result<Option<BasicValueEnum<'ctx>>, String> {
        match expression {
            Expression::Block(block) => {
                for (i, statement) in block.statements.iter().enumerate() {
                    match statement {
                        crate::base_ast::Statement::Let(let_) => {
                            let alloca = self.create_entry_block_alloca(let_.name, let_.tipe);
                            let value = self.compile_expr(&let_.value)?;

                            if let Some(value) = value {
                                self.builder.build_store(alloca, value).unwrap();
                                self.variables
                                    .insert(let_.name.to_string(), (alloca, let_.tipe));
                            } else {
                                return Err("Error compiling let statement. Expression is None."
                                    .to_string());
                            }
                        }
                        crate::base_ast::Statement::Expression(expr) => {
                            self.compile_expr(&expr)?;
                        }
                        crate::base_ast::Statement::Return(expr) => {
                            // emit warning if there are more statements after return
                            if i < block.statements.len() - 1 {
                                eprintln!("Warning: Unreachable code after return statement.");
                            }
                            // check, if there is a return value
                            if let Some(_return_value) = &block.return_value {
                                eprintln!("Warning: Unreachable code after return statement.");
                            }
                            return Ok(self.compile_expr(&expr)?);
                        }
                        crate::base_ast::Statement::Comment(_comment) => (),
                        crate::base_ast::Statement::Error => todo!(),
                    }
                }

                if let Some(return_value) = &block.return_value {
                    Ok(self.compile_expr(return_value)?)
                } else {
                    Ok(None)
                }
            }
            Expression::FunctionCall(function_call) => {
                match self.get_function(function_call.name) {
                    Some(fun) => {
                        let args = &function_call.args;
                        let mut compiled_args = Vec::with_capacity(args.len());

                        for arg in args {
                            compiled_args.push(self.compile_expr(arg)?);
                        }

                        let argsv: Vec<BasicMetadataValueEnum> = compiled_args
                            .iter()
                            .by_ref()
                            .map(|&val| val.expect("Function argument must not be none").into())
                            .collect();

                        match self
                            .builder
                            .build_call(fun, argsv.as_slice(), "tmp")
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                        {
                            Some(value) => Ok(Some(value)),
                            None => Err("Invalid call produced.".to_string()),
                        }
                    }
                    None => Err("Unknown function.".to_string()),
                }
            }
            Expression::Variable(variable) => match self.variables.get(variable.name) {
                Some(var) => Ok(Some(self.build_load(var.0, variable.name, var.1))),
                None => Err("Could not find a matching variable.".to_string()),
            },
            Expression::Number(number) => Ok(Some(BasicValueEnum::IntValue(
                self.context.i32_type().const_int(*number as u64, false),
            ))),
            Expression::String(aststring) => todo!(),
            Expression::If(if_expr) => {
                let (condition, body, else_body) = (
                    &if_expr.condition,
                    &if_expr.body,
                    if_expr
                        .else_body
                        .as_ref()
                        .expect("If expression must have an else body"),
                );
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
                let then_val = self
                    .compile_expr(body)?
                    .expect("If body must return a value");
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                let then_bb = self.builder.get_insert_block().unwrap();

                // build else block
                self.builder.position_at_end(else_bb);
                let else_val = self
                    .compile_expr(else_body)?
                    .expect("Else body must return a value");
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                let else_bb = self.builder.get_insert_block().unwrap();

                // emit merge block
                self.builder.position_at_end(cont_bb);

                let phi_type = match then_val {
                    BasicValueEnum::IntValue(_) => self.context.i32_type(),
                    _ => todo!(),
                };

                let phi = self.builder.build_phi(phi_type, "iftmp").unwrap();

                phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);

                Ok(Some(phi.as_basic_value()))
            }
            Expression::While(while_) => {
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
            Expression::Op(left, opcode, right) => {
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
                                let sola_var = match *left.borrow() {
                                    Expression::Variable(ref var_name) => var_name,
                                    _ => {
                                        return Err("Expected variable as left-hand operator of assignment.".to_string());
                                    }
                                };

                                let var_val = self.compile_expr(right)?;
                                let var = self
                                    .variables
                                    .get(sola_var.name)
                                    .ok_or("Undefined variable.")?;

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
            Expression::ExpressionComment(_) => todo!(),
            Expression::Error => todo!(),
        }
    }
}
