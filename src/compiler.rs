use std::collections::HashMap;

use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    types::BasicMetadataTypeEnum,
    values::{BasicValueEnum, FunctionValue, PointerValue},
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

        println!("Compiling body of function: {}", function.definition.name);
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

        println!("Function body compiled: {}", body);

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
            Expression::Expression(expression) => self.compile_expr(expression),
            Expression::Block(block) => {
                // let parent = self.fn_value();
                // let block_bb = self.context.append_basic_block(parent, "block");
                // self.builder.position_at_end(block_bb);

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
            Expression::FunctionCall(function_call) => todo!(),
            Expression::Variable(variable) => match self.variables.get(variable.name) {
                Some(var) => Ok(Some(self.build_load(var.0, variable.name, var.1))),
                None => Err("Could not find a matching variable.".to_string()),
            },
            Expression::Number(number) => Ok(Some(BasicValueEnum::IntValue(
                self.context.i32_type().const_int(*number as u64, false),
            ))),
            Expression::String(aststring) => todo!(),
            Expression::If(_) => todo!(),
            Expression::Op(expression, opcode, expression1) => todo!(),
            Expression::ExpressionComment(_) => todo!(),
            Expression::Error => todo!(),
        }
    }
}
