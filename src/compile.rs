use inkwell::{
    context::Context,
    module::Module,
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
    OptimizationLevel,
};

use crate::{base_ast::Program, compiler::Compiler};

fn run_passes_on(module: &Module) {
    Target::initialize_all(&InitializationConfig::default());
    let target_triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&target_triple).unwrap();
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "generic",
            "",
            OptimizationLevel::None,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();

    let passes: &[&str] = &[
        "instcombine",
        "reassociate",
        "gvn",
        "simplifycfg",
        // "basic-aa",
        "mem2reg",
        // "default<O3>",
    ];

    module
        .run_passes(
            passes.join(",").as_str(),
            &target_machine,
            PassBuilderOptions::create(),
        )
        .unwrap();
}

pub fn compile(program: &Program) {
    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("tmp");
    Compiler::compile(&context, &builder, &module, program).unwrap();
    println!("compiled");
    run_passes_on(&module);

    module.print_to_stderr();

    // compile to object file
    let target_triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&target_triple).unwrap();
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "generic",
            "",
            OptimizationLevel::None,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();

    module.write_bitcode_to_path(std::path::Path::new("output.bc"));

    // compile bitcode to object file
    target_machine
        .write_to_file(
            &module,
            inkwell::targets::FileType::Object,
            std::path::Path::new("output.o"),
        )
        .unwrap();

    // compile bitcode to assembly
    target_machine
        .write_to_file(
            &module,
            inkwell::targets::FileType::Assembly,
            std::path::Path::new("output.s"),
        )
        .unwrap();

    // link object file
    let output = std::process::Command::new("clang")
        .arg("output.o")
        .arg("-o")
        .arg("output")
        .output()
        .expect("Failed to execute process");

    println!("clang output: {}", String::from_utf8_lossy(&output.stdout));
}
