#[macro_use]
pub mod helpers;

pub mod base_ast;
pub mod compile;
pub mod compiler;
pub mod formatter;
pub mod parser;
pub mod resolver;

use inkwell::OptimizationLevel;
use parser::parse_program;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Opt {
    /// The input file
    #[structopt(parse(from_os_str))]
    input: std::path::PathBuf,

    /// Print the AST
    #[structopt(long)]
    print_ast: bool,

    /// Print the LLVM IR
    #[structopt(short, long)]
    print_ir: bool,

    /// Optimization level
    /// 0: No optimization
    /// 1: Less optimization
    /// 2: Default optimization
    /// 3: Aggressive optimization
    #[structopt(short = "O", long, default_value = "2")]
    optimization: u8,
}

fn main() {
    let opt: Opt = Opt::from_args();
    let input = std::fs::read_to_string(&opt.input).unwrap();
    // println!("{}", input);
    let program = parse_program(&input);
    let program: base_ast::Program<'_> = match program {
        Err(err) => {
            report_parse_errors(&opt, &input, err);
            std::process::exit(1);
        }
        Ok(program) => program,
    };

    if opt.print_ast {
        println!("{:#?}", program);
    }

    let program = match resolver::resolve(&program) {
        Ok(program) => program,
        Err(err) => {
            use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

            let mut colors = ColorGenerator::new();

            // Generate & choose some colours for each of our elements
            let a = colors.next();
            // let b = colors.next();
            // let out = Color::Fixed(81);

            let input_path = opt.input.to_str();
            Report::build(
                ReportKind::Custom("Resolver Error", ariadne::Color::Red),
                (input_path.unwrap(), err.span.clone()),
            )
            .with_note(format!(
                "This error occurred in the compiler at: {}",
                err.compiler_location
            ))
            .with_label(
                Label::new((input_path.unwrap(), err.span))
                    .with_message(err.message)
                    .with_color(a),
            )
            .finish()
            .print((input_path.unwrap(), Source::from(&input)))
            .unwrap();

            std::process::exit(1);
        }
    };

    program.print();

    // print!("{}", formatter::format(&program));

    let level = match opt.optimization {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3 => OptimizationLevel::Aggressive,
        _ => panic!("Invalid optimization level"),
    };

    if let Err(err) = compile::compile(&program, level, opt.print_ir) {
        use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

        let mut colors = ColorGenerator::new();

        // Generate & choose some colours for each of our elements
        let a = colors.next();
        // let b = colors.next();
        // let out = Color::Fixed(81);

        let input_path = opt.input.to_str();
        Report::build(
            ReportKind::Custom("Compile Error", ariadne::Color::Red),
            (input_path.unwrap(), err.span.clone()),
        )
        .with_note(format!(
            "This error occurred in the compiler at: {}",
            err.compiler_location
        ))
        .with_label(
            Label::new((input_path.unwrap(), err.span))
                .with_message(err.message)
                .with_color(a),
        )
        .finish()
        .print((input_path.unwrap(), Source::from(&input)))
        .unwrap();

        std::process::exit(1);
    }
}

fn report_parse_errors(
    opt: &Opt,
    input: &String,
    err: Vec<chumsky::prelude::Simple<parser::Token<'_>>>,
) {
    use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
    let mut colors = ColorGenerator::new();
    let a = colors.next();
    for err in err {
        let input_path = opt.input.to_str();
        match err.reason() {
            chumsky::error::SimpleReason::Unexpected => Report::build(
                ReportKind::Custom("Parse Error", ariadne::Color::Red),
                (input_path.unwrap(), err.span()),
            )
            .with_label(
                Label::new((input_path.unwrap(), err.span()))
                    .with_message(format!("Unexpected token: \"{:?}\"", err.found().unwrap()))
                    .with_color(a),
            )
            .with_message(format!(
                "Expected one of: {:?}",
                err.expected().collect::<Vec<_>>()
            ))
            .finish()
            .print((input_path.unwrap(), Source::from(input)))
            .unwrap(),
            chumsky::error::SimpleReason::Unclosed {
                span: _,
                delimiter: _,
            } => todo!(),
            chumsky::error::SimpleReason::Custom(_) => todo!(),
        }
    }
}
