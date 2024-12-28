pub mod base_ast;
pub mod compile;
pub mod compiler;
pub mod formatter;
pub mod parser;

use inkwell::OptimizationLevel;
use parser::parse_program;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Opt {
    /// The input file
    #[structopt(parse(from_os_str))]
    input: std::path::PathBuf,

    /// Print the AST
    #[structopt(short, long)]
    ast: bool,

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
    println!("{}", input);
    let program = parse_program(&input);
    println!("{:?}", program);
    if let Err(err) = program {
        use ariadne::{Color, ColorGenerator, Fmt, Label, Report, ReportKind, Source};

        let mut colors = ColorGenerator::new();

        // Generate & choose some colours for each of our elements
        let a = colors.next();
        let b = colors.next();
        let out = Color::Fixed(81);

        for err in err {
            let input_path = opt.input.to_str();
            match err.reason() {
                chumsky::error::SimpleReason::Unexpected => {
                    Report::build(ReportKind::Error, (input_path.unwrap(), err.span()))
                        .with_label(
                            Label::new((input_path.unwrap(), err.span()))
                                .with_message(format!(
                                    "Unexpected token: \"{:?}\"",
                                    err.found().unwrap()
                                ))
                                .with_color(a),
                        )
                        .with_message(format!(
                            "Expected one of: {:?}",
                            err.expected().collect::<Vec<_>>()
                        ))
                        .finish()
                        .print((input_path.unwrap(), Source::from(&input)))
                        .unwrap()
                }
                chumsky::error::SimpleReason::Unclosed { span, delimiter } => todo!(),
                chumsky::error::SimpleReason::Custom(_) => todo!(),
            }
        }
        std::process::exit(1);
    }
    let program = program.unwrap();

    if opt.ast {
        println!("{:#?}", program);
    } else {
        print!("{}", formatter::format(&program));
    }

    let level = match opt.optimization {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3 => OptimizationLevel::Aggressive,
        _ => panic!("Invalid optimization level"),
    };

    compile::compile(&program, level);
}
