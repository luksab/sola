use colored::Colorize as _;

use crate::base_ast::*;

pub struct Formatter {
    pub indent_level: usize,
    pub string: String,
}

impl Formatter {
    pub fn new() -> Self {
        Self {
            indent_level: 0,
            string: String::new(),
        }
    }

    pub fn indent(&mut self) {
        self.indent_level += 1;
    }

    pub fn unindent(&mut self) {
        self.indent_level -= 1;
    }

    pub fn push_indent(&mut self) {
        self.string.push_str(&" ".repeat(self.indent_level * 4));
    }

    pub fn push_str_indented(&mut self, s: &str) {
        self.push_indent();
        self.string.push_str(s);
    }

    pub fn push_string_indented(&mut self, s: String) {
        self.push_indent();
        self.string.push_str(&s);
    }

    pub fn push_str(&mut self, s: &str) {
        self.string.push_str(s);
    }
    pub fn push_string(&mut self, s: String) {
        self.string.push_str(&s);
    }
}

pub trait Format {
    fn format(&self, fmt: &mut Formatter);
}

pub fn format<P: Format>(input: &P) -> String {
    let mut formatter = Formatter {
        indent_level: 0,
        string: String::new(),
    };
    input.format(&mut formatter);
    formatter.string
}

impl Format for Program<'_> {
    fn format(&self, fmt: &mut Formatter) {
        for func in &self.things {
            func.format(fmt);
        }
    }
}

impl Format for TopLevel<'_> {
    fn format(&self, fmt: &mut Formatter) {
        match self {
            TopLevel::Function(func) => func.format(fmt),
            TopLevel::Comment(comment) => comment.format(fmt),
        }
    }
}

impl Format for Comment<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str_indented("// ");
        fmt.push_str(self.text);
        fmt.push_str("\n");
    }
}

impl Format for Function<'_> {
    fn format(&self, fmt: &mut Formatter) {
        self.definition.format(fmt);
        self.body.as_ref().map(|body| body.format(fmt));
        fmt.push_str("\n\n");
    }
}

impl Format for FunctionDefinition<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str_indented("fn ");
        fmt.push_str(self.name);
        fmt.push_str("(");

        fmt.push_string(
            self.params
                .iter()
                .map(|param| format!("{}", param))
                .collect::<Vec<_>>()
                .join(", "),
        );

        fmt.push_str(") ");
        if let Some(return_type) = &self.return_type {
            fmt.push_str("-> ");
            fmt.push_str(&return_type.to_string());
            fmt.push_str(" ");
        }
    }
}

impl Format for Statement<'_> {
    fn format(&self, fmt: &mut Formatter) {
        match self {
            Statement::Let(let_) => let_.format(fmt),
            Statement::Expression(expr) => {
                fmt.push_str_indented("");
                expr.format(fmt);
                fmt.push_str(";\n");
            }
            Statement::Return(expr) => {
                fmt.push_str_indented("return ");
                expr.format(fmt);
                fmt.push_str(";\n");
            }
            Statement::Comment(comment) => comment.format(fmt),
            Statement::Error => fmt.push_string_indented("error!\n".red().to_string()),
        }
    }
}

impl Format for FunctionCall<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str(&format!("{}(", self.name));
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                fmt.push_str(", ");
            }
            arg.format(fmt);
        }
        fmt.push_str(")");
    }
}

impl Format for Expression<'_> {
    fn format(&self, fmt: &mut Formatter) {
        match self {
            Expression::Expression(expr) => expr.format(fmt),
            Expression::FunctionCall(func) => func.format(fmt),
            Expression::Block(block) => {
                fmt.push_str("{\n");
                fmt.indent();
                for stmt in block.statements.iter() {
                    stmt.format(fmt);
                }
                if let Some(return_value) = &block.return_value {
                    fmt.push_str_indented("");
                    return_value.format(fmt);
                    fmt.push_str("\n");
                }
                fmt.unindent();
                fmt.push_str_indented("}");
            }
            Expression::Variable(var) => fmt.push_string(var.to_string()),
            Expression::Number(num) => fmt.push_string(num.to_string()),
            Expression::String(str) => fmt.push_string(str.to_string()),
            Expression::Op(lhs, op, rhs) => {
                fmt.push_str("(");
                lhs.format(fmt);
                fmt.push_str(" ");
                fmt.push_string(op.to_string());
                fmt.push_str(" ");
                rhs.format(fmt);
                fmt.push_str(")");
            }
            Expression::If(if_) => if_.format(fmt),
            Expression::ExpressionComment((expr, comment)) => {
                expr.format(fmt);
                comment.format(fmt);
            }
            Expression::Error => fmt.push_string("error".red().to_string()),
        }
    }
}

impl Format for If<'_> {
    fn format(&self, fmt: &mut Formatter) {
        fmt.push_str("if ");
        self.condition.format(fmt);
        fmt.push_str(" ");
        self.body.format(fmt);
        if let Some(else_) = &self.else_body {
            else_.format(fmt);
        }
    }
}
