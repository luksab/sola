use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompilerLocation {
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
}

impl Display for CompilerLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

macro_rules! compiler_location {
    () => {
        CompilerLocation {
            file: file!(),
            line: line!(),
            column: column!(),
        }
    };
}
