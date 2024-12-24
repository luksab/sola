# Sola programming language
Combining the great ideas of simplicity of Go with the amazing engeneering of Rust, Sola is a programming language that aims to be simple, fast and safe.

## Implementation details
Sola is implemented in Rust, using the amazing [LALRPOP](https://lalrpop.github.io/lalrpop/) parser generator and the [inkwell](https://thedan64.github.io/inkwell/inkwell/index.html) LLVM bindings.
A lot of the basic codegen is based on the [Kaleidoscope tutorial](https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/index.html) from the LLVM documentation.
