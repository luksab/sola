- [x] track spans
- [ ] parser error recovery (brace matching)
- [x] track types (i64, i32, u64, etc.)
- [x] make sure all type conversions are inserted in the resolver
- [x] add integer types (43u8)
- [x] add compiler-span to errors (using file! and line! macros)
- [ ] add type casting to syntax (43 as u8)
- [x] resolver errors
- [ ] better error messages (multiple error types with multiple spans)
- [ ] pointer types
- [ ] array/struct/enums
- [ ] match expressions
- [ ] standard library functions
- [ ] resolver step
- [ ] add conversion functions
- [ ] heap allocation
- [ ] GC

- [ ] const as literal const (the const doesn't have a type, only the places where it gets used will have one)


# Type checking systems
- "C++" style: strictly top-to-bottom. Doesn't handle what I want Literals to do.
- Haskell/Rust: walk the entire function. Create a system of constraints. Then solve the constraints. Probably solve along the way.
  - Morphic does that, can look at it for an example
  - Hindley-Milner type inference
- Dependently typed languages: _B_idirectional type checking. 