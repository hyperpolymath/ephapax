# Architecture

Overview of the Ephapax compiler architecture.

## Compiler Pipeline

```
Source Code (.epx)
       │
       ▼
   ┌───────┐
   │ Lexer │  → Tokens
   └───────┘
       │
       ▼
   ┌────────┐
   │ Parser │  → AST
   └────────┘
       │
       ▼
   ┌─────────────┐
   │ Type Checker│  → Typed AST
   └─────────────┘
       │
       ▼
   ┌──────────┐
   │ Lowering │  → IR
   └──────────┘
       │
       ▼
   ┌──────────┐
   │ Codegen  │  → WASM
   └──────────┘
       │
       ▼
  WebAssembly (.wasm)
```

## Crate Structure

```
ephapax/
├── ephapax-syntax/     # AST definitions
├── ephapax-lexer/      # Tokenization (planned)
├── ephapax-parser/     # Parsing (planned)
├── ephapax-typing/     # Type checking
├── ephapax-ir/         # Intermediate representation (planned)
├── ephapax-wasm/       # WASM code generation
├── ephapax-runtime/    # WASM runtime support
├── ephapax-cli/        # Command-line interface (planned)
└── ephapax-lsp/        # Language server (planned)
```

## Component Details

### ephapax-syntax

Core AST definitions shared across the compiler.

```rust
pub enum Ty {
    Base(BaseTy),
    String(RegionName),
    Fun { param: Box<Ty>, ret: Box<Ty> },
    Prod { left: Box<Ty>, right: Box<Ty> },
    Sum { left: Box<Ty>, right: Box<Ty> },
    Borrow(Box<Ty>),
    // ...
}

pub enum ExprKind {
    Lit(Literal),
    Var(Var),
    Let { name: Var, value: Box<Expr>, body: Box<Expr> },
    Lambda { param: Var, param_ty: Ty, body: Box<Expr> },
    // ...
}
```

### ephapax-typing

Linear type checker implementing the rules from `formal/Typing.v`.

Key responsibilities:
- Track linear variable usage
- Verify region scoping
- Check borrow validity
- Ensure branch consistency

```rust
pub struct TypeChecker {
    ctx: Context,  // Variable bindings + usage tracking
}

impl TypeChecker {
    pub fn check(&mut self, expr: &Expr) -> Result<Ty, TypeError>;
}
```

### ephapax-wasm

WASM code generator using the `wasm-encoder` crate.

Key responsibilities:
- Type mapping to WASM types
- Memory management code generation
- Region enter/exit code
- String operation implementation

```rust
pub struct Codegen {
    bump_ptr: u32,
    region_stack: Vec<RegionInfo>,
    module: Module,
}

impl Codegen {
    pub fn generate(&mut self) -> Vec<u8>;
}
```

### ephapax-runtime

`no_std` runtime for WASM execution.

Provides:
- Bump allocation
- Region management
- String operations

```rust
#[no_mangle]
pub extern "C" fn __ephapax_bump_alloc(size: u32) -> u32;

#[no_mangle]
pub extern "C" fn __ephapax_region_enter();

#[no_mangle]
pub extern "C" fn __ephapax_region_exit();
```

## Memory Model

### WASM Linear Memory Layout

```
Address     Content
─────────────────────────────────────
0x0000      Bump pointer (4 bytes)
0x0004      Region stack pointer (4 bytes)
0x0008      Region stack (256 bytes)
0x0108      Heap start
   │        ... bump-allocated data ...
   ▼
   ─        (grows downward)
```

### String Representation

```
String Header (8 bytes):
┌────────────────┬────────────────┐
│  Data Pointer  │    Length      │
│   (4 bytes)    │   (4 bytes)    │
└────────────────┴────────────────┘
        │
        ▼
┌──────────────────────────────────┐
│         UTF-8 Bytes              │
└──────────────────────────────────┘
```

### Region Stack

```
Region Stack Entry (4 bytes):
┌────────────────┐
│ Saved Bump Ptr │  ← Restore on region exit
└────────────────┘
```

On region exit:
1. Pop saved bump pointer
2. Reset bump pointer to saved value
3. All allocations since region entry are "freed"

## Error Handling

### Error Types

```rust
pub enum TypeError {
    LinearVariableReused(Var),
    LinearVariableNotConsumed(Var),
    UnboundVariable(Var),
    InactiveRegion(RegionName),
    TypeMismatch { expected: Ty, found: Ty },
    RegionEscape(RegionName),
    // ...
}
```

### Error Reporting

Uses `ariadne` or `miette` for rich diagnostics:

```
error[E0001]: linear variable `s` used more than once
  ┌─ example.epx:4:9
  │
3 │     print(s)
  │           - first use here
4 │     print(s)
  │           ^ second use (not allowed)
```

## Testing Strategy

### Unit Tests

Each crate has module-level tests:

```rust
#[cfg(test)]
mod tests {
    #[test]
    fn test_linear_variable_reuse() {
        // ...
    }
}
```

### Integration Tests

End-to-end compilation and execution:

```rust
#[test]
fn test_hello_world() {
    let source = r#"
        region r {
            let s = String.new@r("hello")
            print(s)
        }
    "#;

    let wasm = compile(source).unwrap();
    let result = execute(wasm);
    assert_eq!(result.stdout, "hello");
}
```

### Property-Based Tests

Using `proptest`:

```rust
proptest! {
    #[test]
    fn linear_values_used_once(ast in arb_well_typed_ast()) {
        let result = type_check(&ast);
        // If well-typed, linear values used exactly once
        prop_assert!(result.is_ok());
    }
}
```

## Formal Verification

The type system is mechanized in Coq:

```
formal/
├── Syntax.v      # AST definitions
├── Typing.v      # Typing rules
└── Semantics.v   # Operational semantics + soundness
```

Key theorems:
- Progress: Well-typed programs don't get stuck
- Preservation: Types preserved under reduction
- Linearity: Linear values used exactly once
- Memory Safety: No use-after-free, no leaks

## Future Architecture

### Planned Components

- **ephapax-ir**: Typed intermediate representation
- **ephapax-opt**: IR optimizations
- **ephapax-cranelift**: Native code backend
- **ephapax-lsp**: Language server
- **ephapax-fmt**: Code formatter

### Plugin System (Future)

```
┌─────────────┐
│ Plugin API  │
├─────────────┤
│ Custom Pass │
│ Custom Lint │
│ Custom Gen  │
└─────────────┘
```
