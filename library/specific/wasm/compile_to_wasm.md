# Operation: compile_to_wasm

## Interface Signature

```
compile_to_wasm: Module -> Result<WasmBinary, CompileError>
```

## Behavioral Semantics

**Purpose**: Compiles an Ephapax module to WebAssembly binary format.

**Parameters**:
- `module`: A type-checked Ephapax module

**Return Value**: WebAssembly binary bytes or compilation error.

**Properties**:
- Produces valid WebAssembly 1.0 binary
- Linear types enforced at compile time
- Region-based memory compiled to bump allocation
- Zero-cost abstractions for linear operations

**Compilation Strategy**:
- Linear values: Direct WebAssembly locals/globals
- Regions: Bump pointer allocation with bulk free
- Borrows: Pass-by-reference optimization
- Functions: Direct WebAssembly function calls

**Edge Cases**:
- Invalid module produces CompileError
- Unsupported features produce CompileError

## Executable Test Cases

```yaml
test_cases:
  - input: [valid_module]
    output: wasm_bytes
    description: "Compile valid module to WASM"

  - input: [module_with_type_error]
    error: "CompileError::TypeError"
    description: "Type errors prevent compilation"
```

## Ephapax Implementation

```rust
// In Rust codegen
pub fn compile_module(module: &Module) -> Result<Vec<u8>, CompileError> {
    let mut codegen = Codegen::new();
    codegen.compile(module)?;
    Ok(codegen.generate())
}
```
