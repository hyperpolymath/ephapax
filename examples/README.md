# Ephapax Examples

This directory contains example programs demonstrating Ephapax's linear type system and syntax.

## Correct Syntax

Ephapax uses **ML-style syntax**, not C-style syntax. Key differences:

### Function Declarations

**✅ Correct (Ephapax):**
```ephapax
fn function_name(param1: Type1, param2: Type2): ReturnType =
    expression
```

**❌ Wrong (C-style, not supported):**
```
fn function_name(param1: Type1, param2: Type2) -> ReturnType {
    expression
}
```

### Zero-Parameter Functions

Functions with no parameters must accept unit `()`:

```ephapax
fn no_params(_unit: ()): I32 = 42

// Call with unit
fn main(_unit: ()): I32 = no_params(())
```

### Let Bindings

Use `let ... in` syntax (not semicolons):

**✅ Correct:**
```ephapax
fn compute(_unit: ()): I32 =
    let x = 10 in
    let y = 20 in
    x + y
```

**❌ Wrong:**
```
fn compute() {
    let x = 10;
    let y = 20;
    x + y
}
```

### If Expressions

```ephapax
if condition then
    expression1
else
    expression2
```

### Lambda Expressions

```ephapax
fn (param: Type) -> expression
```

Example:
```ephapax
let f = fn (x: I32) -> x + 1 in
f(5)
```

### Product Types (Pairs/Tuples)

```ephapax
let p = (10, 20) in
let x = p.0 in
let y = p.1 in
x + y
```

### Linear Types with Regions

```ephapax
region r {
    let s = String.new@r("hello") in
    let len = String.len(&s) in
    let _ = drop(s) in
    len
}
```

## Working Examples

- **`hello.eph`** - Simple hello world (parsing, type checking, WASM)
- **`syntax-guide.eph`** - Comprehensive syntax reference with examples

## Testing Examples

```bash
# Parse an example
./target/release/ephapax parse examples/hello.eph

# Type-check an example
./target/release/ephapax check examples/hello.eph

# Compile to WASM
./target/release/ephapax compile examples/hello.eph -o hello.wasm

# Run in REPL
./target/release/ephapax repl
```

## Type System Modes

Ephapax supports two modes:

- **Linear mode** (default): Values must be used exactly once
- **Affine mode**: Values can be used 0 or 1 times (implicit drops allowed)

Both modes prevent double-use and ensure memory safety.

## More Information

See the main repository README and documentation for:
- Type system formalization (Coq proofs in `formal/`)
- Language specification
- Build instructions
- Contributing guidelines
