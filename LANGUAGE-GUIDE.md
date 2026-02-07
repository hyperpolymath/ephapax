# Ephapax Language Guide

## Table of Contents

1. [Introduction](#introduction)
2. [Basic Syntax](#basic-syntax)
3. [Types](#types)
4. [Functions](#functions)
5. [Linear Types](#linear-types)
6. [Regions](#regions)
7. [Dyadic Design: Affine vs Linear Modes](#dyadic-design)
8. [Advanced Features](#advanced-features)
9. [Standard Library](#standard-library)
10. [Best Practices](#best-practices)

## Introduction

Ephapax is a **linear type system** for safe memory management, targeting **WebAssembly**. It provides two modes:

- **Affine mode** (≤1 use): Permissive, ideal for prototyping
- **Linear mode** (=1 use): Strict, production-safe with guaranteed resource cleanup

### Philosophy

Ephapax follows the principle of **"use exactly once"** (in linear mode), ensuring:
- No use-after-free
- No double-free
- Guaranteed resource cleanup
- Region-based bulk deallocation

## Basic Syntax

Ephapax uses **ML-style syntax**, not C-style.

### Hello World

```ephapax
fn main(_unit: ()): I32 =
    let x = 1 + 2 in
    let y = x * 3 in
    y
```

**Key differences from C:**
- No semicolons to terminate statements
- Use `in` keyword after let bindings
- Function body is a single expression
- No curly braces for function bodies (unless using blocks)

### Comments

```ephapax
// Single-line comment

/* Multi-line
   comment */
```

### Let Bindings

Always use the `in` keyword:

```ephapax
let x = 10 in
let y = 20 in
x + y
```

**Nested bindings:**

```ephapax
let a = 1 in
let b = 2 in
let c = a + b in
c * 2
```

## Types

### Primitive Types

```ephapax
I32         // 32-bit signed integer
I64         // 64-bit signed integer
F64         // 64-bit floating-point
Bool        // Boolean (true/false)
()          // Unit type (like void)
```

### Product Types (Pairs/Tuples)

```ephapax
(I32, I32)           // Pair of integers
(Bool, (I32, I32))   // Nested products
```

**Creating pairs:**

```ephapax
let pair = (10, 20) in
pair
```

**Accessing fields:**

```ephapax
fn first(p: (I32, I32)): I32 = p.0
fn second(p: (I32, I32)): I32 = p.1
```

### Sum Types (Variants)

```ephapax
inl I32 in Bool + I32    // Left variant: Int 42
inr I32 in Bool + I32    // Right variant: Int 42
```

### Function Types

```ephapax
I32 -> I32              // Function from I32 to I32
(I32, I32) -> I32       // Function taking pair, returning I32
```

### Linear Types

Linear types track **ownership** and **usage**:

```ephapax
String@r                // String allocated in region r
Linear<T>               // Explicitly linear type
```

## Functions

### Function Declarations

```ephapax
fn add(x: I32, y: I32): I32 = x + y
```

**Multiple parameters:**

```ephapax
fn add3(x: I32, y: I32, z: I32): I32 =
    let sum1 = x + y in
    sum1 + z
```

**Using unit parameter (required for zero-arg functions):**

```ephapax
fn constant(_unit: ()): I32 = 42
```

### Lambda Expressions

```ephapax
fn use_lambda(_unit: ()): I32 =
    let f = fn (x: I32) -> x + 1 in
    f(5)
```

**Closures (capture environment):**

```ephapax
fn make_adder(n: I32): I32 -> I32 =
    fn (x: I32) -> x + n
```

### Conditionals

```ephapax
fn abs(x: I32): I32 =
    if x < 0 then 0 - x else x
```

**With linear values (both branches must agree):**

```ephapax
fn conditional_string(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        let result = if true then
            String.len(&s)
        else
            String.len(&s)
        in
        let _ = drop(s) in
        result
    }
```

### Pattern Matching (Sums)

```ephapax
fn handle_sum(x: Bool + I32): I32 =
    case x of
      inl b -> if b then 1 else 0
    | inr n -> n
```

## Linear Types

### Ownership and Usage Rules

**Linear mode (=1 use):**
- Every linear value must be used **exactly once**
- No implicit drops
- Explicit `drop()` required

**Affine mode (≤1 use):**
- Values can be used **at most once**
- Implicit drops allowed
- More flexible for prototyping

### Example: Linear Value

```ephapax
fn process(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in  // s is linear

        // Use s exactly once (via borrow)
        let len = String.len(&s) in

        // Must explicitly drop in linear mode
        let _ = drop(s) in

        len
    }
```

### Borrowing

Borrowing allows **reading** without consuming:

```ephapax
&s           // Borrow s for reading
```

**Example:**

```ephapax
fn double_read(_unit: ()): I32 =
    region r {
        let s = String.new@r("test") in
        let len1 = String.len(&s) in  // Borrow
        let len2 = String.len(&s) in  // Borrow again
        let _ = drop(s) in            // Consume
        len1 + len2
    }
```

### Moving vs Copying

**Move (default for linear types):**

```ephapax
let s1 = String.new@r("data") in
let s2 = s1 in   // s1 is moved, cannot use s1 again
drop(s2)
```

**Copy (explicit):**

```ephapax
let s1 = String.new@r("data") in
let s2 = copy s1 in  // s2 is a copy
let _ = drop(s1) in
drop(s2)
```

## Regions

Regions enable **bulk deallocation** without garbage collection.

### Region Syntax

```ephapax
region r {
    // ... allocations in region r ...
}
```

All allocations in region `r` are deallocated when the region ends.

### String Allocation

```ephapax
fn create_string(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello world") in
        let len = String.len(&s) in
        let _ = drop(s) in
        len
    }
```

### Nested Regions

```ephapax
fn nested(_unit: ()): I32 =
    region r1 {
        region r2 {
            let s1 = String.new@r1("outer") in
            let s2 = String.new@r2("inner") in
            let len = String.len(&s1) + String.len(&s2) in
            let _ = drop(s2) in
            let _ = drop(s1) in
            len
        }
    }
```

### Region Escape Prevention

**Illegal (won't type-check):**

```ephapax
fn escape(): String@r =   // r escapes its scope!
    region r {
        String.new@r("oops")
    }
```

## Dyadic Design

Ephapax is **dyadic** — it supports two modes with different safety guarantees.

### Affine Mode (Prototyping)

```bash
ephapax check --mode affine program.eph
```

**Rules:**
- Use ≤1 times (at most once)
- Implicit drops allowed
- Faster iteration

**Example:**

```ephapax
fn affine_example(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        // s is implicitly dropped - affine mode allows this
        42
    }
```

### Linear Mode (Production)

```bash
ephapax check --mode linear program.eph
```

**Rules:**
- Use =1 time (exactly once)
- Explicit drops required
- Production-safe

**Example:**

```ephapax
fn linear_example(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        // Must explicitly drop in linear mode
        let _ = drop(s) in
        42
    }
```

### Choosing a Mode

| Use Case | Mode | Reason |
|----------|------|--------|
| Rapid prototyping | Affine | Fewer errors, faster iteration |
| Exploring APIs | Affine | Don't need perfect resource tracking |
| Production code | Linear | Guaranteed resource safety |
| Critical systems | Linear | No leaks, explicit control |
| Learning | Affine | Less overwhelming initially |

### Migration Path

1. **Start with affine mode** during development
2. **Switch to linear mode** for production
3. **Fix diagnostics** (add explicit drops)
4. **Deploy** with confidence

## Advanced Features

### First-Class Functions

```ephapax
fn apply(f: I32 -> I32, x: I32): I32 = f(x)

fn use_apply(_unit: ()): I32 =
    let inc = fn (n: I32) -> n + 1 in
    apply(inc, 10)
```

### Function Tables and Indirect Calls

Ephapax compiles lambdas to WASM function tables with `call_indirect`:

```ephapax
fn indirect(_unit: ()): I32 =
    let f = fn (x: I32) -> x * 2 in
    let g = fn (x: I32) -> x + 1 in
    let result1 = f(5) in      // call_indirect
    let result2 = g(result1) in // call_indirect
    result2
```

### Closure Environment Capture

Ephapax automatically detects and captures free variables:

```ephapax
fn make_multiplier(factor: I32): I32 -> I32 =
    fn (x: I32) -> x * factor   // Captures 'factor'
```

## Standard Library

### Prelude

```ephapax
id         : a -> a                    // Identity
compose    : (b -> c) -> (a -> b) -> (a -> c)
flip       : (a -> b -> c) -> (b -> a -> c)
const      : a -> b -> a               // Constant function
```

### Pair Operations

```ephapax
fst        : (a, b) -> a               // First element
snd        : (a, b) -> b               // Second element
swap       : (a, b) -> (b, a)          // Swap elements
```

### Boolean Operations

```ephapax
not        : Bool -> Bool
and        : Bool -> Bool -> Bool
or         : Bool -> Bool -> Bool
```

### Integer Operations

```ephapax
succ       : I32 -> I32                // Increment
pred       : I32 -> I32                // Decrement
abs        : I32 -> I32                // Absolute value
min        : I32 -> I32 -> I32
max        : I32 -> I32 -> I32
clamp      : I32 -> I32 -> I32 -> I32  // Clamp to range
```

### String Operations

```ephapax
String.new@r    : String -> String@r   // Allocate in region
String.len      : &String@r -> I32     // Get length
String.concat@r : &String@r1 -> &String@r2 -> String@r
String.clone@r  : &String@r1 -> String@r
String.eq       : &String@r1 -> &String@r2 -> Bool
```

### I/O Operations

```ephapax
print      : String -> ()
println    : String -> ()
read_line  : () -> String
```

### Math Operations

```ephapax
sqrt       : F64 -> F64
sin        : F64 -> F64
cos        : F64 -> F64
tan        : F64 -> F64
exp        : F64 -> F64
log        : F64 -> F64
pow        : F64 -> F64 -> F64
```

### Memory Management

```ephapax
drop       : Linear<T> -> ()           // Explicit deallocation
alloc@r    : I32 -> Linear<Ptr>@r      // Allocate bytes
free       : Linear<Ptr> -> ()         // Free allocation
```

## Best Practices

### 1. Start with Affine Mode

Affine mode is more forgiving during development. Switch to linear mode for production.

### 2. Use Borrowing for Multiple Reads

```ephapax
// Good
let len1 = String.len(&s) in
let len2 = String.len(&s) in
...

// Bad (compile error in linear mode)
let len1 = String.len(s) in  // s consumed!
let len2 = String.len(s) in  // Error: s already used
...
```

### 3. Explicit Drops in Linear Mode

Always explicitly drop linear values:

```ephapax
let s = String.new@r("data") in
let result = do_something(&s) in
let _ = drop(s) in  // Don't forget!
result
```

### 4. Region-Based Allocation

Use regions for bulk deallocation:

```ephapax
region r {
    let s1 = String.new@r("a") in
    let s2 = String.new@r("b") in
    let s3 = String.new@r("c") in
    // ... use s1, s2, s3 ...
    let _ = drop(s1) in
    let _ = drop(s2) in
    let _ = drop(s3) in
    result
}  // Region r deallocated here
```

### 5. Branch Agreement for Linear Values

Both branches must handle linear values consistently:

```ephapax
// Good
region r {
    let s = String.new@r("data") in
    let result = if condition then
        String.len(&s)
    else
        String.len(&s)
    in
    let _ = drop(s) in
    result
}

// Bad (branch agreement violation)
region r {
    let s = String.new@r("data") in
    if condition then
        drop(s)    // s consumed in then branch
    else
        42         // s not consumed in else branch!
}
```

### 6. Function Signatures

Be explicit about parameter and return types:

```ephapax
// Good
fn process(x: I32, y: I32): I32 = x + y

// Bad (relies on type inference, which may fail)
fn process(x, y) = x + y
```

### 7. Avoid Region Escape

Don't return values allocated in inner regions:

```ephapax
// Bad
fn escape(): String@r =
    region r {
        String.new@r("oops")  // Escapes region!
    }

// Good
fn no_escape(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        let len = String.len(&s) in
        let _ = drop(s) in
        len  // Return non-linear value
    }
```

## Next Steps

- **Examples**: See `examples/` directory for complete working programs
- **REPL**: Try `ephapax repl` for interactive exploration
- **LSP**: Set up editor integration with `ephapax-lsp`
- **WASM**: Compile to WebAssembly with `ephapax compile`

## Resources

- **Syntax Guide**: [examples/syntax-guide.eph](examples/syntax-guide.eph)
- **Examples**: [examples/README.md](examples/README.md)
- **API Reference**: [API-REFERENCE.md](API-REFERENCE.md)
- **LSP Guide**: [LSP-GUIDE.md](LSP-GUIDE.md)
- **Formal Semantics**: [formal/](formal/)

---

**Happy hacking with Ephapax!** 🦀✨
