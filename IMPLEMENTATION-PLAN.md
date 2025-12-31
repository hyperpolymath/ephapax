# Ephapax Implementation Plan

## Complete Language Development Roadmap

**Primary Language**: Rust
**Target**: WebAssembly (wasm32-unknown-unknown, wasm32-wasi)
**Default Type Discipline**: Linear (with affine opt-in)

---

## Phase 1: Core Compiler (Current)

### 1.1 Lexer ✅ (In Progress)
**Crate**: `ephapax-lexer`
**Tech**: Rust + `logos`

```
Status: 🚧 In Progress
Files: src/ephapax-lexer/
```

### 1.2 Parser ✅ (In Progress)
**Crate**: `ephapax-parser`
**Tech**: Rust + `chumsky`

```
Status: 🚧 In Progress
Files: src/ephapax-parser/
```

### 1.3 Type Checker 🚧 (In Progress)
**Crate**: `ephapax-typing`
**Tech**: Rust

```
Status: 🚧 In Progress
Files: src/ephapax-typing/

TODO:
- [ ] Linear context threading
- [ ] Region scope tracking
- [ ] Borrow validity checking
- [ ] Branch agreement verification
- [ ] Affine mode support (opt-in)
```

### 1.4 WASM Code Generator 🚧 (In Progress)
**Crate**: `ephapax-wasm`
**Tech**: Rust + `wasm-encoder`

```
Status: 🚧 In Progress
Files: src/ephapax-wasm/

TODO:
- [ ] Type compilation (Ephapax → WASM)
- [ ] Expression compilation
- [ ] Runtime function generation
- [ ] Memory layout implementation
- [ ] Region stack management
```

---

## Phase 2: Runtime

### 2.1 Core Runtime
**Crate**: `ephapax-runtime`
**Tech**: Rust (compiles to WASM)

```rust
// Runtime functions (compiled into every Ephapax program)

// Memory management
fn bump_alloc(size: u32) -> u32;
fn region_enter() -> u32;
fn region_exit();

// String operations
fn string_new(data: *const u8, len: u32) -> u32;
fn string_concat(a: u32, b: u32) -> u32;
fn string_len(s: u32) -> u32;
fn string_eq(a: u32, b: u32) -> bool;

// I/O (WASI)
fn print(s: u32);
fn read_line() -> u32;
```

### 2.2 WASI Integration
**Tech**: Rust + `wasi` crate

```
TODO:
- [ ] File system access (read/write)
- [ ] Standard I/O (stdin/stdout/stderr)
- [ ] Environment variables
- [ ] Command-line arguments
```

---

## Phase 3: Standard Library

### 3.1 String Module (P0)
**File**: `library/String.ephapax`

```
String.new : ∀r. (bytes: &[u8]) → String@r
String.len : ∀r. (&String@r) → I32
String.concat : ∀r. (String@r, String@r) → String@r
String.slice : ∀r. (&String@r, I32, I32) → String@r
String.eq : ∀r. (&String@r, &String@r) → Bool
String.from_i32 : ∀r. (I32) → String@r
```

### 3.2 I/O Module (P0)
**File**: `library/IO.ephapax`

```
IO.print : ∀r. (&String@r) → Unit
IO.println : ∀r. (&String@r) → Unit
IO.read_line : ∀r. () → String@r
IO.eprint : ∀r. (&String@r) → Unit
```

### 3.3 Option Module (P1)
**File**: `library/Option.ephapax`

```
type Option[T] = None | Some(T)

Option.map : ∀a b. (Option[a], (a) → b) → Option[b]
Option.unwrap : ∀a. (Option[a]) → a  // panics on None
Option.unwrap_or : ∀a. (Option[a], a) → a
Option.is_some : ∀a. (&Option[a]) → Bool
Option.is_none : ∀a. (&Option[a]) → Bool
```

### 3.4 Result Module (P1)
**File**: `library/Result.ephapax`

```
type Result[T, E] = Ok(T) | Err(E)

Result.map : ∀t e u. (Result[t,e], (t) → u) → Result[u,e]
Result.map_err : ∀t e f. (Result[t,e], (e) → f) → Result[t,f]
Result.unwrap : ∀t e. (Result[t,e]) → t  // panics on Err
Result.expect : ∀t e. (Result[t,e], &String) → t
```

### 3.5 List Module (P2)
**File**: `library/List.ephapax`

```
type List[T] = Nil | Cons(T, List[T])

List.new : ∀t. () → List[t]
List.push : ∀t r. (List[t]@r, t) → List[t]@r
List.pop : ∀t r. (List[t]@r) → Option[(t, List[t]@r)]
List.len : ∀t r. (&List[t]@r) → I32
List.map : ∀a b r. (List[a]@r, (a) → b) → List[b]@r
List.fold : ∀a b r. (List[a]@r, b, (b, a) → b) → b
```

---

## Phase 4: Tooling

### 4.1 CLI
**Crate**: `ephapax-cli`
**Tech**: Rust + `clap`

```
Commands:
  ephapax build <file>     Compile to WASM
  ephapax run <file>       Compile and run (via wasmtime)
  ephapax check <file>     Type check only
  ephapax fmt <file>       Format source
  ephapax repl             Interactive REPL
```

### 4.2 Formatter
**Crate**: `ephapax-fmt`
**Tech**: Rust

```
TODO:
- [ ] Parse to AST
- [ ] Pretty-print with consistent style
- [ ] Region annotation alignment
- [ ] Let-binding alignment
```

### 4.3 REPL
**Crate**: `ephapax-repl`
**Tech**: Rust + `rustyline`

```
TODO:
- [ ] Parse and evaluate expressions
- [ ] Maintain linear context across inputs
- [ ] Region scope management
- [ ] Type display
```

### 4.4 Language Server (LSP)
**Crate**: `ephapax-lsp`
**Tech**: Rust + `tower-lsp`

```
Features:
- [ ] Diagnostics (type errors, linearity violations)
- [ ] Hover (type information)
- [ ] Go to definition
- [ ] Completion
- [ ] Rename
- [ ] Code actions (insert drop, etc.)
```

### 4.5 VSCode Extension
**Location**: `editors/vscode/`
**Tech**: TypeScript (only exception - VSCode requires it)

```
Features:
- [ ] Syntax highlighting
- [ ] LSP integration
- [ ] Snippets
- [ ] Region visualization
```

### 4.6 Web Playground
**Location**: `playground/`
**Tech**: Rust (WASM) + ReScript (UI)

```
Features:
- [ ] In-browser compilation
- [ ] In-browser execution
- [ ] Shareable links
- [ ] Example gallery
```

---

## Phase 5: Package Manager

### 5.1 Package Format
**File**: `ephapax.toml`

```toml
[package]
name = "my-package"
version = "0.1.0"
edition = "2025"
mode = "linear"  # or "affine"

[dependencies]
stdlib = "0.1.0"

[lib]
entry = "src/lib.ephapax"
```

### 5.2 Registry Integration
**Tech**: Deno + JSR

```
Publishing:
  ephapax publish        Push to JSR as WASM + type defs

Installing:
  ephapax add <package>  Add dependency
```

---

## Technology Stack Summary

| Component | Technology | Notes |
|-----------|------------|-------|
| Compiler | Rust | Core implementation |
| Lexer | Rust + logos | Fast tokenization |
| Parser | Rust + chumsky | Combinator parsing |
| Type Checker | Rust | Linear/affine logic |
| Code Gen | Rust + wasm-encoder | WASM output |
| Runtime | Rust → WASM | Embedded in output |
| CLI | Rust + clap | Command-line tool |
| Formatter | Rust | AST pretty-printer |
| REPL | Rust + rustyline | Interactive mode |
| LSP | Rust + tower-lsp | IDE support |
| VSCode | TypeScript | Extension only |
| Playground | Rust + ReScript | Web UI |
| Package Manager | Rust + Deno | JSR integration |
| Formal Proofs | Coq | Verification |

---

## Current Crate Structure

```
ephapax/
├── Cargo.toml              # Workspace root
├── src/
│   ├── ephapax-syntax/     # AST definitions ✅
│   ├── ephapax-lexer/      # Tokenization 🚧
│   ├── ephapax-parser/     # Parsing 🚧
│   ├── ephapax-typing/     # Type checking 🚧
│   ├── ephapax-wasm/       # Code generation 🚧
│   ├── ephapax-runtime/    # Runtime library 🚧
│   ├── ephapax-interp/     # Interpreter 🔲
│   ├── ephapax-repl/       # REPL 🔲
│   ├── ephapax-stdlib/     # Standard library 🔲
│   └── ephapax-cli/        # CLI tool 🔲
├── library/                # Stdlib source 🔲
├── formal/                 # Coq proofs ✅
├── academic/               # Documentation ✅
├── editors/                # Editor plugins 🔲
│   └── vscode/
└── playground/             # Web playground 🔲
```

Legend: ✅ Done | 🚧 In Progress | 🔲 Planned

---

## Next Steps (Immediate)

1. **Complete lexer** - Finish keyword/operator tokenization
2. **Complete parser** - Full expression parsing with error recovery
3. **Implement type checker** - Linear context threading
4. **Basic WASM output** - Simple expressions first
5. **Hello World** - End-to-end compilation of minimal program

---

## Timeline (No Dates, Just Order)

```
[Current] Lexer/Parser/Type Checker
    ↓
[Next] Basic WASM codegen (expressions, let, functions)
    ↓
[Then] Runtime (memory, strings, regions)
    ↓
[Then] CLI (build, run, check)
    ↓
[Then] Standard library (String, IO)
    ↓
[Then] REPL
    ↓
[Then] LSP + VSCode
    ↓
[Then] Package manager
    ↓
[Then] Web playground
```

---

*End of Implementation Plan*
