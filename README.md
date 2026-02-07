# Ephapax

[![License: PMPL-1.0](https://img.shields.io/badge/License-PMPL--1.0-blue.svg)](https://github.com/hyperpolymath/palimpsest-license)
[![Rust 1.83+](https://img.shields.io/badge/rust-1.83+-orange.svg)](https://www.rust-lang.org/)
[![WASM](https://img.shields.io/badge/target-wasm32-purple.svg)](https://webassembly.org/)

_ἐφάπαξ — once for all_

**A dyadic linear type system for safe memory management, targeting WebAssembly.**

## 🌟 Key Features

- **Dyadic Design**: Switch between affine and linear modes
  - **Affine mode**: Use-at-most-once (≤1), implicit drops allowed — ideal for prototyping
  - **Linear mode**: Use-exactly-once (=1), explicit consumption required — production-safe
- **Memory Safety**: No use-after-free, no double-free, guaranteed resource cleanup
- **Region-Based Allocation**: Bulk deallocation without garbage collection
- **WebAssembly Target**: Compiles to portable, efficient WASM
- **Formal Foundations**: Type system mechanized in Coq with progress and preservation proofs

## 🚀 Quick Start

### Installation

```bash
# Clone the repository
git clone https://github.com/hyperpolymath/ephapax
cd ephapax

# Build release binary
cargo build --release

# Binary location
./target/release/ephapax
```

### Your First Program

Create `hello.eph`:

```ephapax
fn main(_unit: ()): I32 =
    let x = 1 + 2 in
    let y = x * 3 in
    y
```

Run it:

```bash
# Type-check
./target/release/ephapax check hello.eph

# Compile to WASM
./target/release/ephapax compile hello.eph -o hello.wasm

# Interactive REPL
./target/release/ephapax repl
```

## 📖 Language Overview

### Syntax

Ephapax uses **ML-style syntax** (not C-style):

```ephapax
// Function declarations
fn add(x: I32, y: I32): I32 = x + y

// Let bindings (use 'in' keyword)
fn compute(_unit: ()): I32 =
    let a = 10 in
    let b = 20 in
    a + b

// Conditionals
fn abs(x: I32): I32 =
    if x < 0 then 0 - x else x

// Lambda expressions
fn use_lambda(_unit: ()): I32 =
    let f = fn (x: I32) -> x + 1 in
    f(5)

// Product types (pairs)
fn swap(p: (I32, I32)): (I32, I32) =
    let x = p.0 in
    let y = p.1 in
    (y, x)
```

### Linear Types with Regions

```ephapax
fn process_string(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in

        // Borrow for reading (doesn't consume)
        let len = String.len(&s) in

        // Must explicitly drop in linear mode
        let _ = drop(s) in

        len
    }
```

### Dyadic Modes

**Affine Mode** (permissive):
```bash
./target/release/ephapax check --mode affine program.eph
```
- Values can be used 0 or 1 times
- Implicit drops allowed
- Faster prototyping
- Good for exploration

**Linear Mode** (strict, default):
```bash
./target/release/ephapax check --mode linear program.eph
```
- Values must be used exactly once
- Explicit drops required
- Production-ready
- Guaranteed resource safety

## 📂 Project Structure

```
ephapax/
├── formal/              # Coq mechanization
│   ├── Syntax.v         # AST and types
│   ├── Typing.v         # Linear typing rules
│   └── Semantics.v      # Operational semantics
├── src/                 # Implementation (Rust)
│   ├── ephapax-syntax/  # AST definitions
│   ├── ephapax-typing/  # Type checker (dyadic)
│   ├── ephapax-lexer/   # Tokenizer
│   ├── ephapax-parser/  # Parser
│   ├── ephapax-interp/  # Interpreter
│   ├── ephapax-wasm/    # WASM code generation
│   ├── ephapax-repl/    # Interactive shell
│   └── ephapax-cli/     # CLI interface
├── examples/            # Example programs
│   ├── affine/          # Affine mode examples
│   ├── linear/          # Linear mode examples
│   └── syntax-guide.eph # Comprehensive syntax guide
├── conformance/         # Conformance tests
│   ├── pass/            # Should type-check
│   └── fail/            # Should be rejected
└── tests/               # Integration tests
```

## 🎯 CLI Commands

```bash
# Type checking
ephapax check [--mode affine|linear] file.eph

# Compilation
ephapax compile file.eph -o output.wasm

# Interactive REPL
ephapax repl

# Run a program
ephapax run file.eph

# Show AST
ephapax parse file.eph

# Show tokens
ephapax tokens file.eph

# Help
ephapax --help
```

## 📊 Current Status

| Component | Completion | Status |
|-----------|------------|--------|
| **Type System Design** | 100% | ✅ Complete |
| **Formal Semantics (Coq)** | 100% | ✅ Complete |
| **Lexer** | 100% | ✅ Complete |
| **Parser** | 100% | ✅ Complete |
| **Type Checker** | 85% | 🚧 Near-complete |
| **WASM Codegen** | 85% | 🚧 Near-complete |
| **Lambda Support** | 60% | 🚧 Basic working |
| **Interpreter** | 100% | ✅ Complete |
| **REPL** | 100% | ✅ Complete |
| **CLI** | 100% | ✅ Complete |
| **Examples** | 80% | ✅ Good coverage |
| **Documentation** | 70% | 🚧 In progress |

### Test Coverage

- **150+ tests passing** across all crates
- Lexer: 6 tests
- Parser: 18 tests
- Interpreter: 19 tests
- Type checker: 38 tests (including 7 dyadic mode tests)
- WASM codegen: 58 tests (including lambda compilation)

## 🎓 Examples

### Affine Mode: Flexible Cleanup

```ephapax
fn flexible(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        // s is implicitly dropped - affine mode allows this
        42
    }
```

### Linear Mode: Strict Safety

```ephapax
fn strict(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        // Must explicitly drop - linear mode requires this
        let _ = drop(s) in
        42
    }
```

See `examples/` for more comprehensive examples.

## 🔬 Formal Foundations

The type system is grounded in:

- **Intuitionistic Linear Logic** — Resource-sensitive reasoning
- **Separation Logic** — Memory ownership and framing
- **Region Calculus (Tofte-Talpin)** — Scoped allocation

### Coq Mechanization

```bash
cd formal
coqc Syntax.v
coqc Typing.v
coqc Semantics.v
```

Proves:
- **Progress**: Well-typed programs don't get stuck
- **Preservation**: Types are preserved during evaluation
- **Resource Safety**: Linear values used exactly once (linear mode)

## 🏗️ Building from Source

### Prerequisites

- Rust 1.83+ with `wasm32-unknown-unknown` target
- Cargo
- (Optional) Coq 8.18+ for proof verification

### Build Commands

```bash
# Build all crates
cargo build --release

# Run tests
cargo test --workspace

# Build specific crate
cargo build -p ephapax-cli --release

# Install globally
cargo install --path src/ephapax-cli
```

### Binary Sizes

- `ephapax` binary: **2.1 MB** (stripped)
- Comparable to phronesis reference model
- Includes full compiler, type checker, and REPL

## 📚 Documentation

- **[Syntax Guide](examples/syntax-guide.eph)** — Comprehensive syntax reference
- **[Examples](examples/)** — Working example programs
- **[Examples README](examples/README.md)** — Syntax quick reference
- **[Affine vs Linear](examples/comparison-affine-vs-linear.eph)** — Mode comparison
- **[WASM Status](WASM-CODEGEN-STATUS.md)** — Code generation progress
- **[Type Checker Status](DYADIC-TYPE-CHECKER-COMPLETE.md)** — Type system details

## 🤝 Contributing

Contributions are welcome! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

### Development Workflow

```bash
# Make changes
$EDITOR src/...

# Test
cargo test --workspace

# Format
cargo fmt --all

# Clippy
cargo clippy --all-targets --all-features

# Commit
git commit -m "feat: description"
```

## 🌐 Related Work

- **[Rust](https://www.rust-lang.org/)** — Ownership and borrowing
- **[Linear Haskell](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html)** — Linear types in GHC
- **[MLKit](https://www.cl.cam.ac.uk/research/mvg/tom/mlkit/)** — Region-based memory management
- **[Cyclone](https://cyclone.thelanguage.org/)** — Safe C with regions
- **[ATS](http://www.ats-lang.org/)** — Dependent types with linear resources

## 📜 License

**PMPL-1.0-or-later** (Palimpsest License)

See [LICENSE](LICENSE) for full text.

## 👤 Author

**Jonathan D.A. Jewell**
<jonathan.jewell@open.ac.uk>

---

_"Once for all" — every resource used exactly once (in linear mode)._

## 🎯 Next Steps

- [ ] Complete closure environment capture (10% remaining)
- [ ] Add function tables for indirect calls (5% remaining)
- [ ] Expand standard library
- [ ] Build LSP server for editor integration
- [ ] More comprehensive examples
- [ ] Performance benchmarks

## ⚡ Performance

- Compile times: Fast (< 1s for typical programs)
- WASM output: Compact (547 bytes for hello world)
- Runtime: Zero-cost abstractions (safety at compile time)
- Memory: Region-based allocation (bulk deallocation)

## 🔗 Links

- **Repository**: https://github.com/hyperpolymath/ephapax
- **License**: https://github.com/hyperpolymath/palimpsest-license
- **Issues**: https://github.com/hyperpolymath/ephapax/issues
- **Discussions**: https://github.com/hyperpolymath/ephapax/discussions

---

**Made with 🦀 Rust and ❤️ for memory safety**
