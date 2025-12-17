# Ephapax Development Roadmap

**Version**: 0.1.0
**Last Updated**: 2025-12-17
**SPDX-License-Identifier**: EUPL-1.2

---

## Overview

This roadmap outlines the development plan for Ephapax, a linear type system for safe memory management targeting WebAssembly. The project is organized into phases, each building upon the previous.

---

## Phase 1: Foundation (Current)

**Status**: 35% Complete
**Target**: Q1 2026

### 1.1 Core Infrastructure

| Component | Status | Description |
|-----------|--------|-------------|
| Project Structure | Done | Cargo workspace, Coq setup |
| CI/CD Pipeline | Done | GitHub Actions for Rust + Coq |
| Documentation Framework | Done | AsciiDoc, Markdown, Coqdoc |
| Licence & Compliance | Done | EUPL-1.2, REUSE |

### 1.2 Formal Semantics

| Component | Status | Description |
|-----------|--------|-------------|
| Syntax.v | Done | AST and type definitions |
| Typing.v | Done | Linear typing rules |
| Semantics.v | Done | Operational semantics |
| Soundness Proofs | Partial | Progress, preservation (Admitted) |

### 1.3 Rust Implementation Skeleton

| Crate | Status | Description |
|-------|--------|-------------|
| ephapax-syntax | Done | AST definitions |
| ephapax-typing | In Progress | Type checker |
| ephapax-wasm | In Progress | WASM codegen |
| ephapax-runtime | In Progress | WASM runtime |

---

## Phase 2: Language Frontend

**Status**: Planned
**Target**: Q2 2026

### 2.1 Lexer (`ephapax-lexer`)

| Task | Priority | Notes |
|------|----------|-------|
| Token definitions | High | Keywords, operators, literals |
| Lexer implementation | High | Use `logos` crate |
| Error recovery | Medium | Continue after errors |
| Source spans | High | For error reporting |
| Unicode support | Medium | UTF-8 strings |

**Dependencies**: `logos`, `unicode-xid`

### 2.2 Parser (`ephapax-parser`)

| Task | Priority | Notes |
|------|----------|-------|
| Grammar definition | High | Based on spec/SPEC.md |
| Parser implementation | High | Use `chumsky` or `lalrpop` |
| Error messages | High | Human-readable diagnostics |
| AST construction | High | Build syntax tree |
| Incremental parsing | Low | For IDE support |

**Dependencies**: `chumsky` (preferred) or `lalrpop`

### 2.3 Error Reporting

| Task | Priority | Notes |
|------|----------|-------|
| Diagnostic types | High | Errors, warnings, hints |
| Source locations | High | Span-based |
| Pretty printing | High | Use `ariadne` or `miette` |
| Error codes | Medium | E0001, W0001 format |

**Dependencies**: `ariadne` or `miette`

---

## Phase 3: Type System

**Status**: Planned
**Target**: Q2-Q3 2026

### 3.1 Type Checker Completion

| Task | Priority | Notes |
|------|----------|-------|
| Linear context tracking | High | Track used variables |
| Region checking | High | Verify region scoping |
| Borrow checking | High | Second-class borrows |
| Type inference | Medium | Bidirectional |
| Error recovery | Medium | Continue after type errors |

### 3.2 Type System Extensions

| Feature | Priority | Notes |
|---------|----------|-------|
| Polymorphism | Medium | Type variables |
| Type aliases | Low | Named type abbreviations |
| Recursive types | Low | With linearity checks |

### 3.3 Testing Infrastructure

| Task | Priority | Notes |
|------|----------|-------|
| Unit tests | High | Per-crate |
| Property-based tests | High | Use `proptest` |
| Integration tests | High | End-to-end |
| Fuzzing | Medium | Grammar-based fuzzing |
| Coq extraction tests | Low | Compare implementations |

---

## Phase 4: Code Generation

**Status**: Planned
**Target**: Q3 2026

### 4.1 IR Design (`ephapax-ir`)

| Task | Priority | Notes |
|------|----------|-------|
| IR definition | High | Low-level typed IR |
| Lowering pass | High | AST -> IR |
| IR validation | High | Type-preserving |
| IR optimizations | Medium | Dead code, inlining |

### 4.2 WASM Backend Completion

| Task | Priority | Notes |
|------|----------|-------|
| Complete codegen | High | All expression types |
| Memory management | High | Region allocation |
| String operations | High | concat, slice, etc. |
| Function compilation | High | Parameters, returns |
| Validation | High | Verify output WASM |

### 4.3 Native Backend (Optional)

| Task | Priority | Notes |
|------|----------|-------|
| Cranelift integration | Low | Alternative target |
| Native runtime | Low | For testing |

---

## Phase 5: Developer Tools

**Status**: Planned
**Target**: Q4 2026

### 5.1 REPL (`ephapax-repl`)

| Task | Priority | Notes |
|------|----------|-------|
| Basic REPL loop | High | Parse-check-eval |
| WASM execution | High | Run in wasmtime |
| Pretty printing | Medium | Results and types |
| History | Low | Command history |
| Tab completion | Low | Identifier completion |

**Dependencies**: `rustyline`, `wasmtime`

### 5.2 Interpreter (`ephapax-interp`)

| Task | Priority | Notes |
|------|----------|-------|
| Tree-walking interpreter | Medium | For debugging |
| Step-by-step execution | Medium | Debugger support |
| Memory visualization | Low | Show region state |

### 5.3 Language Server Protocol

| Task | Priority | Notes |
|------|----------|-------|
| LSP server | Medium | `tower-lsp` |
| Hover information | Medium | Types, docs |
| Go to definition | Medium | Navigation |
| Diagnostics | High | Real-time errors |
| Code completion | Low | Suggestions |

**Dependencies**: `tower-lsp`

### 5.4 CLI (`ephapax-cli`)

| Task | Priority | Notes |
|------|----------|-------|
| `ephapax check` | High | Type check |
| `ephapax build` | High | Compile to WASM |
| `ephapax run` | High | Execute in WASM runtime |
| `ephapax repl` | High | Interactive mode |
| `ephapax fmt` | Medium | Code formatter |

**Dependencies**: `clap`

---

## Phase 6: Standard Library

**Status**: Planned
**Target**: 2026-2027

### 6.1 Core Module (`std.core`)

| Component | Priority | Notes |
|-----------|----------|-------|
| Unit, Bool | High | Base types |
| I32, I64, F32, F64 | High | Numeric types |
| Option | High | Linear option type |
| Result | High | Linear result type |

### 6.2 String Module (`std.string`)

| Function | Priority | Notes |
|----------|----------|-------|
| `String.new` | Done | Allocation |
| `String.len` | Done | Length |
| `String.concat` | Done | Concatenation |
| `String.slice` | High | Substring |
| `String.eq` | High | Equality |
| `String.split` | Medium | Tokenization |
| `String.parse_i32` | Medium | Parsing |

### 6.3 Collections Module (`std.collections`)

| Type | Priority | Notes |
|------|----------|-------|
| `Vec` | High | Dynamic array |
| `HashMap` | Medium | Hash table |
| `LinkedList` | Low | Demonstration |

### 6.4 I/O Module (`std.io`)

| Component | Priority | Notes |
|-----------|----------|-------|
| Console I/O | Medium | print, read |
| File I/O | Medium | WASI-based |
| Network I/O | Low | Future |

### 6.5 Memory Module (`std.mem`)

| Function | Priority | Notes |
|----------|----------|-------|
| `region_new` | High | Create region |
| `alloc` | High | Allocate in region |
| `copy_bytes` | Medium | Memory copy |

---

## Phase 7: Frameworks & Libraries

**Status**: Planned
**Target**: 2027

### 7.1 Web Framework (`ephapax-web`)

| Component | Priority | Notes |
|-----------|----------|-------|
| DOM bindings | Medium | WASM-browser bridge |
| Event handling | Medium | Linear callbacks |
| Fetch API | Medium | HTTP requests |

### 7.2 CLI Framework (`ephapax-cli-lib`)

| Component | Priority | Notes |
|-----------|----------|-------|
| Argument parsing | Medium | Typed args |
| Subcommands | Medium | Nested commands |

### 7.3 Testing Framework (`ephapax-test`)

| Component | Priority | Notes |
|-----------|----------|-------|
| Test discovery | High | Automatic |
| Assertions | High | Type-safe |
| Property-based | Medium | QuickCheck-style |

### 7.4 Serialization (`ephapax-serde`)

| Format | Priority | Notes |
|--------|----------|-------|
| JSON | Medium | Common format |
| CBOR | Low | Binary format |

---

## Phase 8: Advanced Features

**Status**: Research
**Target**: 2027+

### 8.1 Typestate

| Task | Status | Notes |
|------|--------|-------|
| Design | Research | Protocol types |
| Implementation | Future | Compile-time state |
| Documentation | Future | Best practices |

### 8.2 Fractional Permissions

| Task | Status | Notes |
|------|--------|-------|
| Design | Research | Read/write splitting |
| Formal semantics | Future | Coq proofs |
| Implementation | Future | Type checker |

### 8.3 Concurrency

| Task | Status | Notes |
|------|--------|-------|
| Linear channels | Research | Message passing |
| Session types | Research | Protocol safety |
| Async/await | Future | WASM threads |

### 8.4 Metaprogramming

| Task | Status | Notes |
|------|--------|-------|
| Macros | Future | Hygenic macros |
| Compile-time execution | Future | constexpr-like |

---

## Testing Strategy

### Unit Testing

- Per-module tests in each crate
- Property-based tests with `proptest`
- Coverage tracking with `tarpaulin`

### Integration Testing

- End-to-end compilation tests
- WASM execution tests with `wasmtime`
- Coq extraction comparison (future)

### Property-Based Testing

| Property | Priority | Notes |
|----------|----------|-------|
| Parsing roundtrip | High | parse(print(ast)) = ast |
| Type preservation | High | Eval preserves types |
| Linearity | High | Linear vars used once |
| Region safety | High | No escapes |

### Fuzzing

| Target | Tool | Notes |
|--------|------|-------|
| Lexer | `cargo-fuzz` | Random input |
| Parser | `cargo-fuzz` | Grammar-based |
| Type checker | `cargo-fuzz` | Well-formed AST |
| Codegen | `cargo-fuzz` | Type-correct IR |

---

## Documentation

### Wiki Structure

```
docs/wiki/
├── getting-started/
│   ├── installation.md
│   ├── hello-world.md
│   └── tutorial.md
├── language/
│   ├── syntax.md
│   ├── types.md
│   ├── linearity.md
│   ├── regions.md
│   └── borrowing.md
├── reference/
│   ├── keywords.md
│   ├── operators.md
│   ├── stdlib/
│   │   ├── core.md
│   │   ├── string.md
│   │   └── collections.md
│   └── builtins.md
├── tooling/
│   ├── cli.md
│   ├── repl.md
│   ├── lsp.md
│   └── formatter.md
├── internals/
│   ├── architecture.md
│   ├── type-checker.md
│   ├── codegen.md
│   └── runtime.md
└── contributing/
    ├── development.md
    ├── testing.md
    └── style-guide.md
```

### API Documentation

- Rustdoc for all crates
- Coqdoc for formal proofs
- OpenAPI for any web services

---

## Milestones

| Version | Target | Key Features |
|---------|--------|--------------|
| 0.1.0 | Q1 2026 | Foundation complete |
| 0.2.0 | Q2 2026 | Lexer + Parser |
| 0.3.0 | Q3 2026 | Type checker complete |
| 0.4.0 | Q4 2026 | WASM codegen complete |
| 0.5.0 | Q4 2026 | REPL + basic stdlib |
| 0.6.0 | Q1 2027 | LSP support |
| 0.7.0 | Q2 2027 | Core stdlib complete |
| 0.8.0 | Q3 2027 | Collections + I/O |
| 0.9.0 | Q4 2027 | Frameworks |
| 1.0.0 | 2028 | Production ready |

---

## Contributing

See [CONTRIBUTING.adoc](CONTRIBUTING.adoc) for:

- Development setup
- Code style guide
- PR process
- Issue templates

---

## Resources

### Research Papers

1. Wadler, P. (1990). *Linear types can change the world!*
2. Tofte, M. & Talpin, J.P. (1997). *Region-based memory management*
3. Walker, D. (2005). *Substructural type systems*
4. Bernardy, J.P. et al. (2018). *Linear Haskell*

### Related Projects

- [Rust](https://www.rust-lang.org/)
- [Linear Haskell](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html)
- [MLKit](https://www.cl.cam.ac.uk/research/mvg/tom/mlkit/)
- [Cyclone](https://cyclone.thelanguage.org/)

---

*Last updated: 2025-12-17*
