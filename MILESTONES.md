<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->
<!-- SPDX-License-Identifier: EUPL-1.2 -->

# Ephapax Milestones

Executable milestones for reaching production readiness.

## Status Key

- 🔲 Not started
- 🚧 In progress
- ✅ Complete

---

## Milestone 0: Foundation (✅ Complete)

**Goal**: Establish theoretical and architectural foundation.

| Task | Status | Verification |
|------|--------|--------------|
| Define linear type system | ✅ | `spec/SPEC.md` exists |
| Mechanize semantics in Coq | ✅ | `coqc formal/*.v` succeeds |
| Prove Progress theorem | ✅ | `formal/Semantics.v` contains proof |
| Prove Preservation theorem | ✅ | `formal/Semantics.v` contains proof |
| Define AST crate | ✅ | `cargo build -p ephapax-syntax` |
| Set up CI pipeline | ✅ | `.github/workflows/ci.yml` exists |

---

## Milestone 1: Lexer Complete (🚧 In Progress)

**Goal**: Tokenize all Ephapax source constructs.

| Task | Status | Verification |
|------|--------|--------------|
| Tokenize keywords | 🚧 | `cargo test -p ephapax-lexer -- keywords` |
| Tokenize operators | 🚧 | `cargo test -p ephapax-lexer -- operators` |
| Tokenize literals (int, float, string, bool) | 🚧 | `cargo test -p ephapax-lexer -- literals` |
| Tokenize identifiers | 🚧 | `cargo test -p ephapax-lexer -- identifiers` |
| Tokenize region annotations | 🚧 | `cargo test -p ephapax-lexer -- regions` |
| Span tracking for error reporting | 🚧 | `cargo test -p ephapax-lexer -- spans` |
| Lexer error recovery | 🔲 | `cargo test -p ephapax-lexer -- recovery` |

**Exit Criteria**:
```bash
cargo test -p ephapax-lexer --all-features
# All tests pass, >90% token coverage
```

---

## Milestone 2: Parser Complete (🚧 In Progress)

**Goal**: Parse all syntactic constructs into typed AST.

| Task | Status | Verification |
|------|--------|--------------|
| Parse let bindings | 🚧 | `cargo test -p ephapax-parser -- let_binding` |
| Parse function definitions | 🚧 | `cargo test -p ephapax-parser -- functions` |
| Parse function application | 🚧 | `cargo test -p ephapax-parser -- application` |
| Parse product types (pairs) | 🚧 | `cargo test -p ephapax-parser -- products` |
| Parse sum types | 🚧 | `cargo test -p ephapax-parser -- sums` |
| Parse region expressions | 🚧 | `cargo test -p ephapax-parser -- regions` |
| Parse borrow expressions | 🚧 | `cargo test -p ephapax-parser -- borrows` |
| Parse conditionals | 🚧 | `cargo test -p ephapax-parser -- conditionals` |
| Error recovery with ariadne | 🔲 | Parse invalid input, emit ≥1 diagnostic |
| Operator precedence | 🔲 | `cargo test -p ephapax-parser -- precedence` |

**Exit Criteria**:
```bash
cargo test -p ephapax-parser --all-features
# All tests pass
# Parse all examples in docs/wiki/language/
```

---

## Milestone 3: Type Checker Hardened (🚧 In Progress)

**Goal**: Full linear type checking with clear error messages.

| Task | Status | Verification |
|------|--------|--------------|
| Check linearity (use exactly once) | 🚧 | `cargo test -p ephapax-typing -- linearity` |
| Check region scoping | 🚧 | `cargo test -p ephapax-typing -- region_scope` |
| Check borrow validity | 🚧 | `cargo test -p ephapax-typing -- borrows` |
| Infer function types | 🔲 | `cargo test -p ephapax-typing -- inference` |
| Reject use-after-move | 🔲 | `cargo test -p ephapax-typing -- use_after_move` |
| Reject region escape | 🔲 | `cargo test -p ephapax-typing -- region_escape` |
| Reject double-use | 🔲 | `cargo test -p ephapax-typing -- double_use` |
| Reject unused linear values | 🔲 | `cargo test -p ephapax-typing -- unused_linear` |
| Clear diagnostic messages | 🔲 | Manual review of error output |

**Exit Criteria**:
```bash
cargo test -p ephapax-typing --all-features
# Reject all invalid programs in tests/reject/
# Accept all valid programs in tests/accept/
```

---

## Milestone 4: WASM Code Generation (🚧 In Progress)

**Goal**: Compile type-checked programs to valid WebAssembly.

| Task | Status | Verification |
|------|--------|--------------|
| Generate WASM for primitives | 🚧 | `wasm-validate output.wasm` |
| Generate WASM for functions | 🚧 | `wasmtime run output.wasm` |
| Generate WASM for products | 🔲 | Test pair creation/projection |
| Generate WASM for sums | 🔲 | Test inl/inr/case |
| Generate WASM for regions | 🔲 | Test region allocation |
| Linear memory management | 🔲 | No leaks in valgrind/wasm-tools |
| Region-based deallocation | 🔲 | Verify bulk free on region exit |
| WASM validation | 🔲 | All output passes `wasm-validate` |

**Exit Criteria**:
```bash
# Compile and run hello world
cargo run -- compile examples/hello.eph -o hello.wasm
wasmtime run hello.wasm
# Output: "Hello, World!"
```

---

## Milestone 5: Test Suite (🔲 Not Started)

**Goal**: Comprehensive automated testing.

| Task | Status | Verification |
|------|--------|--------------|
| Unit tests for each crate | 🔲 | `cargo test --workspace` |
| Integration tests (end-to-end) | 🔲 | `cargo test --test integration` |
| Negative tests (reject invalid) | 🔲 | `tests/reject/` directory |
| Golden tests (expected output) | 🔲 | `tests/golden/` directory |
| Fuzzing harness | 🔲 | `cargo fuzz run lexer` |
| Property-based tests | 🔲 | `cargo test -- proptest` |
| Coq extraction tests | 🔲 | Compare extracted code to impl |

**Exit Criteria**:
```bash
cargo test --workspace --all-features
# >80% code coverage (cargo tarpaulin)
# Zero panics under fuzzing (1M iterations)
```

---

## Milestone 6: Standard Library (🔲 Not Started)

**Goal**: Provide essential safe primitives.

| Task | Status | Verification |
|------|--------|--------------|
| Linear strings | 🔲 | `cargo test -p ephapax-stdlib -- strings` |
| Linear vectors | 🔲 | `cargo test -p ephapax-stdlib -- vectors` |
| Linear maps | 🔲 | `cargo test -p ephapax-stdlib -- maps` |
| I/O primitives | 🔲 | `cargo test -p ephapax-stdlib -- io` |
| Numeric operations | 🔲 | `cargo test -p ephapax-stdlib -- numeric` |
| Option/Result types | 🔲 | `cargo test -p ephapax-stdlib -- option_result` |
| Document all functions | 🔲 | `cargo doc -p ephapax-stdlib` |

**Exit Criteria**:
```bash
cargo test -p ephapax-stdlib --all-features
cargo doc -p ephapax-stdlib --no-deps
# All public items documented
```

---

## Milestone 7: REPL Functional (🔲 Not Started)

**Goal**: Interactive development environment.

| Task | Status | Verification |
|------|--------|--------------|
| Evaluate expressions | 🔲 | Type `1 + 2`, get `3` |
| Multi-line input | 🔲 | `let f = \x -> \n  x + 1` works |
| Type inspection (`:type`) | 🔲 | `:type \x -> x` shows type |
| History persistence | 🔲 | Arrow up recalls previous |
| Tab completion | 🔲 | `pri<TAB>` → `print` |
| Error highlighting | 🔲 | Errors show source location |
| Load files (`:load`) | 🔲 | `:load example.eph` works |

**Exit Criteria**:
```bash
cargo run -- repl
# Run tutorial examples interactively
# No crashes on malformed input
```

---

## Milestone 8: CLI Polish (🔲 Not Started)

**Goal**: Production-quality command-line interface.

| Task | Status | Verification |
|------|--------|--------------|
| `ephapax compile <file>` | 🔲 | Produces valid WASM |
| `ephapax run <file>` | 🔲 | Compiles and executes |
| `ephapax check <file>` | 🔲 | Type checks only |
| `ephapax fmt <file>` | 🔲 | Formats source code |
| `--emit=ast\|ir\|wasm` | 🔲 | Dump intermediate stages |
| `--verbose` / `--quiet` | 🔲 | Control output verbosity |
| Proper exit codes | 🔲 | 0=success, 1=error, 2=usage |
| Shell completions | 🔲 | `ephapax completions bash` |

**Exit Criteria**:
```bash
ephapax --version  # Shows version
ephapax --help     # Shows help
ephapax compile examples/*.eph  # All compile
```

---

## Milestone 9: Language Server (🔲 Not Started)

**Goal**: IDE integration via LSP.

| Task | Status | Verification |
|------|--------|--------------|
| Diagnostics (errors/warnings) | 🔲 | Red squiggles in editor |
| Go to definition | 🔲 | Ctrl+click navigates |
| Hover for type info | 🔲 | Hover shows type |
| Completion suggestions | 🔲 | Autocomplete works |
| Document symbols | 🔲 | Outline view works |
| Workspace symbols | 🔲 | Ctrl+T search works |
| Format on save | 🔲 | Auto-formats |
| Semantic highlighting | 🔲 | Linear vars highlighted |

**Exit Criteria**:
```bash
# Install in VS Code/Helix/Neovim
# Open .eph file, verify features work
```

---

## Milestone 10: Documentation Complete (🔲 Not Started)

**Goal**: Comprehensive user and developer documentation.

| Task | Status | Verification |
|------|--------|--------------|
| Installation guide | 🔲 | Follow steps on fresh system |
| Language tutorial | 🔲 | Complete in <1 hour |
| API reference | 🔲 | `cargo doc --workspace` |
| Examples directory | 🔲 | 10+ working examples |
| Contributing guide | ✅ | `CONTRIBUTING.md` exists |
| Architecture docs | 🔲 | Explains compiler pipeline |
| Linearity explainer | 🔲 | Non-experts understand |

**Exit Criteria**:
```bash
# New user can install, write, and run program
# Following only documentation
```

---

## Milestone 11: Performance Baseline (🔲 Not Started)

**Goal**: Establish and track performance metrics.

| Task | Status | Verification |
|------|--------|--------------|
| Compile-time benchmarks | 🔲 | `cargo bench --bench compile` |
| Runtime benchmarks | 🔲 | `cargo bench --bench runtime` |
| Memory usage benchmarks | 🔲 | Track peak memory |
| Binary size tracking | 🔲 | WASM output size |
| Comparison with peers | 🔲 | vs. Rust WASM, AssemblyScript |
| CI benchmark tracking | 🔲 | Detect regressions |

**Exit Criteria**:
```bash
cargo bench
# Results stored in benches/results/
# <5% regression on PR merge
```

---

## Milestone 12: Alpha Release (🔲 Not Started)

**Goal**: First public release for early adopters.

| Task | Status | Verification |
|------|--------|--------------|
| Version 0.1.0 | 🔲 | `Cargo.toml` version bump |
| Changelog | 🔲 | `CHANGELOG.md` exists |
| GitHub release | 🔲 | Release page with assets |
| Pre-built binaries | 🔲 | Linux, macOS, Windows |
| Announcement post | 🔲 | Blog/social media |
| Issue templates | 🔲 | `.github/ISSUE_TEMPLATE/` |

**Exit Criteria**:
```bash
# User can download binary, run without cargo
# File issues using templates
```

---

## Milestone 13: Ecosystem Bootstrap (🔲 Not Started)

**Goal**: Enable third-party development.

| Task | Status | Verification |
|------|--------|--------------|
| Package format spec | 🔲 | Document in spec/ |
| Package registry design | 🔲 | RFC document |
| Build system integration | 🔲 | Works with Cargo/Deno |
| Tree-sitter grammar | 🔲 | Syntax highlighting |
| Example projects | 🔲 | 3+ real-world examples |

**Exit Criteria**:
```bash
# Third party can create, share, install packages
```

---

## Milestone 14: Beta Release (🔲 Not Started)

**Goal**: Feature-complete for general use.

| Task | Status | Verification |
|------|--------|--------------|
| All major features stable | 🔲 | No breaking changes planned |
| Performance optimized | 🔲 | Benchmarks meet targets |
| Documentation complete | 🔲 | All features documented |
| Known bugs triaged | 🔲 | No critical issues open |
| Community feedback addressed | 🔲 | Top issues resolved |

**Exit Criteria**:
```bash
# Used in 3+ non-trivial projects
# No P0 bugs for 30 days
```

---

## Milestone 15: 1.0 Release (🔲 Not Started)

**Goal**: Production-ready stable release.

| Task | Status | Verification |
|------|--------|--------------|
| Semantic versioning commitment | 🔲 | VERSIONING.md |
| Stability guarantees | 🔲 | Document in spec |
| Security audit | 🔲 | Third-party audit report |
| Long-term support policy | 🔲 | LTS.md document |
| Migration guide from beta | 🔲 | MIGRATING.md |

**Exit Criteria**:
```bash
# Formal stability commitment
# No breaking changes without major version
```

---

## Quick Reference

| Milestone | Target | Blocking |
|-----------|--------|----------|
| M0: Foundation | ✅ Done | - |
| M1: Lexer | M2, M7 | - |
| M2: Parser | M3 | M1 |
| M3: Type Checker | M4 | M2 |
| M4: WASM Codegen | M7, M8, M11 | M3 |
| M5: Test Suite | M12 | M4 |
| M6: Stdlib | M7, M12 | M4 |
| M7: REPL | M12 | M4, M6 |
| M8: CLI | M12 | M4 |
| M9: Language Server | M13 | M4 |
| M10: Docs | M12 | M4 |
| M11: Performance | M14 | M4 |
| M12: Alpha | M13 | M5-M8, M10 |
| M13: Ecosystem | M14 | M12 |
| M14: Beta | M15 | M11, M13 |
| M15: 1.0 | - | M14 |

---

## Next Actions

Priority tasks for immediate progress:

1. **Complete lexer tests** - Unblock parser work
2. **Add parser tests** - Validate AST generation
3. **Create test fixtures** - `tests/accept/` and `tests/reject/`
4. **Implement hello world** - End-to-end compilation proof
5. **Set up benchmarks** - Establish baseline early
