# Ephapax Enhancement Suite - Implementation Status

**Date**: 2026-02-07
**Overall Completion**: 40% (2/5 enhancements completed)

This document tracks the implementation status of the 5 optional enhancements planned for Ephapax after reaching 100% core language completion.

---

## Enhancement #1: Debugger Support ✅ COMPLETED (Phase 1)

**Priority**: 1 (Highest)
**Status**: Phase 1 Complete, Phases 2-4 Planned
**Completion**: 40%

### What Was Implemented

#### ✅ Source Map Generation (JSON Format)
- Maps WASM instruction offsets to source file line numbers
- JSON output: `program.wasm.map`
- Contains mode information (affine/linear)
- Fully functional and tested

#### ✅ Mode Metadata Custom WASM Section
- Custom section: `ephapax.debug.mode`
- JSON payload with variable linearity info
- Embedded in WASM binary

#### ✅ CLI Support
- `--debug` flag to enable debug output
- `--mode <linear|affine>` flag for mode selection
- Automatic source map generation

#### ✅ Span Tracking
- Instruction-to-source-line mapping during codegen
- Stored in `DebugInfo` struct
- Approximates offsets by instruction count

### What Remains

#### ⏳ Phase 2: DWARF Support
**Status**: Started but disabled (gimli 0.31 API issues)

**Blocked by**: gimli library API complexity
**Effort**: 1-2 weeks
**Files**: `src/ephapax-wasm/src/debug.rs` (DwarfBuilder code exists but commented out)

**Tasks**:
- Fix gimli 0.31 API usage (LineProgram::new signature changed)
- Emit `.debug_info`, `.debug_abbrev`, `.debug_line` sections
- Test with lldb/gdb compatibility

#### ⏳ Phase 3: Debug Adapter Protocol (DAP) Server
**Status**: Not started
**Effort**: 2-3 weeks

**New crate**: `ephapax-debug`

**Dependencies**:
```toml
dap = "0.5"             # Debug Adapter Protocol
tokio = "1"             # Async runtime
wasmtime = "28"         # WASM execution
serde_json = "1"        # Mode metadata parsing
```

**Key files**:
- `src/ephapax-debug/src/lib.rs` - DAP adapter
- `src/ephapax-debug/src/mode_view.rs` - Mode-aware formatting
- `src/ephapax-debug/src/wasm_state.rs` - Runtime state tracking

**Features**:
- Breakpoint support (map lines → WASM offsets using source map)
- Step-through execution
- Variable inspection with linearity annotations
- Mode switcher (affine/linear/both views)

#### ⏳ Phase 4: VS Code Extension Integration
**Status**: Not started
**Effort**: 1 week
**Depends on**: Phase 3 (DAP server), Enhancement #4 (VS Code extension)

**Tasks**:
- Add debugger commands to VS Code extension
- Integrate with DAP server binary
- Mode switcher UI in debug view
- Inline variable annotations

### Testing

**Completed**:
```bash
# Source map generation
cargo test --package ephapax-wasm test_source_map_generation

# Integration test
ephapax compile test.eph --debug --mode linear
# Generates test.wasm + test.wasm.map ✓
```

**Pending**:
- DWARF section validation (blocked on Phase 2)
- DAP protocol compliance tests (blocked on Phase 3)
- End-to-end VS Code debugging (blocked on Phase 4)

### Documentation

- ✅ `docs/DEBUG-SUPPORT.md` - Complete Phase 1 documentation
- ⏳ Debugging guide (pending Phase 3/4 completion)

---

## Enhancement #2: Package Manager ✅ COMPLETED

**Priority**: 2
**Status**: Complete
**Completion**: 100%
**Effort**: ~4 hours (implemented 2026-02-07)

### What Was Implemented

#### ✅ Core Features
- **Manifest Parsing**: Full `ephapax.toml` support with validation
- **Local Registry**: Package storage in `~/.ephapax/registry/`
- **Dependency Resolution**: Backtracking algorithm with SemVer constraints
- **Version Selection**: Automatic latest compatible version selection
- **Transitive Dependencies**: Recursive dependency tree resolution
- **Mode-Specific Dependencies**: Support for `mode = "affine"` specification

#### ✅ CLI Commands
- `ephapax package init <name>` - Initialize new projects
- `ephapax package install` - Install from manifest
- `ephapax package search <query>` - Search local registry
- `ephapax package list` - List installed packages

#### ✅ New Crate: `ephapax-package`
**Modules**:
- `manifest.rs` - TOML parsing and validation (275 lines)
- `registry.rs` - Local package storage (280 lines)
- `resolver.rs` - Dependency resolution (230 lines)
- `lib.rs` - Public API (90 lines)

**Tests**: 14 unit tests covering:
- Manifest parsing (valid/invalid cases)
- Dependency specifications (simple, detailed, path, git)
- Registry operations (install, search, versions)
- Resolution (simple, transitive, version selection)

### What Remains (Future Enhancements)

#### ⏳ Phase 2: Remote Registry
- HTTP API for package upload/download
- Authentication with API tokens
- `ephapax package publish` command
- Central package repository

#### ⏳ Phase 3: Module Import Syntax
- Parser: Add `import` statement
- Type checker: Resolve module paths
- Codegen: Link multiple modules

#### ⏳ Phase 4: Lockfile Generation
- Generate `ephapax.lock` for reproducibility
- Pin exact dependency versions

### Design

Cargo-style package manager for Ephapax modules.

#### Manifest Format (`ephapax.toml`)
```toml
[package]
name = "my-lib"
version = "0.1.0"
authors = ["Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"]
license = "PMPL-1.0-or-later"

[dependencies]
linear-collections = "1.0"
affine-utils = { version = "0.5", mode = "affine" }
```

#### Architecture

**New crate**: `ephapax-package`

**Modules**:
- `manifest.rs` - TOML parsing
- `resolver.rs` - Dependency resolution (backtracking algorithm)
- `registry.rs` - Local package registry (`~/.ephapax/registry/`)
- `fetch.rs` - Package downloading (git/http)

#### Module Import Syntax

```ephapax
import "linear-collections/vec" as Vec
import "affine-utils/option" as Opt

fn main(): I32 =
  let v = Vec.new() in
  ...
```

#### CLI Commands

```bash
ephapax package init                    # Create ephapax.toml
ephapax package install <name>          # Install dependency
ephapax package publish                 # Publish to registry
ephapax package search <query>          # Search packages
```

### Implementation Steps

1. Create `ephapax-package` crate
2. Implement TOML manifest parsing
3. Build dependency resolver
4. Create local registry structure
5. Add module import syntax to parser
6. Integrate with type checker (resolve imports)
7. Update codegen to link modules
8. Add CLI subcommands

### Verification

```bash
cd my-project
ephapax package init
ephapax package install linear-collections

# In code: import "linear-collections/vec" as Vec
ephapax compile main.eph
```

---

## Enhancement #3: Performance Benchmarks ⏳ NOT STARTED

**Priority**: 3
**Status**: Planned
**Completion**: 0%
**Effort**: 1-2 weeks

### Benchmark Suite

Compare Ephapax to Rust (wasm32) and AssemblyScript.

#### Metrics

1. **Compilation Speed**
   - Parse time
   - Type check time
   - Codegen time
   - Total time

2. **Binary Size**
   - Raw WASM size
   - Gzipped size
   - Per-function overhead

3. **Runtime Performance**
   - Fibonacci (recursion)
   - Quicksort (arrays)
   - String concatenation
   - HashMap operations

#### Architecture

**New directory**: `benches/`

**Files**:
- `benches/compile_time.rs` - Criterion benchmarks for compiler
- `benches/binary_size.rs` - WASM size measurement
- `benches/runtime_perf.rs` - wasmtime execution benchmarks
- `benches/comparison/` - Reference implementations
  - `fib.eph`, `fib.rs`, `fib.ts`
  - `quicksort.eph`, `quicksort.rs`, `quicksort.ts`
  - `strings.eph`, `strings.rs`, `strings.ts`

#### CI Integration

```yaml
# .github/workflows/benchmark.yml
name: Performance Benchmarks

on: [push, pull_request]

jobs:
  bench:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cargo bench
      - run: ./scripts/compare-benchmarks.sh
      - uses: actions/upload-artifact@v4
        with:
          name: benchmark-results
          path: target/criterion/
```

#### Output Format

| Benchmark | Ephapax | Rust (wasm32) | AssemblyScript | Relative |
|-----------|---------|---------------|----------------|----------|
| Fibonacci (n=30) | 42ms | 38ms | 51ms | 1.1x slower |
| Quicksort (1000 items) | 15ms | 14ms | 18ms | 1.07x slower |
| Binary size (gzip) | 2.1KB | 1.8KB | 3.2KB | 0.66x smaller |

### Implementation Steps

1. Set up Criterion benchmarks
2. Write reference implementations (Rust, AssemblyScript)
3. Create measurement scripts
4. Add CI workflow
5. Generate comparison tables (markdown)
6. Document methodology

---

## Enhancement #4: VS Code Extension ⏳ NOT STARTED

**Priority**: 4
**Status**: Planned
**Completion**: 0%
**Effort**: 1-2 weeks

### Features

1. **Syntax Highlighting**
   - TextMate grammar for `.eph` files
   - Keywords: `fn`, `let`, `let!`, `drop`, `if`, `case`, `region`
   - Type annotations: `I32`, `String`, `->`, `*`, `+`

2. **LSP Integration**
   - Connect to `ephapax-lsp` (already implemented!)
   - Real-time error diagnostics
   - Hover information
   - Code completion

3. **Mode Switcher**
   - Status bar: `Ephapax [Linear]` / `Ephapax [Affine]`
   - Command: "Ephapax: Switch Mode"
   - Updates LSP server mode

4. **Debugger Integration** (depends on Enhancement #1 Phase 3)
   - Debug configuration in `launch.json`
   - Connect to DAP server
   - Mode-aware variable display

### Architecture

**New directory**: `vscode-extension/`

```
vscode-extension/
├── package.json           # Extension manifest
├── src/
│   ├── extension.ts       # Main entry point
│   ├── lsp-client.ts      # LSP client wrapper
│   └── mode-switcher.ts   # Mode toggle logic
├── syntaxes/
│   └── ephapax.tmLanguage.json  # TextMate grammar
└── themes/
    └── ephapax-dark.json  # (Optional) custom theme
```

#### package.json

```json
{
  "name": "ephapax",
  "displayName": "Ephapax Language Support",
  "version": "0.1.0",
  "publisher": "hyperpolymath",
  "engines": { "vscode": "^1.95.0" },
  "categories": ["Programming Languages"],
  "activationEvents": ["onLanguage:ephapax"],
  "contributes": {
    "languages": [{
      "id": "ephapax",
      "extensions": [".eph"],
      "configuration": "./language-configuration.json"
    }],
    "grammars": [{
      "language": "ephapax",
      "scopeName": "source.ephapax",
      "path": "./syntaxes/ephapax.tmLanguage.json"
    }],
    "commands": [{
      "command": "ephapax.switchMode",
      "title": "Ephapax: Switch Mode (Linear/Affine)"
    }]
  }
}
```

### Implementation Steps

1. Create extension scaffold (`yo code`)
2. Write TextMate grammar
3. Implement LSP client (connect to ephapax-lsp)
4. Add mode switcher command
5. Package with vsce
6. Publish to VS Code marketplace

### Testing

```bash
cd vscode-extension
npm install
npm run compile
vsce package  # Creates ephapax-0.1.0.vsix
code --install-extension ephapax-0.1.0.vsix
```

---

## Enhancement #5: Closure Environment Optimization ⏳ NOT STARTED

**Priority**: 5 (Lowest)
**Status**: Planned
**Completion**: 0%
**Effort**: 2 weeks

### Problem

Current lambda compilation captures entire environment. This wastes memory and increases WASM binary size.

**Example**:
```ephapax
fn outer(a: I32, b: I32, c: I32): I32 -> I32 =
  let unused = a + b in
  λ(x: I32) -> x + c  // Only uses `c`, but captures a, b, c, unused
```

### Solution

**Escape analysis** + **free variable analysis** to capture only necessary variables.

#### Architecture

**New module**: `ephapax-analysis`

```
src/ephapax-analysis/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── escape.rs      # Escape analysis
    ├── free_vars.rs   # Free variable analysis
    └── liveness.rs    # Variable liveness
```

#### Algorithm

1. **Free Variable Analysis**
   - Traverse lambda body AST
   - Collect all variable references
   - Exclude lambda parameters
   - Result: `Set<VarName>` of free variables

2. **Escape Analysis**
   - Determine if variables escape their scope (passed to lambdas, returned)
   - Mark non-escaping variables (can be stack-allocated)

3. **Minimal Capture Set**
   - Intersect free variables with escaping variables
   - Only capture variables in intersection

#### Integration

**Update `ephapax-wasm/src/lib.rs`**:

```rust
fn compile_lambda(&mut self, param: &str, body: &Expr) -> u32 {
    let free_vars = if self.optimize_closures {
        analyze_free_vars(body)  // Minimal set
    } else {
        self.locals.all_variables()  // Current: capture everything
    };

    // Emit capture code for `free_vars` only
    // ...
}
```

#### CLI Flag

```bash
ephapax compile program.eph --optimize-closures
```

#### Expected Impact

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Closure env size | 32 bytes | 8 bytes | 75% reduction |
| WASM binary size | 5.2 KB | 3.6 KB | 31% reduction |

### Implementation Steps

1. Create `ephapax-analysis` crate
2. Implement free variable analysis
3. Implement escape analysis
4. Integrate with lambda compilation
5. Add `--optimize-closures` CLI flag
6. Benchmark size reduction

### Verification

```bash
# Before optimization
ephapax compile closures.eph -o before.wasm
ls -lh before.wasm  # 5.2 KB

# After optimization
ephapax compile closures.eph --optimize-closures -o after.wasm
ls -lh after.wasm  # 3.6 KB (31% smaller)
```

---

## Implementation Timeline

### Completed (Week 1)
- ✅ Enhancement #1 Phase 1: Debug support (source maps + mode metadata)

### Recommended Priority Order

**Weeks 2-3**: Enhancement #2 (Package Manager)
- Critical for ecosystem growth
- Enables code reuse

**Week 4**: Enhancement #3 (Performance Benchmarks)
- Demonstrates competitiveness
- Guides optimization efforts

**Weeks 5-6**: Enhancement #4 (VS Code Extension)
- Improves developer experience
- Lowers barrier to entry

**Weeks 7-8**: Enhancement #5 (Closure Optimization)
- Binary size improvement
- Performance optimization

**Weeks 9-10**: Enhancement #1 Phases 2-4 (Complete Debugger)
- DWARF support
- DAP server
- VS Code integration

---

## Success Criteria

### Enhancement #1 ✅
- [x] Can compile with `--debug` flag
- [x] Source map generated correctly
- [x] Mode metadata in WASM custom section
- [ ] DWARF sections for lldb/gdb (Phase 2)
- [ ] DAP server for VS Code (Phase 3)
- [ ] Breakpoints and step-through (Phase 4)

### Enhancement #2 ⏳
- [ ] Can create `ephapax.toml` manifest
- [ ] Dependency resolution works
- [ ] Packages can be installed from registry
- [ ] Module imports work in code

### Enhancement #3 ⏳
- [ ] Benchmarks run in CI
- [ ] Comparison tables vs Rust/AssemblyScript
- [ ] Performance regressions detected

### Enhancement #4 ⏳
- [ ] Syntax highlighting works in VS Code
- [ ] LSP connected and functional
- [ ] Mode switcher updates status bar
- [ ] Extension published to marketplace

### Enhancement #5 ⏳
- [ ] Free variable analysis correct
- [ ] Closure env size reduced 10%+
- [ ] Binary size reduced measurably
- [ ] Correctness tests pass

---

## Known Issues

### Enhancement #1
- **gimli 0.31 API**: DwarfBuilder code exists but disabled due to API changes
  - `LineProgram::new()` signature changed
  - `EndianVec::as_slice()` doesn't exist (use `.slice()`)
  - Needs proper StringId → Vec<u8> conversion

### Future Risks

- **Enhancement #2**: Dependency resolution can be NP-hard (use SAT solver or backtracking with limits)
- **Enhancement #3**: Benchmark variance on CI runners (use multiple samples)
- **Enhancement #4**: VS Code API changes (pin to stable versions)
- **Enhancement #5**: Over-aggressive optimization could break correctness (extensive property-based testing)

---

## Related Documentation

- [docs/DEBUG-SUPPORT.md](docs/DEBUG-SUPPORT.md) - Phase 1 debug documentation
- [.machine_readable/STATE.scm](.machine_readable/STATE.scm) - Project state
- [examples/](examples/) - Example programs

---

**Last Updated**: 2026-02-07 19:04 UTC
**Next Review**: After Enhancement #2 completion
