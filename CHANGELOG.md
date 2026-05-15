<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Changelog

All notable changes to Ephapax are documented here.

## [Unreleased]

### Added
- **typed-wasm L7+L10 integration** (closes the typed-wasm-verify loop for ephapax):
  - **C6 (#70)** — `ephapax-wasm` emits an `affinescript.ownership` custom section on every compile when any user fn has a Linear parameter. Section format and encoder come from the new `typed-wasm-verify` Rust crate (`hyperpolymath/typed-wasm:crates/typed-wasm-verify/`, rev `e11bb985` at C6, bumped to `67006edd` at C7). Driven by `Ty::is_linear()`; entries sorted by `func_idx` for deterministic output. 4 new unit tests; `cargo test --workspace` clean.
  - **C7 (#72)** — New `--verify-ownership` flag on `ephapax compile`. After codegen and before output write, runs `typed_wasm_verify::verify_from_module` on the emitted module and surfaces any aliasing / linearity violation as a non-zero exit. Output: `✓ typed-wasm L7+L10 verification: clean` on success; per-violation diagnostics on failure. 3 new integration tests spawn the built binary.
  - Net effect: ephapax-emitted wasm now has end-to-end L7+L10 guarantees — producer side (custom section emission) + opt-in consumer side (verifier flag), both backed by the canonical Rust verifier shared with `hyperpolymath/typed-wasm`.
- `module Qualified.Name` declarations (dotted module paths)
- `--` Haskell-style line comments (alongside existing `//` and `/* */`)
- Qualified names in imports: `import Foo.Bar.Baz`
- `linear type` and `affine type` modifiers on type definitions
- `const_decl`: module-level `let NAME = expr` bindings
- `named_record_type_def`: `Type = Constructor { field: Type, ... }` syntax
- `->` return type syntax (alongside existing `:`)
- `region name:` colon syntax (alongside `region name { }`)
- `Decl::Const` variant in the AST for module-level constants

### Fixed
- Keyword word-boundary fix: identifiers like `init_result` no longer blocked by `in` keyword match

### Changed
- Parser hardened: 80 production unwraps eliminated, proper ParseError propagation
- License headers: 13 files migrated from EUPL-1.2 to PMPL-1.0-or-later
- Test unwraps replaced with `.expect()` for better diagnostics

## [0.8.0] - 2026-03-16
- 80 examples across 8 categories
- Region-linear fusion type system
- `__ffi()` intrinsic for foreign function interface
- 15 compiler crates

## [0.7.0] - 2026-02-15
- Initial public release
- Linear type system with region annotations
- Pattern matching, modules, error handling
- REPL and interpreter

[Unreleased]: https://github.com/hyperpolymath/ephapax/compare/v0.8.0...HEAD
[0.8.0]: https://github.com/hyperpolymath/ephapax/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/hyperpolymath/ephapax/releases/tag/v0.7.0
