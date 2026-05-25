<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Changelog

All notable changes to Ephapax are documented here.

## [Unreleased]

### Repository tidy (2026-05-25)
- **Cache purge**: removed 340 wrongly-tracked `.zig-cache-global/` files
  + stale `formal/.aux` references to deleted experimental files;
  added `.zig-cache-global/` to `.gitignore` to prevent regression.
- **Document consolidation**: deleted duplicate `CONTRIBUTING.adoc`
  (kept `.md`); deleted root-level OCaml test cruft.
- **Document taxonomy** — moved to `docs/` with date-stamped naming:
  - `formal/PRESERVATION-HANDOFF.md` → `docs/sessions/SESSION-2026-05-24-preservation-handoff.md`
  - `formal/INTERACTIVE-PROOF-SESSION.md` → `docs/sessions/SESSION-2026-03-28-interactive-proof.md`
  - `formal/DESIGN-NOTE-2026-03-28*.md` → `docs/specs/`
  - `PROOF-NEEDS.md` / `TEST-NEEDS.md` / `TOPOLOGY.md` (root) → `docs/specs/`
  - `arcvix-*.tex` (root) → `docs/papers/`
  - `llm-warmup-{dev,user}.md` (root) → `docs/ai/`
  - `aqueduct.eph` (root) → `examples/advanced/`
- **Path refs updated** in `README.adoc`, `ROADMAP.adoc`,
  `EXPLAINME.adoc`, `RUST-SPARK-STANCE.adoc`.
- `formal/` now contains only the canonical Coq sources +
  build glue.
- **Hypatia scan triage**: added `docs/specs/KNOWN-PROOF-DEBT.md`
  cataloguing every flagged item with closure path or acceptance
  rationale (including 4 false positives where the scanner matches
  the words `axiom` / `believe_me` / `assert_total` inside comments).
  `SECURITY.md` links to it.

### Proof state (2026-05-20 → 2026-05-21)
- **Coq `preservation` reduction campaign**: 910 open goals → 12 (98.7% reduction). PR chain:
  - **#92** — honest framing: replaced unsubstantiated "Qed 2026-04-27" claim with `Admitted.`
  - **#102** — 910 → 29: standard preservation pattern (`remember (mu, R, e) as cfg`)
  - **#104** — quantitative status correction in docs
  - **#106** — 29 → 22: universal-IH revert (`revert mu R e mu' R' e' Hcfg Hcfg'` before `induction Hstep`)
  - **#114** — region-invariance lemma `step_R_eq_or_touches_region` (Qed-closed; infrastructure)
  - **#115** — corrected Idris2 region-linearity theorem names in docs
  - **#116** — 22 → 12: per-case manual closures of 10 β-reduction / value-step constructors
  - **#117** — canonicalised 5-phase closure plan in ROADMAP §"Preservation closure plan"
  - **#121** — Phase 1 scaffold: `step_output_context_eq` (Lemma B) stated with induction skeleton

- **Idris2 `%default partial → total` campaign** (2026-05-20): merged 9 PRs (#89, #90, #91, #93, #94, #96, #97, #99, #100) tightening totality across the parser / typechecker / IR-codec layer. 80+ atomic functions now provably total; zero `assert_total` / `believe_me` / `assert_smaller` introduced; 14 retained `covering` markers for documented Idris2 0.8.0 SCT limits.

### Documentation
- **#113** — README + ROADMAP + EXPLAINME refactored for outside readers; documentation map; quickstart-by-audience; proof status tables.
- Wiki refresh — `Home.md` rewritten as nav hub; new `Proof-status.md`; 6 topic guides added (Linear-and-affine, Region-calculus, Two-phase-compiler, What-can-go-wrong, Comparison-to-other-languages, Glossary); `_Sidebar.md` for persistent nav.
- Repo description + topics — added `agda`, `idris2`, `webassembly`, `formal-verification`, `affine-types`, `region-calculus`, `compiler`, `operational-semantics`, `programming-language`.

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
