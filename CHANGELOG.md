<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Changelog

All notable changes to Ephapax are documented here.

## [Unreleased]

### Governance, CI & security-scan infrastructure (2026-06-24)

- **Governance model formalised** (PR #314): added `.github/CODEOWNERS`
  (review routing, sole-maintainer model), `GOVERNANCE.adoc`, and
  `MAINTAINERS.adoc`. Salvaged from the closed estate-standardization
  branch onto a clean base; prose headers normalised to `CC-BY-SA-4.0`.
- **`standards` reusable-workflow pins remediated** (PR #315): re-pinned
  `governance.yml` / `hypatia-scan.yml` / `scorecard.yml` away from
  `5a93d9d57cc0` — a ref that is **not** an ancestor of `standards` HEAD,
  which broke `governance / Check Workflow Staleness` and made the Hypatia
  reusable workflow reference a dead `actions/cache` SHA — to a published
  HEAD. Subsequently bumped to the current `d135b05…` (PR #316).
- **Hypatia neurosymbolic scan unblocked** — with the pin fixed, the
  `scan / Hypatia Neurosymbolic Analysis` gate now runs to completion
  instead of dying at "Prepare all required actions". It reports **37
  pre-existing findings** (5 critical, 7 high, 25 medium) — repo debt the
  broken pin had been masking, **not** introduced here. Triage + fix is
  **handed off** (see `docs/governance/HYPATIA-HANDOFF.md`); a visibility
  patch for `standards`' `hypatia-scan-reusable.yml` (publish findings on
  failure rather than aborting opaquely under `bash -e`) is **drafted but
  not yet applied**.
- **Stale PRs closed**: #310 (disjoint history; reintroduced fenced legacy
  preservation work) and #311 (superseded — features already on `main`).

### Proof + stdlib wave (2026-06-01 → 2026-06-02)

- **P43 — canonical-forms L1 modality-polymorphic** (PR #274): port
  `canonical_{unit,bool,i32,fun,prod,sum,string}_l1_m` to the
  modality-polymorphic L1 judgment. All 7 axiom-free (verified via
  `Print Assumptions`). Prerequisite for `progress_l1` (P42).
- **P10 / P32 — Print Assumptions audit framework** (PR #270): per-
  module whitelist guards mechanically certifying which axioms each
  layer-keystone surfaces. `tfuneff_lambda_retype_l1_m` /
  `subst_typing_gen_l1_m_tfuneff` etc. confirmed zero-axiom; the
  expected residuals (`preservation_l1`, `region_liveness_at_split_l1_gen`,
  `region_shrink_preserves_typing_l1_gen_m`) listed.
- **P06 — `step_pop_disjoint_from_type_l1` partial proof** (PR #280):
  stated + EASY cases Qed-closed (atomic non-region step rules; region
  Enter/Exit/Exit_Echo; StringConcat; App_Step1; Fst/Snd; Borrow;
  Drop; Copy). HARD cases (Let / LetLin / App_Step2 / If / Pair_Step
  / Inl / Inr / Case / Region_Step T_Region_L1) Admitted, tracked
  under issues #240 / #241 / #242.
- **P28 — Rust↔Coq `is_linear_ty` bridge** (PR #273): kernel truth
  table mechanically asserted. Pins the cross-language contract.
- **P59 — OwnershipKind from_byte/to_byte round-trip** (PR #277):
  typed-wasm ADR-0002 carrier handshake locked in Coq.
- **D04 — Transactions as linear scopes** (PR #275): ACID semantics
  via affine sublanguage.
- **D11 — Allen's interval algebra** (PR #272): from DB-theory inventory.
- **D17 — exactly-once `MessageHandle` as linear typestate** (PR #279).
- **D18 — monoidal aggregates** (PR #281): `Sum`/`Product`/`Max`/`Min`/
  `Count`/`And`/`Or`/`String` instances.
- **Truth restore + banned-preservation burial** (PR #263): doc-code
  consistency for proof state.
- **Cluster D meander** (PR #278): L3/L4 status refresh + error-code
  reconciliation + stale counts/paths.
- **CI — coq-build noble apt** (PR #282): switch from
  coqorg/coq:8.18 + `--user root` quirks to ubuntu-latest + apt-coq,
  ~37s one-shot (unblocks ~5 PRs).
- **CI — Track C panic-attack triage** (PR #271): classify findings
  per #138.
- **Governance — R5b standards SHA bump** (PR #276): consume
  version-string drift detection from standards#329.

### Phase 3b Stage 1a + 1b — L2 effect-typed TFun + L3 wiring conditional preservation (2026-05-30 → 2026-05-31)

- **Stage 1a (PR #252, merged 2026-05-30 17:42Z)**: `tfuneff_lambda_free`
  + `Counterexample_L2_nested.v`. Admin-merged after local build oracle
  GREEN with no axiom slippage (only the known-good
  `region_liveness_at_split_l1_gen` axiom).
- **Stage 1b (PR #253)**: L1/L2 plumbing for the effect-typed `TFun` track —
  `expr_closed_below` + closure helpers (Syntax.v), body-transfer + closed-
  value G-poly helpers, `subst_typing_gen_l1_m_tfuneff` Qed (zero axioms),
  and `preservation_l2` β-case for closed `TFunEff` substituents. Builds
  toward the unconditional `preservation_l2` track per
  `PRESERVATION-DESIGN.md §12.x`.

### L3 wiring + L4 Phase A scaffold (2026-05-27 → 2026-05-28)

- **L3 wiring (slice 4, 2026-05-27)**: `preservation_l3_region_active_echo`,
  `preservation_l3_drop_echo`, and the `preservation_l3` umbrella all Qed in
  `formal/Semantics_L1.v` — each conditional on the
  `region_shrink_preserves_typing_l1_gen_m` L1 structural admit. The
  avoidable `T_Region_L1_Echo` mirror was closed in the same slice. Zero new
  admits introduced.
- **L4 Phase A scaffold (2026-05-28)**: `formal/L4.v` lands with `ProgramMode`
  (`PModeLinear` / `PModeAffine` / `PModeBoundaryMix`) and
  `program_mode_to_modality` round-trip. Definitions only by design — no
  theorems, no admits, no axioms.

### Four-layer preservation redesign (2026-05-26 → 2026-05-27)

- **L1 — region capabilities** (PRs #153-line, integration branch
  `proof/l1-region-threading-design`): introduces `has_type_l1` with
  R-threading in `formal/TypingL1.v`. Supporting lemmas in
  `formal/Semantics_L1.v`. Counterexample regression (`bad_input_untypable_l1`)
  Qed in `formal/Counterexample.v`. `preservation_l1` Admitted with 1
  residual inner `admit.` covering App / Pair / StringConcat (lambda-
  rigidity gap per `PRESERVATION-DESIGN.md §4.8`).
- **L2 — Linear/Affine modality** (PR #176, this entry): `has_type_l1`
  carries `m : Modality` parameter so a single judgment specialises to
  ephapax-linear AND ephapax-affine. New `formal/Modality.v` with K-free
  thin poset (`modality_le` at `Type` sort + `_refl`/`_trans`/`_prop`).
  Mode-split constructors for `T_Lam` / `T_Case` / `T_If`; remaining 21
  rules modality-polymorphic. **`linear_to_affine` Qed, closed under the
  global context (zero axioms).** Mirrors `EchoLinear.agda:38-58`'s
  `weaken : LEcho linear → LEcho affine`. `weaken_modality` at the L2
  layer dispatches through `linear_to_affine`. Six pre-L2 `Semantics_L1.v`
  lemmas regressed to `Admitted` (bullet-structure rewrite needed for
  the 3 new Affine-only constructors); restoration tracked as L2-β.
  `Counterexample.bad_input_untypable_l1` generalised to `forall m,
  ~ has_type_l1 m ...` — Qed under both indices.
- **L3 — Echo / residue** (PRs #166, #167-line, parallel track):
  `formal/Echo.v` scaffold with `Mode + LEcho + decoration-commuting
  weakening`; `EchoR` residue + no-section irreversibility headline.
  Decouples residue layer from typing layer; couples through L2's
  thin-poset structure.
- **Disambiguation, durable**: `ephapax-affine ≠ AffineScript`. They are
  separate languages sharing only the typed-wasm target. Per `README`,
  `CLAUDE.md`, `.machine_readable/disambiguation.a2ml` hooks landed via
  PRs #152 / affinescript#393 / typed-wasm#73.

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
