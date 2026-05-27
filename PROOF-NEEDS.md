<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Proof needs — Ephapax (linear + affine sublanguages)

> ## 🛑 First-read disambiguation (human + machine readers)
>
> **This document is for `hyperpolymath/ephapax`.** Ephapax is a research
> language for compile-time WebAssembly memory safety, formally verified
> in Coq + Idris2.
>
> **Ephapax is NOT `hyperpolymath/affinescript`.** AffineScript is a
> separate, unrelated language (JS/TS/ReScript successor, OCaml + ReScript
> runtime, no mechanised proofs, no first-class regions). The two share
> only the compile target (`hyperpolymath/typed-wasm`).
>
> **`ephapax-affine` (in this document) is the affine *sublanguage* of
> Ephapax** — the versatile prototyping companion to `ephapax-linear`.
> It lives inside this repo (`ephapax-linear/` crate). **It is NOT
> AffineScript.** The lexical overlap of the word `affine` is a
> coincidence of substructural-logic terminology, not a project
> relationship. Do not apply lessons or tactics across the boundary.
>
> If you found this document by searching for "affine type system",
> verify which language you actually need before proceeding. Canonical
> side-by-side table:
> https://github.com/hyperpolymath/nextgen-languages/blob/main/docs/disambiguation/ephapax-vs-affinescript.md

## Reading guide

This file is the *proof-debt audit* for Ephapax post-counterexample
(2026-05-26). It supersedes earlier versions of `PROOF-NEEDS.md` that
still referenced the legacy preservation closure plan as if it were
viable.

The audit is split by sublanguage:

* **§1** — what's done (mechanised, Qed) for each sublanguage.
* **§2** — what's todo (active work, by layer).
* **§3** — what's banned (explicit do-not-do anti-patterns).
* **§4** — counts and file-by-file map.

For the architectural background see
[`STATUS.adoc`](STATUS.adoc) and
[`formal/PRESERVATION-DESIGN.md`](formal/PRESERVATION-DESIGN.md).

---

## §1. What's done

### ephapax-linear (strict / obligation-preserving sublanguage)

| Component | File | Status |
|---|---|---|
| L1 judgment (`has_type_l1`) | `formal/TypingL1.v` | 100% — 0 admits, 2 Qed |
| L1 judgment indexed by modality `m : Modality` | `formal/TypingL1.v` | landed via PRs #176 + #177 |
| L2 modality core (`Modality.v`, `linear_to_affine`) | `formal/Modality.v` | 1 Qed, zero axioms |
| L3 calculus (echo / residue fiber + degrade + no-section proof) | `formal/Echo.v` | 12 Qed, 0 admits |
| Linear-mode forward progress lemmas | `formal/Semantics_L1.v` | 23 Qed; 3 residual admits (L2-β follow-up) |
| Counterexample regression witness | `formal/Counterexample.v` | 5 Qed (`bad_input_untypable_l1` proved under both modes) |
| Operational checker (Rust, ephapax-linear sublanguage) | `ephapax-linear/src/linear.rs` | working — discharges resource-exact obligation |

### ephapax-affine (relaxed / degradable sublanguage)

| Component | File | Status |
|---|---|---|
| Affine-mode judgment indexing | `formal/TypingL1.v` (`m = Affine` branch) | landed; 3 Affine-only rules `T_Lam_L1_Affine`, `T_Case_L1_Affine`, `T_If_L1_Affine` |
| Linear ⇒ Affine weakening | `formal/TypingL1.v` `linear_to_affine` | Qed, zero axioms |
| Operational checker (Rust, ephapax-affine sublanguage) | `ephapax-linear/src/affine.rs` | working — permits weakening / graceful abandonment |
| Affine-mode echo discipline (LEcho Affine = lowered triple) | `formal/Echo.v` (calculus) | calculus done; rule wiring pending |
| Affine forward progress lemmas | `formal/Semantics_L1.v` | bullet-structure rewrites + subst_typing_gen_l1_m + region_shrink_preserves_typing_l1_gen_m m-polymorphic generalisations landed 2026-05-27; remaining 3 admits are L2-β deeper-than-bullet debt (see §2) |

### Counterexample regression

| Lemma | Status | What it shows |
|---|---|---|
| `bad_input_untypable_l1` | Qed | the configuration that steps-and-untypes is rejected at type check under the new L1 judgment, in both Linear and Affine modes |
| 4 supporting lemmas | Qed | the legacy judgment *types* the same configuration |

→ The counterexample establishes the gap. The new L1 judgment closes it.

---

## §2. What's todo

### Near-term (L1 ⇒ L2 integration debt — mechanical)

| Item | File | Estimate |
|---|---|---|
| ✅ Close 3 pure bullet-structure regressions (typing_preserves_bindings_l1, unrestricted_flag_unchanged_l1, shift_typing_gen_l1) | `formal/Semantics_L1.v` | done 2026-05-27 |
| ✅ Generalise typing_preserves_length_l1 to modality-polymorphic | `formal/Semantics_L1.v` | done 2026-05-27 |
| ✅ Generalise subst_typing_gen_l1 to modality-polymorphic + Linear wrapper (also generalised typing_preserves_bindings_l1, output_shape_at_l1, loc_retype_at_R_l1) | `formal/Semantics_L1.v` | done 2026-05-27 (L2-β follow-up #2) |
| ✅ Restore region_shrink_preserves_typing_l1_gen bullet structure via m-polymorphic helper (residual list-vs-multiset structural admit isolated to T_Region_Active_L1 shadowed case inside _gen_m) | `formal/Semantics_L1.v` | done 2026-05-27 (L2-β follow-up #3) |
| Close T_Region_Active_L1 [rr = r] shadowed sub-case of region_shrink_preserves_typing_l1_gen_m (list-vs-multiset bridge — option (a) L1 perm lemma, (b) multiset reformulation, or (c) T_Region_*_L1 redesign per the case's own note) | `formal/Semantics_L1.v` | structural; non-trivial — investigation owed; lambda-body's shadowing internal ERegion is the obstacle |
| State and prove `preservation_l1` for both modes | `formal/Semantics_L1.v` | depends on region_shrink + region_liveness narrow admit |

### Near-term (L3 wiring — design + mechanisation)

L3 calculus is done in `formal/Echo.v` (12 Qed, no admits). What's missing
is the *integration* into the typing judgment and the step rules.
The shape is laid out in `formal/PRESERVATION-DESIGN.md §6.3` "Where echo
enters the typing rules" and (for the diagram) in §6 (to be added).

| Item | What it does | Notes |
|---|---|---|
| ✅ Extend AST with [TEcho : ty -> ty] and [EEcho : ty -> expr -> expr] | Type former + runtime value form for L3 echoes | done 2026-05-27 (L3 wiring slice 1 — Syntax.v + free_regions + value/shift/subst cases) |
| ✅ Add `T_Observe_L1` typing rule + `EObserve` expr form | Consumes a `TEcho T` echo, returns `TBase TUnit` | done 2026-05-27 (L3 wiring slice 2 — modality-polymorphic single rule; mandatoriness via `is_linear_ty TEcho`/implicit-drop discipline is a follow-up) |
| ✅ Add `T_Echo_L1` typing rule | Types runtime [EEcho T v] residue values at `TEcho T` | done 2026-05-27 (L3 wiring slice 3a — typing-side counterpart of forthcoming `S_Region_Exit_Echo` / `S_Drop_Echo` step rules; mode-polymorphic) |
| ✅ Add parallel typing rules `T_Region_L1_Echo` / `T_Region_Active_L1_Echo` / `T_Drop_L1_Echo` | Output `TEcho T` instead of `T` / `TBase TUnit`. Programs choose at typing time which path | done 2026-05-27 (L3 wiring slice 3b — owner-approved parallel-rule strategy). +3 internal admits in [region_shrink_preserves_typing_l1_gen_m] + [region_liveness_at_split_l1_gen] are parallel-rule MIRRORS of pre-existing structural admits, NOT new structural debt |
| ✅ Add collapse-function emission to step rules at irreversible boundaries | `S_Region_Exit_Echo` emits `EEcho T v` paralleling `S_Region_Exit` (untouched); `S_Drop_Echo` emits `EEcho T (ELoc l r)` paralleling `S_Drop` | done 2026-05-27 (L3 wiring slice 3c — owner-approved parallel-rule strategy in Semantics.v; updated `step_from_eregion` to 4-disjunct classification + `step_R_change_shape` + `no_leaks_gen` cascade); rules quantified over witness type T |
| ~~Thread `G` (echo context) alongside `R` (region context) through compound rules~~ | ~~New context parameter on every L1 compound rule~~ | **OBSOLETE 2026-05-27**: under the owner-approved parallel-rules design (slices 3a–3c), echoes are values of type `TEcho T` that flow through the existing `ctx` G. No separate echo-context parameter is needed. |
| State and prove `preservation_l3` | Per-layer preservation theorem against the L3 invariants for the new echo-emitting step rules + echo-typed paths | Cross-layer dependency annotated in `PRESERVATION-DESIGN.md §5.1`. The four prerequisite slices (1, 2, 3a, 3b, 3c) all landed; `preservation_l3` is the capstone. |

### Mid-term (L4 — not started)

L4 covers dyadic interaction semantics (mother–child distinction).
Design lives in `formal/PRESERVATION-DESIGN.md §7`. No file, no mechanisation
yet. To be approached only after L3 wiring lands.

### Value-prop directions (committed and speculative)

| Direction | Status | Proof obligation |
|---|---|---|
| Linear Echo + Region-Based Memory Management (S_Region_Exit certified-evidence emission) | Committed for v1 | `preservation_l3` for the Region branch |
| Selective reversibility via L2 modality (Linear ≤ Affine thin-poset) | Committed for v1 | Already mechanised in `Modality.v` |
| Debugging / provenance via Linear Echoes as type-system receipts | Committed for v1 | Follows from L3 wiring |
| Linear discipline on deterministic drop (Rust-style) for critical resources | Speculative | Compatible with L3 wiring; not committed v1 |
| GDPR-style certified erasure as compliance use-case | Direction | Concrete instantiation; no separate proof obligation |

---

## §3. What's NOT to do (banned anti-patterns)

These are not preferences. They are explicit, durable, owner-issued
2026-05-27 directives.

### A. Do not close the legacy preservation theorem

* ❌ `Theorem preservation` in `formal/Semantics.v` is **provably false**.
  No proof closes it. The `Admitted.` is correct. Leave it.
* ❌ Do not add lemmas to `formal/Semantics.v` aimed at that closure.
  Examples that have wasted real session time:
  * Lemma B variants (`step_preserves_type`,
    `step_output_context_eq`, `step_preserves_type_at_pre`,
    `step_output_context_eq_at_pre`)
  * `region_add_typing_for_non_values`
  * Strengthened substitution lemmas
  * `sibling_typing_transfers_across_step`-style helpers
* ❌ Do not patch the legacy `formal/Typing.v` judgment.
  `Counterexample.v` depends on its falsity.

### B. Do not close L1/L2 admits by ad-hoc cross-layer reasoning

* ❌ `region_liveness_at_split_l1` (if it returns) must NOT be closed
  by adding proof tricks, side conditions discharged ad-hoc, or
  strengthened lemma signatures within the current judgment shape.
  Post-L2-hybrid these closures are cross-layer; the layered design
  intentionally splits some closures across layers.
* ❌ The 9 Semantics_L1.v admits are L2-integration debt (bullet
  structure for new Affine constructors). They are *not* invitations
  to introduce new `Axiom` declarations.

### C. Do not bake linearity into Echo Types

Echo semantics (L3) and structural discipline (L2) must remain
orthogonal and compositional.

* ❌ Do not write `LinearEcho` and `AffineEcho` as separate type
  formers. There is **one** type former (the fiber); the two modes
  are *applications* of it with different witness shapes.
* ❌ Do not pattern-match on `Linear`/`Affine` inside `Echo.v`.
  The discipline is read from L2's `m : Modality` at the typing-rule
  boundary, not inside the calculus.

### D. Do not treat Echo Types as a tracing-GC replacement

* ❌ Echo Types do not solve reachability or cycles.
* ❌ Echo Types are not a "fire-and-forget" automatic memory manager.
* ✅ Echo Types are a *type-theoretic discipline for accountability of
  irreversible reclamation* — strongest in conjunction with RBMM
  (regions) or deterministic ownership (Rust-style drop).

### E. Do not follow pre-2026-05-26 plans

* ❌ Anything dated before 2026-05-26 that proposes closing
  `preservation` to `Qed.` is pre-discovery. PRs #92, #102, #104,
  #106, #114, #116, #117, #121, #146 are archaeology.
* ❌ Branch `lemma-b-phase2-middle-narrow` (deleted post-archaeology
  cherry-pick) was the most recent pre-discovery attempt. Do not
  resurrect.

### F. Do not conflate `ephapax-affine` with AffineScript

* ❌ `ephapax-affine` lives in this repo's `ephapax-linear/` crate
  alongside `ephapax-linear`. It is a *sublanguage* of Ephapax.
* ❌ `AffineScript` (`hyperpolymath/affinescript`) is a different
  language with no source-level overlap. Borrow-checker tactics from
  `affinescript/lib/borrow.ml` do not apply here, and vice versa.
* ❌ The lexical overlap of the word `affine` is a coincidence.
  Substructural-logic family terminology, not project relationship.

### Anti-pattern detector

If your session is producing any of the following, **stop and escalate
to the owner**:

* `sibling-region-disjointness` side conditions on compound rules
* region-weakening predicates indexed on syntactic shape
* admit-shuffling between `Semantics.v` and a new lemma file
* "the previous-PR-line-of-attack just needs one more lemma"
* proposing to close `Theorem preservation` in `Semantics.v` to `Qed.`
  by any chain of reasoning
* adding new `Axiom` declarations to discharge L1/L2 gaps
* writing a `LinearEcho` distinct from an `AffineEcho`
* applying tactics or framings from `hyperpolymath/affinescript` here

---

## §4. Counts + file-by-file map

### Per-file Qed / Admitted summary (as of 2026-05-27)

| File | Qed | Admitted | Disposition |
|---|---:|---:|---|
| `formal/Semantics.v` (legacy) | n/a | **3** | 🛑 archaeology — do not extend |
| `formal/Typing.v` (legacy) | n/a | 0 | 🛑 archaeology — `Counterexample.v` depends on falsity |
| `formal/Counterexample.v` | **5** | 0 | ✅ pinned regression witness |
| `formal/TypingL1.v` | **2** | 0 | ✅ active — L1 judgment, modality-indexed |
| `formal/Semantics_L1.v` | **23** | **3** | ✅ active — bullet-structure regressions + subst_typing_gen_l1_m + region_shrink_preserves_typing_l1_gen_m closed 2026-05-27; 3 residual admits are deeper L2-β debt (region_shrink T_Region_Active_L1 list-vs-multiset case now isolated in _gen_m internal admit, region_liveness_at_split narrow admit per ERegion counterexample, preservation_l1 cap) |
| `formal/Modality.v` | **1** | 0 | ✅ active — L2 core, zero axioms |
| `formal/Echo.v` | **12** | 0 | ✅ active — L3 calculus, not yet wired into L1 |
| `formal/TypingL2.v` | (wrapper) | (wrapper) | ✅ thin re-indexing through `TypingL1.has_type_l1` |
| `src/abi/Ephapax/…` (Idris2) | n/a | n/a | ✅ active — ABI, Region linearity, no `believe_me` / `sorry` / `assert_total` |

### Idris2 side (proof carriers, not Coq mechanisation)

| Concern | File(s) | Status |
|---|---|---|
| Region linearity | `src/formal/Ephapax/Formal/RegionLinear.idr` | working — explicitly "REAL proof — not believe_me, not assert_total" |
| ABI surface (17 files) | `src/abi/Ephapax/…` | working — clean of `believe_me` / `sorry` |

### Tools

* **Coq 8.18+** for `formal/*.v` — primary mechanisation.
* **Idris2 0.8.0** (needs `IDRIS2_PREFIX` pointing at a prefix with TTCs)
  for `src/abi/Ephapax/…`.
* **Just** as the build orchestrator (`just proofs`, `just idris-build`,
  `just golden`).

### Build oracles

* `coqc 8.18.0` is the **only authoritative answer** to "is this proved?"
  for `.v` files. Comments in source claiming `Qed` without `coqc`
  acceptance are not evidence.
* `idris2 --check` is the same for `.idr` files.
* Both are wired into `rust-ci.yml`'s "Coq proofs" and "Idris2 build"
  jobs.

---

## Cross-references

* [`STATUS.adoc`](STATUS.adoc) — past / present / future temporal map.
* [`formal/PRESERVATION-DESIGN.md`](formal/PRESERVATION-DESIGN.md) —
  canonical four-layer design doctrine.
* [`CLAUDE.md`](CLAUDE.md) — agent guidance; owner directive 2026-05-27.
* [`formal/Counterexample.v`](formal/Counterexample.v) — the 5 Qed
  lemmas that pin the soundness gap.
* [`https://github.com/hyperpolymath/echo-types`](https://github.com/hyperpolymath/echo-types)
  — upstream Agda foundation for L3.
* [Disambiguation: ephapax vs AffineScript](https://github.com/hyperpolymath/nextgen-languages/blob/main/docs/disambiguation/ephapax-vs-affinescript.md)
  — canonical side-by-side table.
