<!-- SPDX-License-Identifier: MPL-2.0 -->
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
| Linear-mode forward progress lemmas | `formal/Semantics_L1.v` | 37 Qed; 3 outer `Admitted.` markers cover 5 internal `admit.` cases at current lines 576/646/1994/2014/3132. Phase 3b Stage 1a (#252, MERGED 2026-05-30: `tfuneff_lambda_free` + `Counterexample_L2_nested.v`) and Stage 1b (#253, MERGED 2026-05-31: closed-value substitution + `preservation_l2_app_eff_beta` β-case for TFunEff). Slice 4 L3 wiring delivered `preservation_l3_region_active_echo` / `preservation_l3_drop_echo` / `preservation_l3` umbrella. |
| L2 β-case lemmas (Stage 1b) | `formal/TypingL2.v` | 10 Qed total: `weaken_modality` family (5), `preservation_l2_via_l1` (conditional on `preservation_l1`), `linear_value_retype_l1_m`, and 3 `preservation_l2_app_eff_beta_*` variants (Linear / ground_nonlinear / tfuneff conditional on Stage 1b side conditions P1+P2+P3). Stage 2/3/4 (#240/#241/#242) drop the conditions. |
| L4 labelling scaffold (Phase A, 2026-05-28) | `formal/L4.v` | `ProgramMode` enum (`PModeLinear` / `PModeAffine` / `PModeBoundaryMix`) + `program_mode_to_modality` round-trip. Definitions only — no theorems, zero axioms. |
| Counterexample_L2 regression witnesses (Phase 4c + 3b) | `formal/Counterexample_L2.v`, `formal/Counterexample_L2_nested.v` | 5 + 5 Qed pinning the Phase 4c (fresh-region scope crossing) and Phase 3b (nested TFunEff) soundness-gap classes |
| Counterexample regression witness | `formal/Counterexample.v` | 5 Qed (`bad_input_untypable_l1` proved under both modes) |
| Operational checker (Rust, ephapax-linear sublanguage) | `ephapax-linear/src/linear.rs` | working — discharges resource-exact obligation |

### ephapax-affine (relaxed / degradable sublanguage)

| Component | File | Status |
|---|---|---|
| Affine-mode judgment indexing | `formal/TypingL1.v` (`m = Affine` branch) | landed; 3 Affine-only rules `T_Lam_L1_Affine`, `T_Case_L1_Affine`, `T_If_L1_Affine` |
| Linear ⇒ Affine weakening | `formal/TypingL1.v` `linear_to_affine` | Qed, zero axioms |
| Operational checker (Rust, ephapax-affine sublanguage) | `ephapax-linear/src/affine.rs` | working — permits weakening / graceful abandonment |
| Affine-mode echo discipline (LEcho Affine = lowered triple) | `formal/Echo.v` (calculus) | calculus done; rule wiring pending |
| Affine forward progress lemmas | `formal/Semantics_L1.v` | bullet-structure rewrites + `subst_typing_gen_l1_m` + `region_shrink_preserves_typing_l1_gen_m` m-polymorphic generalisations landed 2026-05-27; Phase 3b Stage 1a + 1b landed 2026-05-30/31 via #252 + #253. Remaining admits are pre-existing L1 structural debt + one provably-false-as-stated sub-case (`Semantics_L1.v:1994` / mirror `:2014` — closure requires Phase D reformulation, not direct proof). See §4 seam audit. |

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
| ✅ Add parallel typing rules `T_Region_L1_Echo` / `T_Region_Active_L1_Echo` / `T_Drop_L1_Echo` | Output `TEcho T` instead of `T` / `TBase TUnit`. Programs choose at typing time which path | done 2026-05-27 (L3 wiring slice 3b — owner-approved parallel-rule strategy). Initial +3 internal admits in [region_shrink_preserves_typing_l1_gen_m] + [region_liveness_at_split_l1_gen] were parallel-rule MIRRORS of pre-existing structural admits; the avoidable T_Region_L1_Echo mirror was CLOSED in slice 4 — only the two true T_Region_Active_*_L1_Echo shadowed-case mirrors remain, both blocked by the same pre-existing list-vs-multiset structural debt as the originals |
| ✅ Add collapse-function emission to step rules at irreversible boundaries | `S_Region_Exit_Echo` emits `EEcho T v` paralleling `S_Region_Exit` (untouched); `S_Drop_Echo` emits `EEcho T (ELoc l r)` paralleling `S_Drop` | done 2026-05-27 (L3 wiring slice 3c — owner-approved parallel-rule strategy in Semantics.v; updated `step_from_eregion` to 4-disjunct classification + `step_R_change_shape` + `no_leaks_gen` cascade); rules quantified over witness type T |
| ~~Thread `G` (echo context) alongside `R` (region context) through compound rules~~ | ~~New context parameter on every L1 compound rule~~ | **OBSOLETE 2026-05-27**: under the owner-approved parallel-rules design (slices 3a–3c), echoes are values of type `TEcho T` that flow through the existing `ctx` G. No separate echo-context parameter is needed. |
| ✅ State and prove `preservation_l3` | Per-layer preservation theorem against the L3 invariants for the new echo-emitting step rules + echo-typed paths | done 2026-05-27 (L3 wiring slice 4 — capstone). Two per-case Qed lemmas (`preservation_l3_region_active_echo` for `S_Region_Exit_Echo` × `T_Region_Active_L1_Echo`, and `preservation_l3_drop_echo` for `S_Drop_Echo` × `T_Drop_L1_Echo`) plus an umbrella `preservation_l3` (their conjunction, Qed). Zero new admits or axioms. Per-case alignment forced by `T_Echo_L1`'s witness-type premise; non-deterministic crossover cases are non-preserving by design (typing derivation pins the path). Conditionally Qed under the pre-existing `region_shrink_preserves_typing_l1_gen_m` L1 structural admit per PRESERVATION-DESIGN.md §5.1. |
| ⏸ Register `TEcho` as linear via `is_linear_ty` (Phase B Slice 1) — DEFERRED 2026-05-28 | Realises the design intent annotated at `TypingL1.v:T_Observe_L1`: under Linear discipline, unobserved `TEcho` must fail typing closure | **deferred until Phase D**. Investigation 2026-05-28: adding `| TEcho _ => true` to `is_linear_ty` is structurally non-vacuous at L1 — `EEcho T v` is both a value (`VEcho`) and typed at `TEcho T` (via `T_Echo_L1`, TypingL1.v:351-354), refuting the conclusion of `linear_value_is_loc_l1` (Semantics_L1.v:891) and breaking 9 call-sites in `subst_typing_gen_l1_m` (Semantics_L1.v:1326-1605, Qed). Realising the wire requires a disjunctive rewrite of `linear_value_is_loc_l1` plus per-caller handling of the TEcho disjunct — substantially larger than the original "1-line definitional" framing. Owner deferred to after Phase D (L2 effect-typed TFun) when the L1 substitution chain reshapes naturally. The legacy `Semantics.v` branch is vacuous (no rule produces `TEcho`) and would have closed trivially. |
| ⏸ Close the L1 list-vs-multiset structural admits at `Semantics_L1.v:553/621` (Phase C) — DEFERRED 2026-05-28 | The `T_Region_Active_L1`-shadowed sub-case of `region_shrink_preserves_typing_l1_gen_m` requires bridging body derivations across input shrinkage when the outer region matches a body-internal active occurrence | **deferred until Phase D**. Four design paths surfaced + analytically evaluated 2026-05-28 (recorded in this session's memory + companion design note `Semantics_L1.v:366-402`): (a) Permutation-based perm-l1 leaves a list-structure output mismatch (concrete counterexample at `R_body = [a; rr; b; c]` vs `R_body' = [b; rr; a; c]`); (b) multiset reformulation of `remove_first_L1` cascades through every L1 rule's output threading; (c) `T_Region_*_L1` rule redesign (Permutation premise on body output) was implemented in-flight on `proof/phase-c-l1-multiset-bridge` — closes sub-sub-case (ii) (R has exactly 1 rr via count-vacuity) but leaves sub-sub-case (i) (R has ≥2 rr) requiring body-input-shrinkage, which itself is NOT a theorem (T_Loc_L1 counterexample at count=1; T_Let composition fails for the count-≥-2 precondition); (d) defer was selected as the most mathematically safe + elegant path. Phase D (L2 effect-typed TFun) introduces the natural setting: lambda bodies' R-flow becomes effect-typed, which gives the structural invariant that lets body-input-shrinkage discharge. The 2 admits at lines 553/621 remain as documented L1 debt, and the outer `Admitted.` at line 653 + the `preservation_l3` dependency annotation in PRESERVATION-DESIGN.md §5.1 continue to attribute them correctly. |

### Mid-term (L4 — scaffold landed 2026-05-28)

L4 covers dyadic interaction semantics (mother–child distinction).
Per `formal/PRESERVATION-DESIGN.md §7`, L4 is "not a separate proof
layer. It is a labelling discipline at the program / module level...
No proofs change."

Phase A scaffold landed 2026-05-28:

| Item | File | Status |
|---|---|---|
| ✅ L4 design page | `formal/L4-DYADIC.md` | done — extracts + extends design doc §7 |
| ✅ Labelling enum `ProgramMode` + `program_mode_to_modality` mapping to L2 | `formal/L4.v` | done — Definitions only, no theorems, no admit, no axiom |

Future L4 work (post-Phase D, optional): surface-syntax wiring in
the borrow checker so `#![ephapax_linear]` / `#![ephapax_affine]` /
`#![module_boundary_mix]` parse and select the L2 modality. This is
implementation, not proof debt.

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

<!-- status-gate marker: do not move. scripts/status-gate.sh reads this line. -->
Coq admitted proofs remaining: 4

(1 outer `Admitted.` in `formal/Semantics.v` — sacrosanct legacy
preservation, provably false per `Counterexample.v` + 3 outer
`Admitted.` markers in `formal/Semantics_L1.v` covering 5 internal
`admit.` cases — all pre-existing L1 structural debt + parallel
mirrors. See the per-file table and seam audit below.)

### Per-file Qed / Admitted summary (as of 2026-06-01)

| File | Qed | Admitted | Disposition |
|---|---:|---:|---|
| `formal/Semantics.v` (legacy) | n/a | **1** | 🛑 archaeology — single `Admitted.` at line 9257 (`Theorem preservation`, provably false); do not extend |
| `formal/Typing.v` (legacy) | n/a | 0 | 🛑 archaeology — `Counterexample.v` depends on falsity |
| `formal/Counterexample.v` | **5** | 0 | ✅ pinned regression witness (`bad_typable`, `bad_step`, `bad_post_untypable`, `t_loc_l1_R_preserving`, `bad_input_untypable_l1`) |
| `formal/Counterexample_L2.v` | **5** | 0 | ✅ Phase 4c soundness-gap witness — fresh-region scope crossing (`v_typed_at_empty`, `outer_typed`, `e_before_typed`, `e_step`, `e_after_untypable`) |
| `formal/Counterexample_L2_nested.v` | **5** | 0 | ✅ Phase 3b soundness-gap witness — nested TFunEff (analogue structure to `Counterexample_L2.v`) |
| `formal/TypingL1.v` | **2** | 0 | ✅ active — L1 judgment, modality-indexed |
| `formal/Semantics_L1.v` | **37+** | **3** | ✅ active — Phase 3b Stage 1a + 1b landed via PRs #252 + #253. 3 outer `Admitted.` markers cover 4 internal `admit.` cases. See seam audit below for current line numbers. |
| `formal/Modality.v` | **1** | 0 | ✅ active — L2 core, zero axioms (`linear_to_affine`) |
| `formal/Echo.v` | **12** | 0 | ✅ active — L3 calculus mechanised |
| `formal/TypingL2.v` | **10** | 0 | ✅ active — `weaken_modality` (+ Affine_id + 3 `_le_*` variants), `preservation_l2_via_l1` (conditional on `preservation_l1`), `linear_value_retype_l1_m`, and 3 β-case lemmas (`preservation_l2_app_eff_beta_linear`, `_ground_nonlinear`, `_tfuneff` conditional on Stage 1b side conditions). NOT a wrapper. |
| `formal/L4.v` | (Definitions only) | 0 | ✅ active — L4 labelling discipline (`PModeLinear` / `PModeAffine` / `PModeBoundaryMix` + `program_mode_to_modality` round-trip). No theorems. Phase A scaffold landed 2026-05-28. |
| `src/abi/Ephapax/…` (Idris2) | n/a | (E1–E6 + compileOk = 7 `0`-quantity postulates) | ✅ active — ABI; postulates are explicit OWED-to-Coq forwards. See §1 Idris row below. |
| `src/formal/Ephapax/…` (Idris2) | working | none | ✅ active — Region linearity, narrow no-escape proof; no `believe_me` / `sorry` / `assert_total` |

### Seam audit (current 2026-06-01): every admit/axiom classified

The current `admit.` / `Admitted.` set in `formal/*.v`. The remaining
admits are exactly the **pre-existing L1 structural debt** (with one
true parallel mirror that closes when its original closes) plus the
**sacrosanct legacy preservation** (provably false per `Counterexample.v`).

| Location | Class | Closes when |
|---|---|---|
| `Semantics_L1.v:576` (`admit.`) | **Pre-existing** L1 structural — `region_shrink_preserves_typing_l1_gen_m` / T_Region_Active_L1 shadowed sub-case; list-vs-multiset gap | L1 perm/multiset bridge OR `T_Region_*_L1` redesign (deferred to Phase D) |
| `Semantics_L1.v:646` (`admit.`) | **Parallel mirror** of `:576` — T_Region_Active_L1_Echo shadowed sub-case; structurally identical | Same as `:576` (mechanical replay) |
| `Semantics_L1.v:678` (`Admitted.`) | **Outer marker** — depends on internal `:576` + `:646` | When both internal admits close |
| `Semantics_L1.v:1994` (`admit.`) | **Pre-existing** L1 structural — `region_liveness_at_split_l1_gen` / T_Region_Active_L1 `binder = rv` sub-case; **GENUINELY FALSE as stated** (single-case counterexample documented at site lines 1923-1926); current `Admitted.` is a transparency mark, not "almost done" | L2 effect-typed `TFun` per `PRESERVATION-DESIGN.md §5.1`; closure requires reformulation, not direct proof |
| `Semantics_L1.v:2014` (`admit.`) | **Parallel mirror** of `:1994` — T_Region_Active_L1_Echo `binder = rv` sub-case; inherits same falsity | Same as `:1994` |
| `Semantics_L1.v:2028` (`Admitted.`) | **Outer marker** — depends on internal `:1994` + `:2014` | When both internal admits close (i.e., never directly — only via reformulation) |
| `Semantics_L1.v:3132` (`admit.`) | **Pre-existing** — `preservation_l1` body, covering S_StringConcat_Step2 + S_App_Step2 + S_Pair_Step2 cases; lambda-rigidity gap per `PRESERVATION-DESIGN.md §4.8` | Phase 3b Stages 2/3/4 (#240/#241/#242) — L2 effect-typed lambdas with `R_in/R_out` syntactic annotations |
| `Semantics_L1.v:3133` (`Admitted.`) | **Outer marker** — depends on internal `:3132` | When `:3132` closes |
| `Semantics.v:9257` (`Admitted.`) | **🛑 Sacrosanct** — legacy `Theorem preservation`, **provably false** per `Counterexample.v` (owner directive 2026-05-27) | Never. The `Admitted.` is correct. |

**Falsity audit** — two admits are not "unproven but true"; they are
**provably false as stated**:

1. `Semantics.v:9257` — refuted by `Counterexample.v`; sacrosanct.
2. `Semantics_L1.v:1994` (and its mirror `:2014`) — refuted by single-case
   counterexample `ERegion rv (EI32 5)` at `R=[rv]` documented in the
   source at lines 1923-1926. Their `Admitted.` is a transparency mark
   acknowledging the residual sub-case is false. Closure requires
   reformulation at the L2 layer (lambda-rigidity gap), not a direct proof.

No `Axiom` declarations in `formal/*.v`. `Counterexample.v` /
`Counterexample_L2.v` / `Counterexample_L2_nested.v` carry 5 + 5 + 5
Qed respectively; `TypingL1.v` / `Modality.v` / `Echo.v` / `TypingL2.v`
are all `admit.`-free.

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
