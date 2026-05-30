<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Design: generalising `subst_typing_gen_l1_m` to non-linear `T1`

**Date**: 2026-05-28
**Author**: session 8 (Phase D slice 4 — preservation_l2 follow-on)
**Status**: design only; no code lands in this doc's PR

## TL;DR

The β-case for `T_App_L2_Eff` in `preservation_l2` (`formal/TypingL2.v`) requires substituting a value into a lambda body when the lambda parameter type `T1` is **non-linear**. The existing substitution lemma `subst_typing_gen_l1_m` (`formal/Semantics_L1.v:1358`) carries an `is_linear_ty T1 = true` precondition that blocks this. Generalising it is more complex than a "sibling lemma with `false` instead of `true`" — it interacts with **body-R-rigidity** for non-linear `ELam` values. This document captures the analysis, identifies the sub-problems, and recommends a phased approach.

## Why this matters

`T_App_L2_Eff` (`formal/TypingL2.v:111`, PR #209) is the L2 elimination form for effect-typed lambdas. Closing `preservation_l2` over `has_type_l2` requires handling its β-reduction case (`S_App_Fun`). After inversion through `L2_lift_l1` + `T_Lam_L1_*_Eff` and applying `value_R_G_preserving_l1` to the argument value, the residual obligation is exactly:

```coq
has_type_l1 m R G v T1 R G ->
has_type_l1 m R ((T1, false) :: G) ebody T2 R_out ((T1, true) :: G) ->
is_value v ->
has_type_l1 m R G (subst 0 v ebody) T2 R_out G
```

This is the signature of `subst_typing_gen_l1_m` at `k = 0`, EXCEPT for the linearity precondition. For non-linear `T1` (any of `TUnit`, `TBool`, `TI32`, `TFun T1' T2'`, `TFunEff T1' T2' R_in' R_out'`, `TProd …` with non-linear components, `TSum …` with overall non-linear, `TRef Unr _`, `TEcho T'`), the existing lemma cannot fire.

## What `subst_typing_gen_l1_m` actually does with `is_linear_ty T1 = true`

Read of `Semantics_L1.v:1358-1656`. Two distinct uses of `Hlin`:

### Use A: `linear_value_is_loc_l1` to extract canonical location form

In ~20 of the proof's 28 cases, the tactic pattern is:

```coq
destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin)
  as [lv [rv [-> [-> Hregv]]]].
```

`linear_value_is_loc_l1` requires `is_linear_ty T = true` to conclude `v = ELoc l r ∧ T = TString r ∧ In r R`. This canonical form lets subsequent reasoning:
- Treat `v` as a location (so substitution into typing positions becomes "introduce a location at the right region").
- Use `loc_retype_at_R_l1_m` to lift the location's typing across R-shifts within `ebody`'s recursion.

For non-linear values, this canonical-form extraction has no analogue:
- `EUnit` / `EBool` / `EI32` have trivial R-irrelevance (T_Unit_L1 / T_Bool_L1 / T_I32_L1 type them at any R).
- `ELam` has body-R-rigidity (the lambda's body is typed at a fixed R determined at lambda formation).
- `EPair` / `EInl` / `EInr` are R-relevant if any sub-component is R-relevant.
- `EBorrow` of a location is R-relevant.

### Use B: contradiction discharge in `T_Var_Unr_L1`

`Semantics_L1.v:1409`:
```coq
exfalso. unfold ctx_lookup in H. rewrite Hk_in in H.
injection H as <- <-. rewrite Hlin in H0. discriminate.
```

When the substituted variable position `k0` is the same as the variable being typed AND the variable is typed via T_Var_Unr_L1 (unrestricted), the rule's `is_linear_ty T = false` premise contradicts `Hlin : is_linear_ty T1 = true` (since they refer to the same type). The case is vacuous.

For non-linear `T1`, this case is **not vacuous** — it's the actual substitution case: substituting an unrestricted value into an unrestricted variable position. The proof structure must handle it constructively rather than discharge by contradiction.

## The body-R-rigidity issue (the real obstacle)

For the recursive cases in `subst_typing_gen_l1_m` (e.g. `T_App_L1`, `T_Pair_L1`, `T_Let_L1`), the IH on each sub-expression needs `Hv_type` at the **sub-expression's** input R, which may differ from the outer R due to region operations inside `ebody`.

For linear values (locations), the existing proof lifts `Hv_type` across R-shifts via:
```coq
apply loc_retype_at_R_l1_m. eapply region_liveness_at_split_l1_gen; ...
```
or
```coq
apply loc_retype_at_R_l1_m. right; exact Hregv.
```

The `loc_retype_at_R_l1_m` lemma re-types an `ELoc` at any `R` that contains the location's region. The corresponding non-linear-value retype lemma is more nuanced:

| Value | Retype across R-shift `R → R'`? |
|---|---|
| `EUnit` / `EBool` / `EI32` | ✅ Trivial (R-irrelevant) |
| `ELoc l r` | ❌ Always linear; outside non-linear scope |
| `ELam T e` (TFun T1 T2) | ❌ Body typed at fixed R; retype requires body-R-shift |
| `ELam T e` (TFunEff T1 T2 R_in R_out) | ⚠️ Body typed at R_in (independent of outer R); retype works if R' still satisfies `forall r, In r R' -> In r R_in` |
| `EPair v1 v2` | ⚠️ Inherits from components |
| `EInl T v` / `EInr T v` | ⚠️ Inherits from `v` |
| `EBorrow (ELoc l r)` | ❌ Inherits R-dependence from `ELoc` |
| `EEcho T v` | ⚠️ Inherits from `v` |

The ❌ rows mean a fully general `nonlinear_value_retype_at_R_l1_m` lemma is **false** in the unrestricted case — specifically, `TFun` lambdas have body-R-rigidity (the same gap that blocks legacy `preservation_l1` per `Semantics_L1.v:1708-1713`).

## What this means for the lemma's scope

The clean non-linear substitution lemma cannot cover all non-linear `T1`. The categories that **do** admit a clean lemma:

1. **Ground non-linear values** (`EUnit`, `EBool`, `EI32`): trivially R-irrelevant. A retype lemma `ground_nonlinear_retype_l1_m` is Qed-able in ~10 lines.

2. **TFunEff lambdas** (`ELam T e` typed at `TFunEff T1 T2 R_in R_out`): R'-retype works under the side condition `forall r, In r R' -> In r R_in`. The lambda value's typing rule `T_Lam_L1_*_Eff` already requires this side condition at formation; preserving it across retype is a one-line obligation.

The categories that **do not** admit a clean lemma:

3. **TFun lambdas** (legacy `T_Lam_L1_Linear` / `T_Lam_L1_Affine`): body-R-rigid. Same gap as legacy `preservation_l1` slice 4b.

4. **EBorrow of a location**: inherits linear R-dependence; the borrow doesn't reduce R-dependence.

5. **Compound values with R-dependent sub-components**: inherit from sub-components.

## Recommended phasing

### Phase 1 (next session): ship `ground_nonlinear_retype_l1_m`

A 10-line lemma covering `EUnit` / `EBool` / `EI32`. Qed-able trivially. Useful in its own right (any β-reduction with `T1 ∈ {TUnit, TBool, TI32}` becomes closeable).

```coq
Lemma ground_nonlinear_retype_l1_m :
  forall m R R' G v T,
    is_value v ->
    is_ground_nonlinear_ty T = true ->   (* new predicate; TUnit/TBool/TI32 only *)
    has_type_l1 m R G v T R G ->
    has_type_l1 m R' G v T R' G.
```

Where `is_ground_nonlinear_ty` is a new predicate:
```coq
Definition is_ground_nonlinear_ty (T : ty) : bool :=
  match T with
  | TUnit | TBool | TI32 => true
  | _ => false
  end.
```

### Phase 2: ship `subst_typing_gen_l1_m_ground_nonlinear`

A parallel substitution lemma for ground non-linear types. Uses `ground_nonlinear_retype_l1_m` in place of `loc_retype_at_R_l1_m` in the cases that need R-shift retyping.

Structure mirrors `subst_typing_gen_l1_m`'s 28 cases. Crucially:
- `T_Var_Lin_L1` with `i = k0`: **exfalso** via `is_linear_ty T1 = false` vs T_Var_Lin_L1's `is_linear_ty T = true` premise.
- `T_Var_Unr_L1` with `i = k0`: **constructive**; apply `Hv_type` directly.
- Compound cases: use `ground_nonlinear_retype_l1_m` for R-shift retypes.

Estimated ~250-300 lines, paralleling the existing proof.

### Phase 3: ship `tfuneff_lambda_retype_l1_m` + extend substitution

Add a retype lemma for TFunEff lambdas (under R' ⊆ R_in side condition). Extend the substitution lemma to cover `T1 = TFunEff …` lambdas as substituends. This is the case actually needed for higher-order β-reductions where the lambda parameter is itself a function type.

### Phase 4: close `preservation_l2` β-case using Phases 1-3

With the substitution machinery in place, the T_App_L2_Eff β-case in `preservation_l2` closes by:
1. Inversion on the L2 derivation → L1 derivation of `T_Lam_L1_*_Eff`.
2. Inversion on the L1 derivation → body typing at R_in + side condition.
3. Apply `value_R_G_preserving_l1` to argument value → R_in = R, G'' = G.
4. Case-split on `is_linear_ty T1`:
   - Linear: use existing `subst_typing_gen_l1_m`.
   - Ground non-linear: use Phase 2 lemma.
   - TFunEff non-linear: use Phase 3 lemma.
   - Other non-linear: deferred (compound values; see Phase 5).
5. `L2_lift_l1` wrap.

### Phase 5 (deferred): compound non-linear values

`EPair` / `EInl` / `EInr` / `EEcho` of non-linear components. Sub-component analysis. May require additional retype machinery. Realistically multiple sessions of work.

## Phase 4c addendum (2026-05-30) — conditional preservation_l2 for TFunEff β

Prototyping Phase 4c on paper (after Phase 4a / 4b landed at PRs #228 / #233) revealed a structural soundness gap that requires a **conditional** preservation_l2 statement for the TFunEff β-case. `formal/Counterexample_L2.v` mechanises the witness.

### The obstacle (mechanised in `Counterexample_L2.v`)

For any TFunEff lambda body that introduces a fresh region via `ERegion` AND references the substituted variable inside that region scope, β-reduction does **not** preserve typing:

```
T1_inner = TFunEff TUnit TUnit [] []                       (* substituee type, R_in_v = [] *)
outer    = ELam T1_inner (ERegion r2 (EVar 0))             (* body introduces fresh r2 *)
v2       = ELam TUnit EUnit                                (* a value of type T1_inner *)
e_before = EApp outer v2     (* well-typed via T_App_L2_Eff at R = [] *)
e_after  = ERegion r2 v2     (* β-result: subst 0 v2 (ERegion r2 (EVar 0)) *)
```

`e_before` types (Qed: `e_before_typed`); `e_step` reduces it to `e_after` (Qed: `e_step`); `e_after` does not type at the same outer type (Qed: `e_after_untypable`). The mechanism: T_Region_L1's `~ In r (free_regions T)` premise prevents the fresh `r` from being in `R_in_v` (since `R_in_v ⊆ free_regions(TFunEff)`). After β-substitution, the inner expression becomes a TFunEff value that must re-type at `r :: R`, requiring `r ∈ R_in_v` (false).

### Resolution: Phase 4c ships **conditionally**

Preservation_l2 for the T_App_L2_Eff β-case holds **only** for programs satisfying:

```
regions_introduced_by(ebody) ⊆ R_in_v
```

where `regions_introduced_by` is the `Fixpoint` already landed in `Syntax.v` (PR #230), `ebody` is the outer lambda's body, and `R_in_v` is the substituee's TFunEff input region env.

The Phase 3b substitution lemma (`subst_typing_gen_l1_m_tfuneff`) ships with this precondition; the Phase 4c β-case wrapper propagates it. Programs not satisfying the precondition are a **documented soundness-gap subclass** — they witness the same fundamental "scoped resource cannot escape its scope" limitation that motivated the four-layer redesign in the first place.

### Three resolution paths (broader than original (a)/(b)/(c) options)

1. **Conditional preservation_l2 (recommended)**: Phase 3b lemma takes the precondition; Phase 4c β-case requires it; programs outside form a documented soundness-gap class. This is what `Counterexample_L2.v` justifies. Aligns with the legacy `Counterexample.v` precedent (preservation holds modulo a structural constraint that legitimate programs satisfy).
2. **Region-polymorphic TFunEff**: change the type system so `TFunEff T1 T2 R_in R_out` permits implicit region extension at use sites. Major type-system change; defers to a future redesign.
3. **L2 region-transfer combinator**: add an L2 typing rule that explicitly transfers a fresh region into a TFunEff lambda's R_in for the duration of a scope. Adds L2 expressiveness; defers to a future PR.

### What ships in the Phase 4c PR

- `formal/Counterexample_L2.v` — three Qed lemmas mechanising the soundness gap.
- This addendum to `SUBST-LEMMA-GENERALIZATION-DESIGN.md`.
- STATE.a2ml refresh to reflect the conditional path.

Phase 3b implementation (the ~400-line `subst_typing_gen_l1_m_tfuneff` lemma body) and Phase 4c β-case wrapper remain follow-up work — but the design constraint they must satisfy is now mechanically witnessed.

## What this session ships

This design document only. No code changes. STATE.a2ml shifts `next_action` to "Phase 1: implement `ground_nonlinear_retype_l1_m` per `formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md`".

## Owner-directive compliance check

Per `CLAUDE.md` 2026-05-27:

- ✅ Does not propose closing legacy `preservation` in `Semantics.v` (provably false).
- ✅ Does not extend `Semantics.v` with closure-support lemmas.
- ✅ Does not close residual `Semantics_L1.v` axioms via proof tricks — Phase 1-2 add NEW infrastructure to `Semantics_L1.v` orthogonal to legacy admits.
- ✅ Does not follow pre-2026-05-26 closure plans.
- ✅ Does not patch legacy `Typing.v`.
- ✅ Reads `PRESERVATION-DESIGN.md` first (specifically §5.1 lines 468-474 — the L1-intro / L2-elim design vision endorsing T_App_L2_Eff at L2).
- ✅ Works per-layer (L1 infrastructure → L2 preservation closure).
- ✅ Escalates before patching (this design doc IS the escalation).

Anti-pattern detector (per `CLAUDE.md` §"Anti-pattern detector"):

- ✅ No sibling-region-disjointness side conditions proposed.
- ✅ No region-weakening predicates indexed on syntactic shape (the proposed retype lemmas are indexed on TYPE shape, not syntactic shape — `is_ground_nonlinear_ty` is a type predicate).
- ✅ No admit-shuffling between `Semantics.v` and a new lemma.
- ✅ No proposal to close `Theorem preservation` in `Semantics.v` to `Qed.`.
- ✅ No new `Axiom` declarations.

## Open design questions for owner

1. **`is_ground_nonlinear_ty` predicate placement**: `Syntax.v` (near `is_linear_ty`) or `Semantics_L1.v` (near the lemma that uses it)? Recommendation: `Syntax.v` for symmetry with `is_linear_ty`.

2. **Phase 3 scope**: TFunEff lambdas only, or also TFun lambdas with the body-R-rigidity gap honestly admitted? Recommendation: TFunEff only (TFun is the legacy slice 4b debt; not in scope for this initiative).

3. **Phase 5 priority**: should compound non-linear values block `preservation_l2` closure, or can `preservation_l2` Qed with the compound-value case admitted? Recommendation: defer Phase 5; `preservation_l2` can close conditionally on a `nonlinear_compound_substitutable T` predicate that returns true for ground + TFunEff and false otherwise. The predicate's `true` cases let preservation_l2 fire; the `false` cases vacuously discharge or admit at the predicate-false branch.

4. **Sibling vs case-split**: Phase 2 ships as a parallel lemma (`subst_typing_gen_l1_m_ground_nonlinear`) rather than folding case-split into the existing lemma. Avoids breaking ~30 Qed downstreams of `subst_typing_gen_l1_m`. Confirmed.

## References

- `formal/Semantics_L1.v:1358-1656` — `subst_typing_gen_l1_m` proof body.
- `formal/Semantics_L1.v:916-933` — `linear_value_is_loc_l1` canonical-form extractor.
- `formal/Semantics_L1.v:1168-1235` — `loc_retype_at_R_l1_m` (the lemma to parallel for non-linear values).
- `formal/Semantics_L1.v:1708-1713` — body-R-rigidity comment in preservation_l1.
- `formal/TypingL1.v:221-229` — `T_Lam_L1_Linear_Eff` / `T_Lam_L1_Affine_Eff` (TFunEff lambdas with R_in side condition).
- `formal/TypingL2.v` post-PR #211 — `preservation_l2_via_l1` + doc block stating the full preservation_l2 goal.
- `formal/PRESERVATION-DESIGN.md` §5.1 lines 468-474 — load-bearing design quote.
- `CLAUDE.md` owner directive 2026-05-27 — preservation-work boundaries.
- PR #209 — T_App_L2_Eff constructor.
- PR #211 — preservation_l2_via_l1.
- PR #212 — STATE shift after PR #211.
