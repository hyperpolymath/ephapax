<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Phase D — L2 effect-typed TFun, redesign memo (2026-05-28)

This memo refines the Phase D plan in
[`PRESERVATION-DESIGN.md §5.1`](PRESERVATION-DESIGN.md) based on
analytical findings from the 2026-05-28 implementation attempt.
**Read this before continuing Phase D work; it supersedes earlier
slice-by-slice framings that omit the substitution-lemma side
condition introduced below.**

## What landed

Two PRs landed on `main` during the 2026-05-28 session as part of
Phase D's scaffolding plus an independent reformulation:

| PR | Title | What |
|---|---|---|
| #200 | `syntax(L2 Phase 2 / Phase D slice 1): add TFunEff effect-typed function constructor` | Adds `TFunEff T1 T2 R_in R_out` to `ty` in `Syntax.v`; extends `free_regions` in `Typing.v` for the new case. Zero proof changes. Legacy `TFun T1 T2` preserved per CLAUDE.md owner directive. |
| #201 | `syntax: expr_strictly_free_of_region (closes blocker 5)` | Adds a strict variant of `expr_free_of_region` that recurses unconditionally into `ERegion r' body` (no shadow short-circuit). Migrates L1 region-shrinkage lemma preconditions to the strict variant. **Blocker 5 (predicate weakness from shadow short-circuit) — CLOSED.** |

## What we tried for slice 2 — and what broke

The 2026-05-28 slice 2 attempt added two new typing rules to
`TypingL1.v`:

```coq
| T_Lam_L1_Linear_Eff : forall R G T1 T2 e R_in R_out,
    R_in ; ctx_extend G T1 |=L1[Linear] e : T2 -| R_out ; (T1, true) :: G ->
    R ; G                  |=L1[Linear] ELam T1 e : TFunEff T1 T2 R_in R_out -| R ; G

| T_Lam_L1_Affine_Eff : forall R G T1 T2 e u R_in R_out,
    R_in ; ctx_extend G T1 |=L1[Affine] e : T2 -| R_out ; (T1, u) :: G ->
    R ; G                  |=L1[Affine] ELam T1 e : TFunEff T1 T2 R_in R_out -| R ; G
```

Adding new constructors to `has_type_l1` forces every existing
inductive lemma over `has_type_l1` to cover the new cases. The
following lemmas were exercised:

| Lemma | T_Lam_L1_*_Eff case | Outcome |
|---|---|---|
| `count_occ_le_l1_m` | R-preserving outer | (not hit in this attempt; would close trivially) |
| `region_shrink_preserves_typing_l1_gen_m` | Body's R_in unaffected by outer shrink → use body unchanged | ✅ closed via `eapply T_Lam_L1_*_Eff. eassumption.` |
| `shift_typing_gen_l1_m` | Body's context extends by T1; shift by (S k) | ✅ closed via same pattern as legacy T_Lam |
| `subst_typing_gen_l1_m` | **Substituted value lives at outer R, body at R_in** | 🛑 **STRUCTURAL FAIL** |

The substitution lemma's `T_Lam_L1_Linear_Eff` case decomposes as:

* Hypothesis: `Hregv : In rv R` (substituted value's region is in the
  outer environment).
* Goal: produce a body derivation at `R_in` with `rv` substituted in.
  The body's typing rules (T_Loc_L1, etc.) for occurrences of the
  substituted variable require `In rv R_in`.
* Available: nothing that ties `R` to `R_in`.

**`In rv R` does not imply `In rv R_in`** under the current rule
shape. The body's `R_in` is a free parameter of the lambda type — the
lambda value can declare any `R_in` it likes. There is no enforced
connection between `R_in` and the regions of the bound variable's
type at lambda formation. Substitution lemma is therefore not
generalisable to the new constructors without an additional
invariant.

## The structural insight

This is the *same* missing invariant we hit at:

* `Semantics_L1.v:553/621` (Phase C — shadowed `T_Region_Active_L1`)
* `Semantics_L1.v:1694` (`preservation_l1` lambda-rigidity)
* Sub-sub-case (i) of Phase C's option (c) attempt
  (`feedback`: body-input-shrinkage is not a theorem in general)

Each instance is the L1 vocabulary lacking a way to relate the
**outer** region environment (where caller values live) to a
**nested** region environment (where a lambda body, or a region's
scoped body, operates). The L1 rule shapes treat outer and inner
environments as independent, but **substitution and call sites
require a connection**.

## The redesign — side condition on `T_Lam_L1_*_Eff`

Add an explicit side condition to `T_Lam_L1_*_Eff` requiring the
bound variable's regions to be live in the body's input environment:

```coq
| T_Lam_L1_Linear_Eff : forall R G T1 T2 e R_in R_out,
    (forall r, In r (Typing.free_regions T1) -> In r R_in) ->  (* NEW *)
    R_in ; ctx_extend G T1 |=L1[Linear] e : T2 -| R_out ; (T1, true) :: G ->
    R ; G                  |=L1[Linear] ELam T1 e : TFunEff T1 T2 R_in R_out -| R ; G

| T_Lam_L1_Affine_Eff : forall R G T1 T2 e u R_in R_out,
    (forall r, In r (Typing.free_regions T1) -> In r R_in) ->  (* NEW *)
    R_in ; ctx_extend G T1 |=L1[Affine] e : T2 -| R_out ; (T1, u) :: G ->
    R ; G                  |=L1[Affine] ELam T1 e : TFunEff T1 T2 R_in R_out -| R ; G
```

**Interpretation**: any region appearing in the bound variable's
type `T1` is guaranteed to be live in the body's input environment
`R_in`. When substituting a value `v : T1` with `free_regions T1 ⊇ {rv}`
into the body, `In rv R_in` follows from the side condition.

For typical lambda types:

* `T1 = TBase TUnit`: `free_regions T1 = []`. Side condition vacuous.
  No constraint on R_in. ✓
* `T1 = TString rv`: `free_regions T1 = [rv]`. Side condition forces
  `In rv R_in`. ✓
* `T1 = TPair (TString r1) (TString r2)`: forces both `r1` and `r2`
  in R_in. ✓
* `T1 = TFun T1' T2'`: forces all free regions of T1' and T2' into
  R_in. ✓ (Closures over substring-typed values carry their region
  requirements.)

This side condition is **discharge-able at lambda formation time**:
the caller forming the lambda must establish the constraint. In
practice this is automatic — any program that types a lambda body
referencing a region in T1 already has that region in scope.

## Why this closes `subst_typing_gen_l1_m`

In the T_Lam_L1_Linear_Eff case of the substitution lemma:

* Hypothesis from rule: `H : forall r, In r (free_regions T1) -> In r R_in`.
* The substituted value `vv` has `In rv R` (lemma's preexisting
  Hregv) AND `vv : T1` with `In rv (free_regions T1)` (since
  `linear_value_is_loc_l1` constrains rv to be T1's region).
* Apply H: `In rv R_in`. ✓
* Body typing after substitution uses `In rv R_in` to discharge
  T_Loc_L1's `In r R` premise at the substituted variable's
  occurrences.

The lemma case closes via the same pattern as legacy T_Lam_L1_Linear
but threaded through R_in instead of outer R.

## Slice plan (revised)

| Slice | Scope | Status |
|---|---|---|
| 1 | TFunEff syntax (`Syntax.v` + `free_regions`) | ✅ MERGED PR #200 |
| 2 (redesigned) | `T_Lam_L1_*_Eff` with side condition `R ⊆ R_in`; cascade through 3 inductive lemmas in `Semantics_L1.v` | ✅ MERGED PR #204 |
| 3 — first attempt | `T_App_L1_Eff` with explicit count-le premise | ⚠️ **REVERTED 2026-05-28** — see addendum below |
| 3 — redesign | TBD — see addendum below | Pending |
| 4 | `preservation_l1` lambda-rigidity closure (`Semantics_L1.v:1694`) | Pending |
| 5 | Phase B Slice 1 (TEcho linearity wire) + Phase C (list-vs-multiset bridge) unlocks | Pending |

## Slice 3 addendum — type-embedded R blocks env-shrinkage (2026-05-28)

The first slice 3 attempt added the rule

```coq
| T_App_L1_Eff : forall m R R_pre G G' G'' e1 e2 T1 T2 R_in R_out,
    R     ; G  |=L1[m] e1 : TFunEff T1 T2 R_in R_out -| R_pre ; G' ->
    R_pre ; G' |=L1[m] e2 : T1                       -| R_in  ; G'' ->
    (forall r, count_occ string_dec R_out r <= count_occ string_dec R_in r) ->
    R     ; G  |=L1[m] EApp e1 e2 : T2 -| R_out ; G''
```

`count_occ_le_l1_m`'s case closed via the count-le premise + the IHs. `region_shrink_preserves_typing_l1_gen_m`'s case did NOT close, exposing the deeper structural issue.

**The issue:** TFunEff embeds R_in / R_out in the type T. When the env-shrinkage lemma removes one occurrence of `rr` from the outer R, the rule's structure forces:

* e1's TFunEff type is preserved (lemma signature: `T` unchanged).
* e2's IH gives output `remove_first rr R_in` (shrunk version of e2's original output).
* The rule's `R_in` premise is `R_in` (from e1's TFunEff, unchanged).

These mismatch unless `rr ∉ R_in`. Similarly the lemma's expected output `remove_first rr R_out` vs the rule's output `R_out` requires `rr ∉ R_out`. The natural precondition `~ In rr (free_regions T)` would give both (`free_regions (TFunEff T1 T2 R_in R_out) ⊇ R_in ∪ R_out`).

**Adding the precondition cascades:** the lemma's induction would need every sub-IH to also satisfy a type-precondition for the sub-expression's type. For `T_App_L1`, e2's type is `T1` (the argument type), which is NOT constrained by the parent's HnotT (parent only constrains `T2`, the return type). So `T_App_L1`'s case BREAKS under the strengthened precondition.

Strengthening further (e.g., "no intermediate type contains `rr`") is not a clean Prop and would need a meta-condition over derivations.

**Decision:** REVERT slice 3's `T_App_L1_Eff`. The rule is too tightly coupled to env-shrinkage with the current `region_shrink_preserves_typing_l1_gen_m` signature.

**Future redesign options for slice 3:**

1. **Lift env-shrinkage out of the lemma's general statement.** Split `region_shrink_preserves_typing_l1_gen_m` into (i) a value-restricted shape that handles TFunEff vacuously (no T_App in value derivations), and (ii) a non-value shape with TFunEff *explicitly forbidden* via a type-shape predicate. Application sites of `_gen_m` choose which version they need.
2. **Make `T_App_L1_Eff`'s premise pass through an explicit "env-frame" rather than the function's R_in/R_out.** I.e., the rule says "given e1 typing at TFunEff with effect (R_in, R_out), and a frame Δ such that the call-site env is `Δ ∪ R_in`, the post-call env is `Δ ∪ R_out`." This decouples the embedded R from the call-site env. Bigger redesign.
3. **Defer `T_App_L1_Eff` indefinitely.** Phase D's main payoff (closing lambda-rigidity at `Semantics_L1.v:1694`) doesn't strictly require `T_App_L1_Eff` if we can argue preservation for β-reduction on `T_Lam_L1_*_Eff`-typed lambdas via a different path. Investigation owed.

The 2026-05-28 attempt's diff is preserved in git history (commit on the now-deleted branch); see `git log --all` for archaeology.

**What slice 3 was supposed to unlock:** β-reduction for `T_Lam_L1_*_Eff`-typed lambdas (preservation_l1 case S_App_Fun) would use `T_App_L1_Eff`'s typing. Without `T_App_L1_Eff`, TFunEff lambdas can be *formed* but never *called* via has_type_l1 — slice 2's contribution is preserved but standalone (no programs exercise it yet).

The strict-predicate reformulation (PR #201) is independent of these
slices and already merged.

## Implementation notes for slice 2

1. The 2 rules: add right after `T_Lam_L1_Affine` at
   `TypingL1.v:183` (verified compile order works).
2. The side condition is a `forall r, In r (free_regions T1) -> In r R_in`
   Prop — straightforward to discharge in induction cases.
3. **Cascade to 8 inductive Qed lemmas** in `Semantics_L1.v`:
   - `count_occ_le_l1_m` — trivial (R-preserving outer)
   - `region_shrink_preserves_typing_l1_gen_m` — re-apply rule with
     body unchanged + side condition unchanged (region shrink at
     outer doesn't touch the body's premise)
   - `typing_preserves_length_l1` — trivial
   - `typing_preserves_bindings_l1` — mirrors legacy T_Lam case
   - `unrestricted_flag_unchanged_l1` — similar
   - `shift_typing_gen_l1_m` — mirrors legacy T_Lam case
   - `value_R_G_preserving_l1` — lambda is a value; R-preserving
     case trivial
   - `subst_typing_gen_l1_m` — **uses the side condition** to discharge
     `In rv R_in` from `In rv (free_regions T1)`
4. `Counterexample.v` is unaffected (no TFunEff or T_Lam_L1_*_Eff
   usage).

## Owner directive compliance

Per CLAUDE.md owner directive 2026-05-27:

* ✅ Zero new `Admitted.` or `Axiom.` declarations
* ✅ No patching of `Semantics.v` `preservation` (provably false)
* ✅ No patching of legacy `Typing.v` judgment
* ✅ Counterexample.v regression theorem untouched
* ✅ All commits GPG-signed
* ✅ Auto-merge ON for every PR

## Anti-patterns this redesign avoids

* **Strengthening `subst_typing_gen_l1_m`'s preconditions** with a
  per-call-site `In rv R_in` hypothesis would cascade to every
  caller and force them to prove the connection ad-hoc. The side
  condition at rule formation localises the constraint.
* **Separate `has_type_l1_eff` judgment** would double the lemma
  surface and require bridge lemmas. Avoided by extending
  `has_type_l1` in place with a clean side condition.
* **Constraining R_in = outer R** would defeat the purpose of
  effect-typing. Avoided.

## Cross-references

* [`PRESERVATION-DESIGN.md §5.1`](PRESERVATION-DESIGN.md) — original
  Phase D outline.
* [`PROOF-NEEDS.md`](../PROOF-NEEDS.md) — proof debt audit (Phase B
  + Phase C deferral rows reference this Phase D closure).
* `Semantics_L1.v:553/621` — Phase C structural admits that close
  once slice 4+5 land.
* `Semantics_L1.v:1694` — `preservation_l1` lambda-rigidity admit
  that closes at slice 4.

## Future re-attempts of perm_l1 (agent finding 2026-05-28)

The standalone `region_env_perm_typing_l1` (existential output)
agent attempt 2026-05-28 found 7 admits across two failure families:

1. R-stability rules (`T_Lam_L1_*`, `T_Borrow_Val_L1`, `T_Echo_L1`)
   — force output_R = input_R as lists; IH gives perm-equiv not
   list-equal.
2. Branch-agreement rules (`T_Case_L1_*`, `T_If_L1_*`) — branches
   yield outputs perm-equiv to a join but not list-equal.

Both families dissolve once the L2 effect-typed structure is in
place: R-stability rules get effect-typed wrappers that don't force
list equality, and branch-agreement gets a per-branch effect that
the join sums.

`perm_l1` is therefore unblocked at slice 5 (post-T_App_L1_Eff
landing), not at slice 2.
