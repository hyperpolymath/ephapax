<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
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

## Slice 3 sub-addendum — option 4 (meta-lemma) analysis (2026-05-28, session 4)

The 2026-05-28 session 3 close-out flagged a fourth option not in the list above and tagged it "UNTRIED — most promising":

> **Option 4 — Meta-lemma approach.** Strengthen `expr_strictly_free_of_region`'s `ELam` case to recurse into the type annotation:
> ```coq
> | ELam T body => ~ In r (Typing.free_regions T) /\ expr_strictly_free_of_region r body
> ```
> Add a context-freedom precondition `forall i T u, ctx_lookup G i = Some (T, u) -> ~ In r (free_regions T)` to `region_shrink_preserves_typing_l1_gen_m`. Then prove a meta-lemma `strict_free_implies_type_free` that derives `~ In rr (free_regions T)` from `expr_strictly_free_of_region rr e` + the typing derivation + context-freedom. The shrinkage lemma's `T_App_L1_Eff` case closes by applying the meta-lemma to e1's TFunEff type, extracting `~ In rr R_in` and `~ In rr R_out`, then mechanically matching the rule's premises with the env-shrunk IHs.

Session 4 (this addendum) analysed option 4 in detail and **found it provably non-viable**. Recording the analysis here so that future sessions don't re-attempt it.

### Why the meta-lemma fails at `T_Lam_L1_*_Eff`

The proposed meta-lemma:

```coq
strict_free_implies_type_free :
  forall rr e R G T R' G' m,
    ctx_free_of rr G ->        (* context-freedom precondition *)
    expr_strictly_free_of_region rr e ->
    R ; G |=L1[m] e : T -| R' ; G' ->
    ~ In rr (free_regions T)
```

would induct on the typing derivation. The `T_Lam_L1_Linear_Eff` case (the rule that landed in slice 2, `TypingL1.v:221-224`) has the shape:

```coq
| T_Lam_L1_Linear_Eff : forall R G T1 T2 e R_in R_out,
    (forall r, In r R -> In r R_in) ->
    R_in ; ctx_extend G T1 |=L1[Linear] e : T2 -| R_out ; (T1, true) :: G ->
    R ; G                  |=L1[Linear] ELam T1 e : TFunEff T1 T2 R_in R_out -| R ; G
```

In the meta-lemma's induction at this case:

* Expression: `ELam T1 body`.
* Strengthened strict-free of `ELam T1 body` decomposes (per the proposed strengthening) to `~ In rr (free_regions T1) /\ expr_strictly_free_of_region rr body`.
* Conclusion type: `TFunEff T1 T2 R_in R_out`. Its `free_regions` (per `Typing.v:55-71`, including the slice 1 case `TFunEff T1 T2 R_in R_out => free_regions T1 ++ free_regions T2 ++ R_in ++ R_out`) is the four-way concatenation.
* The goal `~ In rr (free_regions (TFunEff T1 T2 R_in R_out))` decomposes into four conjuncts:
  - `~ In rr (free_regions T1)` ← available from the strengthened strict-free hypothesis. ✓
  - `~ In rr (free_regions T2)` ← available from the IH on `body` (typed at `T2` in the extended context, with the strengthened strict-free of `body`, and context-freedom of the extended `ctx_extend G T1` derivable from outer context-freedom + the first conjunct). ✓
  - `~ In rr R_in` ← **NO SOURCE.**
  - `~ In rr R_out` ← **NO SOURCE.**

`R_in` and `R_out` are **free parameters of the rule**. They appear in the conclusion type but are not constrained by anything in the lambda's syntactic form. The rule's side condition `forall r, In r R -> In r R_in` is unidirectional (R ⊆ R_in), so it gives `In r R → In r R_in`, not `~ In r R_in → ~ In r R`. The body's typing premise (`R_in ; ... |- body : T2 -| R_out`) likewise constrains R_in/R_out only by what the body needs, not by what `rr` doesn't touch.

In short: **the strengthened strict-free predicate covers syntactic occurrences of `rr` in `ELam T1 body` (which is just T1 and body), but cannot reach `R_in` and `R_out` because those live only in the *typing derivation*, not in the *expression*.**

### Why this is the same impedance mismatch as the original slice 3 blocker

The original slice 3 blocker (session 3, this document above) was: `region_shrink_preserves_typing_l1_gen_m`'s `T_App_L1_Eff` case couldn't close because the IH on `e2` gives `remove_first rr R_in` while the rule's premise demands `R_in`.

The proposed fix via option 4 (meta-lemma) **relocates the same mismatch** to a different proof obligation: the meta-lemma's `T_Lam_L1_*_Eff` case can't close because `R_in`/`R_out` are syntax-invisible free parameters.

The root cause is the same in both presentations: **the L1 vocabulary of `expr_strictly_free_of_region` cannot constrain the effect-typing annotations carried in `TFunEff`**, because effect annotations are a *typing* artifact, not a *syntactic* one.

### Adjacent options also fail for the same reason

Two repair attempts on option 4 also fail:

1. **Require `R_in ⊆ free_regions T1 ∪ free_regions T2`** as an extra side condition on `T_Lam_L1_*_Eff`. This would let `~ In rr T1` + `~ In rr T2` (from strict-free + IH) imply `~ In rr R_in`. **Problem**: this over-constrains R_in. A lambda body that uses regions *not* in its parameter or return type (e.g., a lambda that allocates a transient region for its body's local work, drops it before returning) would no longer type — its R_in legitimately exceeds the type's free regions.
2. **Require `R_in` to be minimal** (exactly the regions the body actually uses, derivable as a function of body syntax). **Problem**: this requires a "region inference" function that is decidable and structurally faithful. The current ephapax grammar doesn't expose enough structure at lambda formation to compute this; we'd need annotations or a fresh inference pass.

Both repairs require slice 2's already-landed rule shape to change. Even granting the change, they trade off compositionality (call sites that wrap lambdas with extra-region preludes/postludes break under a minimal-R_in regime).

### Implication for the slice 3 redesign

Option 4 is removed from the candidate list. The remaining candidates are:

1. **Split lemma** (option 1) — value-restricted vs non-value variants of `region_shrink_preserves_typing_l1_gen_m`. **Caveat surfaced in session 4**: the value-restricted variant's `T_Lam_L1_*` cases still recurse into non-value bodies via IH, so the non-value variant must exist and must handle `T_App_L1_Eff`. The split doesn't make `T_App_L1_Eff`'s case go away; it just moves it.
2. **Env-frame Δ** (option 2) — restructure `T_App_L1_Eff`'s premise so the call-site env is `Δ ++ R_in` and the post-call env is `Δ ++ R_out`. **Caveat surfaced in session 4**: `remove_first` on `Δ ++ R_in` still removes from R_in if `rr ∈ R_in`. The frame Δ doesn't shield R_in from env shrinkage unless we further require `rr ∉ R_in`. The deeper fix is still needed.
3. **Defer `T_App_L1_Eff` indefinitely** (option 3) — explicitly accept that TFunEff lambdas can be formed but never called via `has_type_l1`. **Status from session 3**: rejected because slice 4 (preservation_l1 lambda-rigidity closure) requires β-reduction typing for TFunEff lambdas. **Status from session 4**: re-examined and the rejection still holds, but with one nuance — preservation_l1's `S_App_Step2` case can be made vacuous for TFunEff function values *if* we can prove "an `EApp v1 e2` with `v1 : TFunEff T1 T2 R_in R_out` does not type via `has_type_l1`" as a meta-fact. This is true (no T_App rule produces a TFunEff conclusion at the function position), so option 3 is *partially* viable for slice 4: it closes lambda-rigidity for *uncallable* TFunEff lambdas. Slice 5's broader effect-typing work would still need T_App_L1_Eff or a successor.

### Option 5 — level-split

A new option surfaces from the session 4 analysis. The structural insight is that **T_App_L1_Eff is doing L2 work** (calling an effect-typed function is fundamentally a modality/effect operation, not a region operation), but it currently lives in L1 (`has_type_l1`). Move it to L2:

* `has_type_l1` (L1) — knows `TFunEff` exists as a type former (slice 1, already landed) and can type lambdas at it (slice 2, already landed), but **does not provide an application rule for TFunEff**. EApp on a TFunEff function does not type at L1.
* `has_type_l2` (L2) — wraps `has_type_l1` with a `T_App_L2_Eff` rule that handles application of TFunEff lambdas. The L2 judgment becomes the canonical home for effect-typed application.

Properties:

* `region_shrink_preserves_typing_l1_gen_m` only needs to handle the L1 judgment, where T_App_L1_Eff doesn't exist. Slice 3's blocker disappears at the L1 level.
* `preservation_l1` lambda-rigidity closure (slice 4): TFunEff lambdas are still uncallable at L1, but L1 was never the right venue for their β-reduction. Lambda-rigidity at the L1 level closes for *legacy* lambdas via existing means; TFunEff lambdas are inert at L1, and inert values preserve trivially.
* `preservation_l2`: a new theorem (slice 5 work) handles β-reduction for TFunEff lambdas under the L2 judgment. The L2 vocabulary can introduce effect-aware env-shrinkage lemmas designed for TFunEff from the start, without retrofitting an L1 lemma.

Trade-off: option 5 splits T_Lam_L1_*_Eff (L1) from T_App_L2_Eff (L2). The introduction and elimination of TFunEff live at different layers. This is unusual for type formers but defensible because the introduction is "syntactically lambda-shaped" (an L1 syntactic form with extra type-level annotations) while elimination is "effect-semantic" (consuming the effect annotations meaningfully). The current `TypingL2.v` is described as a "thin wrapper through `TypingL1.has_type_l1`"; option 5 thickens it with at least the T_App_L2_Eff rule.

### Recommendation for owner decision

Session 4 cannot pick among options 1, 2, 3, and 5 without owner input — the choice is a layer-design decision, not a proof-tactics decision. Each option has a different downstream cost profile:

| Option | Slice 3 cost | Slice 4 closure | Slice 5 unblock |
|---|---|---|---|
| 1 (split lemma) | High (rewrite `_gen_m`; non-value variant still blocked) | Partial | Unclear |
| 2 (env-frame Δ) | Medium-high (`T_App_L1_Eff` redesign + cascade) | Should close | Unclear; might cascade-break Phase B Slice 1 |
| 3 (defer) | Low (no code change) | Closes for legacy lambdas only | Blocked until 5 lands |
| 5 (level-split) | Medium (new T_App_L2_Eff in `TypingL2.v`; thicken L2 wrapper) | Closes at L1 (TFunEff inert at L1) | Natural L2 venue for full effect typing |

Per the CLAUDE.md owner directive "DO escalate before patching": this addendum **escalates the slice 3 redesign decision to the owner**. No code lands until the option is selected.

### What does NOT change

* PR #200 (TFunEff syntax) stays.
* PR #201 (strict predicate, blocker 5 closure) stays.
* PR #203 (this design memo) stays.
* PR #204 (T_Lam_L1_*_Eff rules + R ⊆ R_in side condition cascade) stays.
* PR #205 (slice 3 first attempt findings) stays.
* Counterexample.v (legacy preservation is false) is untouched in all four options.

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

## Slice 3 sub-sub-addendum — option 5a picked, slice plan revised (2026-05-28, session 5)

The owner picked **option 5a** (level-split, intro stays at L1, elim moves to L2) on 2026-05-28 after the session 4 analysis (slice 3 sub-addendum above) and a session 5 design-doc cross-check.

### Why 5a is the right call — design-doc alignment

`PRESERVATION-DESIGN.md` §5.1 lines 468-474 already endorse the L1-intro / L2-elim split explicitly:

> **Why this isn't L1's job.** Effect-typed function types are a typing-layer property, not a region-layer property. Adding them to L1's unparameterised judgment would conflate the two. **L2 is the natural home**: the modality parameter is *already* a typing-layer decoration; the effect annotation rides alongside it. **After L2's effect-typed TFun lands, L1's gap closes by importation, not by re-deriving L1.**

The doc consistently names the introduction rule `T_Lam_L1_Linear` / `T_Lam_L1_Affine` with the `_L1_` infix, confirming that intro lives in L1. Option 5a is therefore not an architectural departure — it returns the slice plan to the design-doc-prescribed line, which session 3's first slice-3 attempt (T_App_L1_Eff in `has_type_l1`) had deviated from.

§10's implementation order ("each step's correctness is independent of the next") imposes no sequencing constraint that blocks 5a.

### 5a vs 5b

Two sub-variants of option 5 exist:

| Sub-option | What | Disposition |
|---|---|---|
| **5a (picked)** | Intro stays at L1 via PR #204; elim adds `T_App_L2_Eff` to `has_type_l2`. | **Picked.** Smallest delta from current main. Design-doc-aligned. |
| 5b | Retract PR #204's L1 intro landing; move both intro and elim into L2. | Discarded — retracts an already-merged PR for marginal architectural neatness; trades real churn for theoretical symmetry. |

### What changes vs the original slice plan

| Slice | Original plan | Option 5a revised plan |
|---|---|---|
| 1 | TFunEff syntax | Unchanged. ✅ MERGED PR #200 |
| 2 | `T_Lam_L1_*_Eff` with R ⊆ R_in side condition | Unchanged — *but reframed as "inert introduction at L1"*. ✅ MERGED PR #204 |
| 3 | `T_App_L1_Eff` in `has_type_l1` | **MOVED**: `T_App_L2_Eff` lands in `has_type_l2` (TypingL2.v) as a sibling of `L2_lift_l1`. |
| 4 | `preservation_l1` lambda-rigidity closure | **SPLIT** into 4a (effect-typed path) + 4b (legacy path) — see below. |
| 5 | Broader effect-typing + Phase B/C unblocks | Naturally hosted in L2 with effect-aware lemmas; `preservation_l2` is the new theorem target. |

### Slice 4 split — what option 5a does and does not close at L1

The session 4 addendum noted that under option 5a, "TFunEff lambdas are inert at L1, and inert values preserve trivially." A session 5 subagent verification confirmed this holds for *one of two* sub-cases inside `preservation_l1`'s `S_App_Step2`:

- **Slice 4a — TFunEff lambdas (effect-typed path).** Under option 5a there is no `T_App_L1_Eff` rule, and the legacy `T_App_L1` at `TypingL1.v:231-234` requires `e1 : TFun T1 T2`, NOT `TFunEff`. No coercion bridge exists (`linear_to_affine` is structural; T_Var/T_Loc cannot hide TFunEff). Therefore any `EApp v1 e2` derivation at L1 with `v1` typed via `T_Lam_L1_*_Eff` is vacuous: no L1 derivation reaches this case. The corresponding sub-case in `preservation_l1` closes by inversion vacuity. **No new proof work needed.**

- **Slice 4b — legacy `TFun` lambdas (body-R-rigidity path).** The legacy `T_Lam_L1_Linear` / `T_Lam_L1_Affine` rules at `TypingL1.v:177-184` still produce `TFun T1 T2`, and `T_App_L1` at `TypingL1.v:231-234` still accepts them. The body-R-rigidity gap documented in `Semantics_L1.v:1708-1713` *remains* for these lambdas under option 5a — option 5a's level-split does **not** add structural information that closes legacy `TFun` lambda-body preservation across an R-shift. **This sub-case stays gated.**

Implication: `preservation_l1` as currently stated (over the whole `has_type_l1` judgment) cannot Qed under option 5a alone. The natural closure venue is `preservation_l2` — a new theorem stated over `has_type_l2`, where effect-typed paths are fully covered and legacy `TFun` paths are honestly carried forward via L1 importation (with the legacy body-R-rigidity admit recorded as inherited debt rather than concealed).

### The T_App_L2_Eff rule design

The L2 elimination rule mirrors `T_App_L1` but with effect threading through R_in/R_out:

```coq
| T_App_L2_Eff : forall m R R1 G G' G'' e1 e2 T1 T2 R_in R_out,
    has_type_l2 m R  G  e1 (TFunEff T1 T2 R_in R_out) R1   G' ->
    has_type_l2 m R1 G' e2 T1                        R_in G'' ->
    has_type_l2 m R  G  (EApp e1 e2) T2              R_out G''
```

Reading: e1 produces an effect-typed lambda (consuming R → R1, where R1 is the intermediate env after e1's evaluation). e2 evaluates the argument, threading R1 → R_in (the lambda's input expectation). The lambda body then runs, consuming R_in and producing R_out. The whole `EApp` expression's output env is R_out.

The e1 sub-derivation at type `TFunEff T1 T2 R_in R_out` lifts from an L1 derivation via `L2_lift_l1` (since `T_Lam_L1_*_Eff` rules are still the source of TFunEff typings — option 5a keeps intro at L1).

**Side condition discharge**: PR #204's `(forall r, In r R -> In r R_in)` constraint (R ⊆ R_in on the lambda's input env) was the load-bearing invariant for slice 2's substitution closure. At elimination time (T_App_L2_Eff), this constraint flows naturally — the lambda was formed at R ⊆ R_in, and the call site supplies R_in directly via e2's output env. No new side condition is needed at elimination.

### Implementation surface (verified by session 5 subagent audit)

`formal/TypingL2.v` currently has a single constructor `L2_lift_l1` at lines 85-91 — a modality-indexed lift-only inductive ready for thickening. Adding `T_App_L2_Eff` as a sibling constructor (insertion point: after line 91) is additive and has zero downstream consumers in `formal/*.v` (only the file itself references `has_type_l2`). Existing utilities (`weaken_modality`, `weaken_modality_le`, `lift_l1_to_*`, `project_l2_to_l1`) continue to work — they bridge via `L2_lift_l1` for L1-derived facts and the new constructor adds an independent path for T_App_L2_Eff derivations.

### Slice plan (post-option-5a)

| Slice | Scope | Status |
|---|---|---|
| 1 | TFunEff syntax | ✅ MERGED PR #200 |
| 2 | `T_Lam_L1_*_Eff` rules with R ⊆ R_in side condition | ✅ MERGED PR #204 |
| 3 (option 5a) | `T_App_L2_Eff` in TypingL2.v as a sibling constructor to `L2_lift_l1` | **Next** |
| 4a | TFunEff path inert-at-L1 (closes by inversion vacuity) | Bundled with slice 5 (`preservation_l2`) |
| 4b | Legacy `TFun` body-R-rigidity at preservation_l1 | **Stays gated**; honest admit carried forward into `preservation_l2` via L1 importation |
| 5 | `preservation_l2` (new theorem); broader effect-typing; Phase B/C unblocks | After slice 3 |

### What does NOT change

* PR #200 (TFunEff syntax) — unchanged.
* PR #201 (strict predicate, blocker 5 closure) — unchanged.
* PR #203 (Phase D memo) — unchanged.
* PR #204 (T_Lam_L1_*_Eff rules) — unchanged. Reframed as "inert introduction at L1."
* PR #205 (slice 3 first attempt findings) — unchanged (archaeology).
* PR #207 (slice 3 sub-addendum, option 4 non-viability) — unchanged.
* Counterexample.v — untouched.

### Disposition of session 4's candidate matrix

| Option | Disposition |
|---|---|
| 1 (split lemma) | Discarded — non-value variant still blocked per session 4 caveat. |
| 2 (env-frame Δ) | Discarded — `remove_first` still cuts R_in per session 4 caveat. |
| 3 (defer) | Discarded — punts the design question; slice 5 ends up needing option 5 anyway. |
| 4 (meta-lemma) | Discarded — proved non-viable in session 4 sub-addendum (above). |
| **5a (level-split, intro at L1, elim at L2)** | **Picked.** Smallest delta from current main. Design-doc-aligned. |
| 5b (both intro and elim at L2) | Discarded — retracts PR #204's already-merged L1 landing; higher churn for marginal architectural neatness. |

### Owner directive compliance

Per CLAUDE.md owner directive 2026-05-27:

* ✅ Zero new `Admitted.` or `Axiom.` declarations planned for slice 3.
* ✅ No patching of `Semantics.v` `preservation` (provably false).
* ✅ No patching of legacy `Typing.v` judgment.
* ✅ `Counterexample.v` regression theorem untouched.
* ✅ Honest accounting of the slice 4b gap (not closed by option 5a; carried forward into `preservation_l2`).
* ✅ All commits GPG-signed.
* ✅ Auto-merge ON for every PR.
