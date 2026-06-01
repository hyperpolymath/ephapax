<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Hand-off: closing `preservation` in `formal/Semantics.v`

> # 🛑 ARCHAEOLOGY ONLY — do NOT follow the closure plans in this file
>
> The verified counterexample at `formal/Counterexample.v` (five
> lemmas `Qed.`) shows `Theorem preservation` in `formal/Semantics.v`
> is **provably false**. The reduction-from-910-goals story below is
> the **historical record** of attempts that, at the time, looked
> like they would close it. None of them work — preservation
> cannot be closed because no proof exists.
>
> **DO NOT** spend session time on:
> - The 5-phase "Preservation closure plan" (Lemma B / region-weakening
>   / Phase 5 Qed flip) — that section has been removed from
>   `ROADMAP.adoc` as of 2026-05-27.
> - Continuing the 12 → 0 reduction story.
> - Extending the legacy `Semantics.v` with new lemmas to support
>   any of the above (`step_preserves_type_at_pre`,
>   `step_output_context_eq_at_pre`, etc. are all in this class).
>
> The canonical design for the fix is the **four-layer redesign** in
> `formal/PRESERVATION-DESIGN.md`. Preservation is re-derived
> per-layer (`preservation_l1` in `Semantics_L1.v`, etc.), not
> closed against the legacy judgment. The owner directive
> (2026-05-27) is in `CLAUDE.md` at the repo root.
>
> This file is retained so the per-case diagnostic data (which
> congruence patterns hit which obstacle, etc.) remains available
> to inform the layered design — but reading it as a closure plan
> is the trap.

Diagnostic + remediation log. The proof is still `Admitted.`, but as
of **2026-05-21** it's **down from 910 open goals to 12** via four
landed PRs. This file tells whoever picks it up next exactly what's
open and what the canonical closure path is.

> **The canonical closure plan is now in `formal/PRESERVATION-DESIGN.md`**
> (four-layer redesign; L1 region capability threading). The prior
> "Preservation closure plan" in `ROADMAP.adoc` is superseded; this
> file remains as the per-case diagnostic record. Read the design
> doc first; come back here for case detail and the historical
> closure-attempt log.

## State at a glance

| Date | Open goals | Notes |
|------|-----------:|-------|
| 2026-04-27 | "fully closed" | In-file comment — but `coqc` rejected the `Qed.`. The claim was unsubstantiated; the proof never closed. |
| 2026-05-20 (am) | 910 | Discovered via `Show. Show Existentials.` before the `Admitted.`. Exactly 35 (step rules) × 26 (typing rules). The existing `try solve [...]` chain closes ZERO. |
| 2026-05-20 (pm) | 29 | After the standard preservation pattern (`remember (mu, R, e) as cfg` + symmetric for cfg', then `inversion Hcfg; subst; inversion Hcfg'; subst;` inside each case). 97% reduction. PR #102. |
| 2026-05-20 (eve) | 22 | After `revert mu R e mu' R' e' Hcfg Hcfg'` before `induction Hstep` so each case's IH carries universal quantification over the inner step's config. PR #106. |
| 2026-05-20 (eve) | 22 | Region-invariance lemma `step_R_eq_or_touches_region` landed as infrastructure (no goal closures). PR #114. |
| 2026-05-20 (night) | **12** | 10 β-reduction / value-step cases discharged via per-case manual proofs using the lemma. PR #116. **98.7% reduction across one day.** |
| 2026-05-24 | Lemma B 4/35 closed | `step_output_context_eq` scaffolded with `cfg`-remember pattern. Atomic-axiom tactic closes 4 step rules. PRs #121/#124/#126. |
| 2026-05-24 (late) | Lemma B 31/35 closed | Cluster A (β-reduction, 7) **FULLY CLOSED** via `subst_preserves_typing_strong` + `output_ctx_det`. Cluster C (region/compound-value, 6) **FULLY CLOSED** via inversion + `value_context_unchanged`. Cluster B (congruence) 9 of 18 closed via R-shape dispatch. |
| 2026-05-26 | **1 + 1 + 12** | Empirical `coqc 8.18.0` re-verification: 1 admit in `step_preserves_type` (Semantics.v:4885), 1 admit in `step_output_context_eq` (Semantics.v:5963), 12 cascading goals in `preservation`. The two upstream admits are the SAME structural sub-case — S_Region_Step's `r = r1` "exited from inside" — mirrored across both lemmas. |
| 2026-05-26 (eve) | **0 + 0 + 12** (Qed × 2) | **Path 3 (at-pre helper) lands.** Both upstream lemmas are now `Qed`. Introduced two NEW helper lemmas (`step_preserves_type_at_pre` and `step_output_context_eq_at_pre`) whose typings are at the SHARED pre-step env R. The S_Region_Step cross-case `T_Region_Active × T_Region` collapses to a contradiction (In r R vs ~In r R at same env) — sidestepping the original obstacle. Plug-in via `region_env_perm_typing` + `remove_first_then_cons_membership_eq` (existing, Qed). The 12 cascading goals in `preservation` remain — they're a SEPARATE structural problem, not the shared admit. |
| 2026-05-26 (late eve) | **Qed × 4 + 11** | **Swarm A + B + C complete.** `step_preserves_type_at_pre` and `step_output_context_eq_at_pre` are now Qed (Swarm A + B per-goal closures landed). Swarm C oracle splice closes all 10 congruence LEFT branches in `preservation` via `step_output_context_eq` (Qed) — `assert Gmid = Gout by (eapply step_output_context_eq; …); subst` unifies the IH's existential output context with the sibling's Gmid. `S_StringLen_Step` closes ENTIRELY as vacuous (`EBorrow`'s inner is `EVar` or value, neither steps — pattern lifted from `S_Borrow_Step` elsewhere in this proof). 11 admits remain in `preservation`: 10 RIGHT-only sub-cases (`HTR : touches_region` in scope) + 1 `S_Region_Step` (special). All 10 RIGHT cases share the same shape and block on the same region-env weakening lemma for non-values (= Brief C, structural follow-up). |
| 2026-05-26 (night) | **Qed × 4 + 11** (narrowed) | **MIDDLE narrowing lands.** Converted all 10 congruence `S_*_Step` blocks from 2-way (`step_R_eq_or_touches_region`) to 3-way (`step_R_change_shape`) dispatch. LEFT branch unchanged. **MIDDLE (R' = rw :: R, push)** now closes via the same `step_output_context_eq` oracle on the stepped child + `region_add_typing` to lift the sibling typing from `R` to `rw :: R`. RIGHT (`R' = remove_first r R`, pop) remains `idtac`. Result: each of the 10 admits is now narrower — `Hrem : R0' = remove_first r R0` and `HinR : In r R0` are in scope (vs the broader `HTR : touches_region` before). Brief C's required lemma reduces from "region-env weakening across any touches_region step" to "pop-only weakening" (the surviving sibling must be transportable from `R` to `remove_first r R` when `In r R`). Coq subtlety: the 2 S_StringConcat blocks must use `[rw …]` instead of `[r …]` in the destruct pattern because the outer T_StringConcat inversion binds an `r` (the TString region) in scope already. |

> **Path 3 (landed 2026-05-26 eve):** The Option 2 plan (structural
> recursion deriving `expr_free_of_region`) was **blocked** by the
> `ELet (ERegion r v_inner) (ELoc l r)` counterexample (sibling
> references to r survive the exit, so `expr_free_of_region r e'` is
> false in general). Path 1 (mutual induction) would have been a
> heavy refactor (~8-12h).
>
> Path 3 introduces TWO helper lemmas whose signatures match the
> upstream pair except both typings are at the SHARED pre-step env R
> (not R/R'). In this framing, the S_Region_Step cross-case
> `T_Region_Active × T_Region` collapses to a vacuous contradiction
> (`In r R` vs `~In r R` at the same env), sidestepping the obstacle.
> The plug-in then uses the existing `region_env_perm_typing` to
> transport the body's typing from `r :: remove_first r R0` to `R0`
> (membership-equivalent when `In r R0`). Net code change: ~100
> lines + 2 helper bodies (~1600 lines copy-paste from upstream).
> Wall-clock: **~3h** to land both Qed flips.
>
> **Status of the helpers themselves (2026-05-26 late eve, commit
> `d6ebf68`):** both are now `Qed`. The mass-copied Cluster A/B/C
> tactic blocks (verbatim from the upstream lemmas, patterns use
> `?R`/`?R'` polymorphically) close the bulk; the residual cases that
> didn't fit those patterns are closed by explicit `1: {...}` per-
> goal blocks at the tail of each helper — 5 in
> `step_preserves_type_at_pre` (S_StringConcat_Step2, S_App_Step2,
> S_Snd atomic, S_Case_Step, S_Copy atomic) and 11 in
> `step_output_context_eq_at_pre` (the listed S_*_Step congruence
> cases). The upstream `step_preserves_type` and
> `step_output_context_eq` `Qed` chain is therefore non-axiomatic.
>
> **Status of preservation:** 12 cascading goals remain, expected to
> still need a region-env weakening for non-values (per the original
> analysis below). The at-pre helpers DON'T directly help with these
> — they help with the UPSTREAM lemma obstacle, not preservation's
> own touches_region RIGHT branch. Re-diagnosis is in progress now
> that step_preserves_type + step_output_context_eq are available as
> oracles.

## What the 910 → 29 fix did

The prior `induction Hstep` did not substitute the outer expression
slot `e` to the constructor's form — so `inversion Htype` produced
all 26 typing arms per step rule instead of just the diagonal. Cross-
cases (e.g. `S_StringNew` step + `T_Unit` typing) had no
discriminating equation in scope, so `try solve [exfalso;
discriminate | exfalso; congruence]` couldn't fire.

The fix:

```coq
intros mu R e mu' R' e' Hstep.
remember (mu, R, e) as cfg eqn:Hcfg.
remember (mu', R', e') as cfg' eqn:Hcfg'.
induction Hstep; intros G0 T0 G0' Htype;
  inversion Hcfg; subst;
  inversion Hcfg'; subst;
  inversion Htype; subst;
  (* … existing try-solve chain …  *)
```

`remember` turns `Hstep : step (mu, R, e) (mu', R', e')` into
`Hstep : step cfg cfg'` with two side equations `Hcfg : ... = (mu, R,
e)`, `Hcfg' : ... = (mu', R', e')`. Now `induction Hstep` substitutes
the constructor's "from" config into `cfg` and the equation `Hcfg`
becomes (for `S_StringNew`) `(mu0, R0, EStringNew r s) = (mu, R, e)`.
`inversion Hcfg; subst` decomposes this and substitutes
`e := EStringNew r s` everywhere — including in `Htype`. Then
`inversion Htype; subst` only generates the diagonal `T_StringNew`
arm; the 25 cross-arms are eliminated by inversion's constructor-
mismatch check.

The earlier `remember e_typed as e_orig eqn:He_orig` (the original
"preserve discriminating equation" attempt) was a misdiagnosis — it
remembered the *typing's* `e`, which was already abstract; the
problem was that the *config's* expression slot was abstract.

## How to reproduce the diagnostic

```coq
    end).
Show.            (* prints current goal *)
Show Existentials. (* prints all 29 unresolved metavariables *)
Admitted.
```

then:

```sh
cd formal
coq_makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
```

`coqc` prints goal count + every open existential. Restore the
`Admitted.` afterwards. Same recipe (now yielding 29 instead of 910)
is the per-case work list.

## The 29 remaining goals (per-case checklist)

### Axiom cases needing explicit reconstruction (~3 goals)

| Step rule | Goal needs | Tactic sketch |
|-----------|-----------|---------------|
| `S_StringNew` | type `ELoc l r` at `TString r` | `eexists; eapply T_Loc; eauto using mem_alloc_lookup` |
| `S_StringConcat` | type `ELoc l' r` at `TString r0` | same as above, with the new alloc |
| `S_StringLen` | type `EI32 (String.length s)` at `TBase TI32` | `eexists; constructor` |

### β-reduction cases needing `subst_preserves_typing` (~6 goals)

| Step rule | Tactic |
|-----------|--------|
| `S_Let_Val`, `S_LetLin_Val`, `S_App_Fun`, `S_Fst`, `S_Snd`, `S_Case_Inl`, `S_Case_Inr` | `eexists; eapply subst_preserves_typing; eauto` (most should fall through the existing chain once the expression slots are concrete) |
| `S_If_True`, `S_If_False` | `eexists; eassumption` (the branch typing is already in context) |

### Congruence cases needing IH + reconstruction (~15 goals)

For each `S_*_Step`: `destruct (IHHstep ...) as [G_out Hout]; eexists;
econstructor; eauto`. The IH's form is awkward after `remember` —
contains the `Hcfg`/`Hcfg'` equations as extra premises. May need
`specialize IHHstep with (1 := Heqcfg_inner) (2 := Heqcfg'_inner)`
first, or restructure to revert + induct on typing instead of step.

### Region cases (~3 goals)

| Step rule | Status |
|-----------|--------|
| `S_Region_Enter` | typing reconstruction (`T_Region_Active` + `In r (r::R)`) — the existing `try solve [eexists; eapply T_Region_Active; ...]` should fire |
| `S_Region_Exit` | needs `region_shrink_preserves_typing` (existing — Qed) + the `expr_free_of_region` step premise |
| `S_Region_Step` + `T_Region_Active` | **the bottleneck** — needs a **region-env *weakening* lemma for non-values** that does not yet exist. Roughly: `forall R e G G' T r, R; G \|- e : T -\| G' -> ~ In r R -> e is not a value -> (r :: R); G \|- e : T -\| G'`. The "not a value" precondition is delicate — naive weakening is unsound for `EBorrow` and friends. Probably 50–150 LOC by itself. |

### Linear cases (~2 goals)

| Step rule | Tactic |
|-----------|--------|
| `S_Drop` | `eexists; constructor` (drop yields `EUnit : TBase TUnit`) |
| `S_Copy` | `eexists; constructor; assumption` (copy yields `EPair v v : TProd T T`) |

## What it would take to finish

Realistic estimate: **days, not weeks** — the 29 remaining goals are
all standard preservation-proof glue except for the region-env
weakening lemma. The lemma's design (which non-value carriers admit
weakening, which don't) is the only genuine theory question. The
mechanical 28 are 1–2 days of tactic work.

## What is NOT a fix

- Adding more `try solve [...]` lines to the existing chain at random.
  Run `Show. Show Existentials.` first to see what's actually open.
- Replacing `induction Hstep` with `inversion Hstep` — that loses the
  IHs needed for congruence cases.
- Mass-`Admitted.` per case — defeats the point and conflicts with
  estate's "build is the only oracle" policy. The honest mark is one
  `Admitted.` on `preservation`, not 29.

## `step_preserves_type` per-case status (2026-05-24, late)

Empirically verified against `coqc 8.18.0`. The 12 cases identified
as "remaining open" after the f499c82 clone-out have now each been
given an explicit per-case proof skeleton. **Three iterations**:

1. **First pass**: dispatched on `step_R_eq_or_touches_region`,
   closed the LEFT (R = R') branches, admitted RIGHT. 8 admits remained.
2. **Second pass**: introduced finer `step_R_change_shape` (3-way
   disjunction: equal / prepend r / remove_first r), closed the MIDDLE
   (prepend) branch for all 7 congruence cases via `region_add_typing`.
   Still 8 admits, but each tied to the strictly-narrower
   "remove_first r R" sub-case rather than the broader "touches_region".
3. **Third pass**: added the `remove_first_then_cons_membership_eq`
   helper (proving `r :: remove_first r R` and `R` have the same
   membership whenever `In r R`, no `NoDup R` required) and used it
   with `region_env_perm_typing` to close the RIGHT (`remove_first`)
   sub-case in all 7 congruence proofs. **Now 1 admit remains**,
   tied to S_Region_Step's exfalso when the inner step exits the
   outer region from inside (r = r1 sub-case).

**Moved** `touches_region` + `step_R_eq_or_touches_region` to before
`step_preserves_type` so the latter can dispatch on the LEFT
(R = R') branch.

### Fully closed (4 of 12)

| Goal | Step rule | Closure |
|------|-----------|---------|
| 1 | `S_StringConcat_Step2` | outer T = TString r is structurally constrained; IH on (e2, e2') gives r = r' |
| 8 | `S_Snd` atomic (ESnd (EPair v1 v2) → v2) | `value_context_unchanged` on v1 + `type_determinacy` on v2 |
| 10 | `S_Region_Exit` (ERegion r v → v) | `region_shrink_preserves_typing` bridges R0 and remove_first r R0, then `type_determinacy` |
| 12 | `S_Copy` atomic (ECopy v → EPair v v) | `value_context_unchanged` on first projection + two `type_determinacy` calls on v |

### Fully closed via R-shape dispatch (7 of 12 congruence cases)

After the third pass, every congruence case closes via the 3-way
dispatch on `step_R_change_shape`:

| Goal | Step rule | LEFT (R = R') | MIDDLE (R' = r :: R) | RIGHT (R' = remove_first r R) |
|------|-----------|----------------|----------------------|-------------------------------|
| 2 | `S_Let_Step` | ✅ | ✅ via `region_add_typing` | ✅ via lift+perm |
| 3 | `S_LetLin_Step` | ✅ | ✅ | ✅ |
| 4 | `S_App_Step2` | ✅ | ✅ | ✅ |
| 5 | `S_If_Step` | ✅ | ✅ | ✅ |
| 6 | `S_Pair_Step1` | ✅ | ✅ | ✅ |
| 7 | `S_Pair_Step2` | ✅ | ✅ | ✅ |
| 9 | `S_Case_Step` | ✅ | ✅ | ✅ |

The RIGHT sub-case (when the inner step exits a region) is closed by:
1. `region_add_typing` lifts the post-step sibling typing from
   `remove_first r R0` to `r :: remove_first r R0`.
2. `region_env_perm_typing` converts to `R0` via
   `remove_first_then_cons_membership_eq` — the new helper that proves
   `r :: remove_first r R0` and `R0` have the same membership when
   `In r R0` (NO `NoDup R` invariant needed; works even for duplicates).
3. `type_determinacy` aligns the types under the now-shared `R0`.

### Partially closed — one sub-case admitted (1 of 12)

| Goal | Step rule | Closures | Remaining admit |
|------|-----------|----------|-----------------|
| 11 | `S_Region_Step` (ERegion r e → ERegion r e') | T_Region (Hte) contradicted by `In r R0`; T_Region_Active × T_Region_Active via IH; T_Region_Active × T_Region 3 of 4 R-shape sub-cases close (R = R', R' = r1::R0, R' = remove_first r1 R0 with r ≠ r1) — all by contradiction with `~In r R0'` | One sub-case: T_Region_Active × T_Region with `R0' = remove_first r R0` (the outer r is exited from inside). Closing requires `expr_free_of_region r e'` to shrink the post-step inner typing, derivable but requires further inversion on `Hstep` to reach the underlying `S_Region_Exit`'s premise. |

### Net effect

- **Before**: `step_preserves_type` was `all: admit` with 12 open
  goals — every case admitted with no structure.
- **After (pass 1)**: 4 of 12 closed fully, 7 of 12 had LEFT (R = R')
  branch closed, 1 of 12 had main branch closed. 8 admits.
- **After (pass 2)**: each congruence admit narrowed to just the
  `R' = remove_first r R` sub-case via `step_R_change_shape` +
  `region_add_typing`. Still 8 admits but each strictly narrower.
- **After (pass 3)**: all 7 congruence RIGHT sub-cases closed via the
  new `remove_first_then_cons_membership_eq` helper +
  `region_env_perm_typing`. **1 admit remains** — the
  `T_Region_Active × T_Region` cross-case of `S_Region_Step` when
  the inner step exits the outer region from inside.

New supporting lemmas added (all `Qed.`):
- `step_R_change_shape` (~10 LOC): refines the 2-way disjunction
  into 3-way, also exposing `~In r R` / `In r R` for the prepend /
  remove cases.
- `remove_first_then_cons_membership_eq` (~15 LOC): proves
  `(r :: remove_first r R)` and `R` have the same membership when
  `In r R`. NO `NoDup R` required.

The single remaining admit is the cross-case where `Hte` uses
`T_Region_Active` and `Hte'` uses `T_Region` — meaning the inner
step exits the outer `ERegion`'s own region `r`, and `r` was unique
in `R0` (so post-step `~In r remove_first r R0`).

**The genuine obstacle:** `e'` may syntactically reference `r` even
though `r` was unique pre-step. Concrete witness: if
`e = ELet (ERegion r v_inner) (ELoc l r)`, then after the inner
`S_Region_Exit` we get `e' = ELet v_inner (ELoc l r)`. The post-step
sibling `ELoc l r` still references `r`, so `expr_free_of_region r e'`
is false. Yet `e'` is well-typed under `r :: remove_first r R0`
because `T_Region` re-introduces `r` at the head, making
`ELoc l r` typeable via the freshly-bound `r`. This is the
semantic-freshness issue inherent to concrete-name region encodings:
with alpha-renaming the post-step `r` would be a distinct region
name; with concrete names the syntactic occurrence persists.

Consequences for closure paths:
- Adding `NoDup R` as an invariant does **not** close it. The
  `T_Region`-vs-`T_Region_Active` choice in `Hte'` already encodes
  uniqueness in scope (`H3 : ~In r remove_first r R0` plus
  `H : In r R0` implies `r` unique). NoDup gives no extra info.
- A `typing_implies_free_of_absent_region` lemma doesn't apply
  because `e'` is typed at `r :: remove_first r R0` where `r` IS
  present (at the head), so `~In r R` doesn't hold for the typing
  in scope.
- A `step_exit_implies_free_of_exited_region` lemma would be **false**
  for congruence cases that preserve siblings — the sibling's
  surviving `r`-references break the freedom claim.

The genuinely-closing options are:
1. **Mutual recursion with `preservation`**: prove `preservation`
   and `step_preserves_type` simultaneously. `preservation`'s direct
   construction of a typing for `e'` at the post-step `R'` provides
   exactly what this admit needs. Standard textbook approach for
   region calculi, but a significant restructuring touching both proofs.
2. **Inversion on `Hstep` with structural recursion**: directly case-split
   on the step rule path that produced `R' = remove_first r R0`,
   handling the `S_Region_Exit`-at-top sub-case via region_shrink
   (works because `e' = v`, free of `r` by `S_Region_Exit`'s premise),
   and handling the congruence-bubbling sub-cases by recursive structural
   argument on the wrapping. ~150 LOC, orthogonal to the current case split.

Both are substantial follow-ups. The current single admit is bounded
and well-documented; closing it should be deferred to whoever takes
on (1) or (2) as a focused effort.

## Lemma B per-case status (2026-05-24)

Empirically verified against `coqc 8.18.0`. The Phase 1 scaffold for
`step_output_context_eq` now uses the `cfg`-remember pattern that
mirrors `step_R_eq_or_touches_region` and `preservation`, plus an
atomic-axiom closure tactic. **4 of 35 step rules close**; 31 remain.

### Closed (4)

| Step rule | Why it closes |
|-----------|---------------|
| `S_StringNew` | atomic: `EStringNew → ELoc`, both type to identity-output |
| `S_StringConcat` | atomic: `EStringConcat (ELoc _) (ELoc _) → ELoc`, all premises invert to identity-output T_Loc |
| `S_Drop` | atomic: `EDrop (ELoc _) → EUnit`, both T_Drop and T_Unit are identity-output |
| `S_Borrow_Step` | **accidental congruence closure**: both `T_Borrow` and `T_Borrow_Val` output the input context unchanged, so `Ga = G = Gb` regardless of whether the inner step is reachable. Vacuous-but-closes. |

### Open (24, was 31)

#### Cluster A — β-reduction ✅ FULLY CLOSED (2026-05-24)

All 7 β-reduction cases closed via
`subst_preserves_typing_strong` (PR: this branch) + `output_ctx_det`
(PR: this branch). Recipe per case:
1. Invert the outer compound typing (`T_Let`, `T_App`, `T_If`,
   `T_Case`) to expose body + value premises.
2. For T_App: also invert `T_Lam` on the function value.
3. For T_Case: apply `value_context_unchanged` on the EInl/EInr
   premise, then invert `T_Inl`/`T_Inr`.
4. Apply `value_context_unchanged` on the value premise(s) to
   align intermediate contexts with the input context.
5. `destruct (subst_preserves_typing_strong ...)` to construct a
   typing of the substituted form at the specific output context.
6. `eapply output_ctx_det` against `Htype_e'` to conclude
   `Ga = Gb`.

Closed cases: `S_Let_Val`, `S_LetLin_Val`, `S_App_Fun`,
`S_If_True`, `S_If_False`, `S_Case_Inl`, `S_Case_Inr`.

#### Cluster B — congruence (10 of 18 closed, 8 open)

**Closed (2026-05-24)**: `S_StringConcat_Step1`,
`S_StringConcat_Step2`, `S_Pair_Step1`, `S_Pair_Step2`,
`S_Inl_Step`, `S_Inr_Step`, `S_Copy_Step`, `S_If_Step`,
`S_StringLen_Step`. (Plus `S_Borrow_Step` closed accidentally
earlier.)

Recipe (canonical two-child congruence, e.g.
`S_StringConcat_Step1`):
1. Invert both `Hte` and `Hte'`.
2. `pose proof step_R_eq_or_touches_region` to dispatch `R = R'`.
3. LEFT (R = R'): apply IH on inner step's typings to get
   `Gmid = Gmid'`; `output_ctx_det` on the unchanged sibling
   closes.
4. RIGHT (`touches_region`): locally `admit` per-case.

Variants:
- Second-child congruences (`S_StringConcat_Step2`,
  `S_Pair_Step2`): use `value_context_unchanged` on the first
  child (the value) to align contexts before IH on the second
  child.
- Single-child congruences (`S_Inl_Step`, `S_Inr_Step`,
  `S_Copy_Step`): no sibling, IH directly closes.
- `S_If_Step`: condition at `TBase TBool` (fixed type), branches
  at outer `T` — fully constrained.
- `S_StringLen_Step`: vacuous via inversion chain (T_StringLen →
  T_Borrow / T_Borrow_Val: the inner must be `EVar` or a value;
  neither steps).

**Open (6 of original 8)** — blocked on **type-alignment circularity WITHOUT independent-context sibling**:

S_App_Step1 and S_App_Step2 closed via the "sibling type_determinacy"
trick (their sibling's context — `Gmid` for Step1, `G` for Step2 via
value_context_unchanged — is independent of the unconstrained `T1`).

For the remaining cases, no such sibling exists or its context
depends on the unconstrained type:

| Step rule | Inner-type that's NOT fixed by outer T |
|-----------|----------------------------------------|
| `S_Let_Step` | `T_Let`'s binding type `T1` |
| `S_LetLin_Step` | `T_LetLin`'s binding type `T1` |
| `S_Case_Step` | `T_Case`'s scrutinee `TSum T1 T2` |
| `S_Drop_Step` | `T_Drop`'s arg type `T` (outer is `TBase TUnit`) |
| `S_Fst_Step` | `T_Fst`'s second component `T2` |
| `S_Snd_Step` | `T_Snd`'s first component `T1` |

For each: T_X inversion of Hte and Hte' produces independent
fresh type-vars for the unconstrained inner types. To apply
Lemma B's IH on the inner step, we'd need to know both typings
are at the SAME inner type — but establishing that requires
preservation. Circular.

**Resolution paths**:
1. Prove Lemma B and preservation by **simultaneous mutual
   induction** (restructure both proofs).
2. **Re-state Lemma B** with a conclusion that doesn't need
   shared T (weaker output-context-equivalence).
3. Add a **type-preservation-under-step** sub-lemma (essentially
   the type-only part of preservation) and prove it separately
   via a more restricted induction.

#### Cluster C — region / compound-value ✅ FULLY CLOSED (2026-05-24)

**Closed**: `S_Fst`, `S_Snd`, `S_Copy`, `S_Region_Exit`,
`S_StringLen` (atomic), `S_Region_Enter`. All 6.

Recipes:
- `S_Fst`, `S_Snd`, `S_Copy`, `S_Region_Exit`: invert the compound
  rule (T_Fst → T_Pair, T_Snd → T_Pair, T_Copy, T_Region_Active),
  apply `value_context_unchanged` on each value-typing premise to
  align intermediate contexts with G, then `reflexivity` closes.
- `S_StringLen` atomic: 3-level inversion chain T_StringLen →
  T_Borrow_Val (T_Borrow's EVar form contradicted by ELoc) → T_Loc.
  Each preserves the context, so Ga = G. T_I32 on Hte' gives Gb = G.
- `S_Region_Enter`: 4 inversion sub-goals from T_Region /
  T_Region_Active × Hte / Hte'. Two contradiction patterns:
  `tauto` closes Hn-vs-`In r R0` cases; explicit
  `apply H; left; reflexivity` closes the `~ In r (r :: R0)`
  case. The valid sub-goal (Hte = T_Region, Hte' = T_Region_Active)
  closes via `output_ctx_det` on the two inner typings of `e` at
  `(r :: R0); G`.



| Step rule | What's needed |
|-----------|---------------|
| `S_Region_Enter` | `T_Region` ↔ `T_Region_Active` dispatch via `In r R`; needs `output_ctx_det` sub-lemma on `e_inner` |
| `S_Region_Exit` | needs `region_shrink_preserves_typing` (already Qed) + value-output-context invariance |
| `S_Region_Step` | **blocked on Phase 3** — region-env weakening for non-values |
| `S_StringLen` (atomic!) | inversion of `T_StringLen` → `T_Borrow_Val` → `T_Loc` chain needs explicit nested invocation; my repeat-match doesn't cover the `EBorrow (ELoc _ _)` shape |
| `S_Copy` | atomic but compound: `T_Copy` outputs `G'` where `G'` is value-input; needs `value_context_unchanged` invocation |
| `S_Fst` / `S_Snd` | atomic but inversion of `T_Pair` premise needs `value_context_unchanged` to align inner v1/v2 typings |

### Effort revision (current — 2026-05-26)

The earlier "8-15 focused hours for Lemma B alone" estimate (recorded
2026-05-24) was keyed off a "31 remaining cases" framing. Subsequent
work on the same day closed Clusters A and C entirely, and most of
Cluster B, leaving the shape below.

Empirical `coqc 8.18.0` verification (2026-05-26):

- `step_preserves_type`: **1 open admit** at `Semantics.v:4885`
- `step_output_context_eq` (Lemma B): **1 open admit** at `Semantics.v:5963`
- `preservation`: 12 cascading goals (the `S_*_Step` congruence
  cases + `S_Region_Step`) — these close mechanically once Lemma B is
  `Qed.`; they are NOT independently hard.

The two upstream admits are the SAME structural sub-case (S_Region_Step's
`r = r1` "inner step exits the outer region from inside") mirrored
across both lemmas.

**Revised estimate: 4-6 hours wall-clock** for the whole chain to `Qed`:

- ~3h: Option 2 helper lemma body
  (`exit_implies_typing_at_remove_first`, ~150 LOC by structural
  recursion on `Hstep`).
- ~1h: plug helper into the two upstream admits.
- ~2h: Phase 2 cascade through `preservation`'s 12 congruence goals
  (most fall through the existing `all: try (...)` chain once Lemma B
  is `Qed.`).
- ~1h: unwind checklist (PROOF-NEEDS.md, ROADMAP.adoc,
  RUST-SPARK-STANCE.adoc, delete this file, `Admitted → Qed`).

### Effort revision (historical — 2026-05-24)

[Retained for context; superseded by the section above.]

- 4 trivial cases closed by a uniform tactic in ~30 minutes.
- Each of the remaining 31 needs a hand-rolled per-case tactic block.
- Cluster A (7) needs one shared sub-lemma first
  (`subst_preserves_typing_strong`).
- Cluster B (17–18) shares the same recipe but each case names
  different premises and constructor arguments — call it ~10 minutes
  per case once the recipe is debugged on the first one.
- Cluster C (6) is a mixed bag; `S_Region_Step` carries Phase 3 risk.

Original estimate: **8–15 focused hours** for Lemma B alone. Cluster A
and Cluster C closed by 2026-05-24 night; most of Cluster B by the same
session. By 2026-05-26 the surface had collapsed to the single shared
S_Region_Step admit.

### Watch for: circularity risk

Some Cluster B cases require knowing that `e` and `e'` have the
same type before applying the IH. `type_determinacy` operates on
same-expression pairs, not stepped pairs. The natural lemma —
"step preserves type" — is part of what preservation itself
proves. If the inductive structure of Lemma B turns out to need
preservation as a sub-lemma, the closure path needs revision.
Watch for this when attacking the first Cluster B case.

## Open: region-env weakening for non-values (2026-05-26)

After `step_preserves_type` and `step_output_context_eq` reached Qed
(via the at-pre helper pattern, Path 3 above), preservation's 12
remaining admits split into two flavours:

| Sub-case | Count | Blocker |
|----------|------:|---------|
| Congruence RIGHT (touches_region) | 11 | r-shrunk env, sibling might reference r |
| `S_Region_Step` + `T_Region_Active` × `T_Region` (r=r1) | 1 | same shape inside `step_preserves_type_at_pre` |

The 11 RIGHT-branch admits each have shape:

> `Hstep : (mu, R, e1) -->> (mu', R', e1')`,
> `HTR  : touches_region e1`,
> `H1   : R; G |- e1 : T1 -| Gmid`,
> `H2   : R; <ctx> |- e2 : T2 -| <ctx'>`     (the unchanged sibling),
> `IH   : ... → exists G_out, R'; G |- e1' : T1 -| G_out`
>
> ⊢ `exists G_out, R'; G |- COMPOUND e1' e2 : ... -| G_out`

The IH gives the stepped child at `R'`. The sibling `e2` is still
typed at `R`. To reconstruct `COMPOUND e1' e2` at `R'`, we need
`R'; <ctx> |- e2 : T2 -| <ctx'>` — i.e. a *non-value* region-env
weakening lemma carrying e2 from `R` to `R'`.

Three candidate formulations were explored in 2026-05-26 sessions:

### III-a — Permutation-aware variant (PROVABLE, LANDED, CLOSES 0/12)

**Statement**:
```coq
Lemma region_shrink_preserves_typing_dup :
  forall R G e T G' r,
    R; G |- e : T -| G' ->
    In r (remove_first r R) ->
    (remove_first r R); G |- e : T -| G'.
```

**Proof**: pure transport via `region_env_perm_typing` — when
`In r (remove_first r R)`, the membership of every region is
preserved. ~15 LOC. Now Qed at `Semantics.v:3332`.

**Why it doesn't close any admit**: the duplicate-r hypothesis
`In r (remove_first r R)` is never available in the touches_region
RIGHT branches. `S_Region_Exit`'s premise (`In r R`) only guarantees
single membership; the dual `In r (remove_first r R)` would require
multi-occurrence, which a well-typed initial program never
produces (`T_Region`'s `~In r R` premise prevents same-name
shadowing throughout reachable configurations).

Lands as adjunct infrastructure: completes the case split alongside
`region_shrink_preserves_typing` and documents the explored
formulation.

### III-b — `no_leaks` invariant as oracle (NOT VIABLE)

`no_leaks` (line 374) proves only a memory-side fact:
`mem_read mu' l = Some (CString r s) -> False`. It says nothing
about whether `e'` is syntactically free of `r`. The bridge that
would make it useful — `step_exit_implies_free_of_exited_region` —
is **false** for congruence cases (the surviving sibling's
references to r break the freedom claim, as documented above at
"step_exit_implies_free_of_exited_region would be false").
Re-engineering `no_leaks` to produce expression-side freedom would
require strengthening its conclusion from "memory free of r" to
"resulting expression syntactically free of r" — a different
judgement entirely, equivalent in effort to the auxiliary lemma
itself. III-b collapses to III-a / Option 2.

### III-c — Restated preservation with membership-equivalence (WRONG AXIS)

Weakening preservation's conclusion to `exists R'', (forall r, In r R''
<-> In r R') /\ R''; G |- e' : T -| G'` does not help: 11 of the 12
open goals are blocked on **G-context** Skolem alignment (already
solved by the Swarm-C `step_output_context_eq` splice), and the
12th wants genuine *weakening* (`r :: R'`), not membership-
equivalence. III-c diagnoses the wrong axis.

### Conclusion

The 12 admits do **not** dissolve under a clean lemma-level fix.
They require one of:

1. **Mutual induction** with `preservation` and `step_preserves_type`
   simultaneously (Option 1 above — the standard textbook approach
   for region calculi, but a significant restructuring).
2. **Inversion-on-Hstep structural recursion** (~150 LOC, Option 2
   above) — orthogonal to the current case split; closes the single
   `step_preserves_type_at_pre` admit at the source, which cascades
   to the corresponding preservation admit.
3. **Type-system change**: add a sibling-region-disjointness side
   condition to `T_Let`, `T_App`, etc. — ensures every well-typed
   compound rules out the bad configuration where exit-able r is
   shared with a sibling. Requires re-proving every existing lemma
   under the new typing rule.

Recommend Option 2 (~150 LOC, scope-isolated) over Option 1
(refactor entire proof). Type-system change (Option 3) is the
"correct" fix for the underlying concrete-name encoding gap, but
the cost (re-prove every lemma) is high.

## Unwind checklist (when finally closed)

1. Replace `Admitted.` with `Qed.`
2. Flip `ROADMAP.adoc`'s admitted-proofs counter `1 → 0`
3. Flip `PROOF-NEEDS.md`'s status row + delete the "what needs
   proving" item for `preservation`
4. Delete this file
5. Update `RUST-SPARK-STANCE.adoc`'s E1 row from OWED to DISCHARGED
   (and remove the "honest gap" entry about preservation)
6. Delete the proof-status comment block at `Semantics.v` immediately
   below the (now-`Qed.`) preservation
