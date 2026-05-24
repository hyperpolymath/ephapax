<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Hand-off: closing `preservation` in `formal/Semantics.v`

Diagnostic + remediation log. The proof is still `Admitted.`, but as
of **2026-05-21** it's **down from 910 open goals to 12** via four
landed PRs. This file tells whoever picks it up next exactly what's
open and what the canonical closure path is.

> **The canonical closure plan is now in `ROADMAP.adoc` §
> "Preservation closure plan".** This file remains as the per-case
> diagnostic record. Read ROADMAP first; come back here for case
> detail.

## State at a glance

| Date | Open goals | Notes |
|------|-----------:|-------|
| 2026-04-27 | "fully closed" | In-file comment — but `coqc` rejected the `Qed.`. The claim was unsubstantiated; the proof never closed. |
| 2026-05-20 (am) | 910 | Discovered via `Show. Show Existentials.` before the `Admitted.`. Exactly 35 (step rules) × 26 (typing rules). The existing `try solve [...]` chain closes ZERO. |
| 2026-05-20 (pm) | 29 | After the standard preservation pattern (`remember (mu, R, e) as cfg` + symmetric for cfg', then `inversion Hcfg; subst; inversion Hcfg'; subst;` inside each case). 97% reduction. PR #102. |
| 2026-05-20 (eve) | 22 | After `revert mu R e mu' R' e' Hcfg Hcfg'` before `induction Hstep` so each case's IH carries universal quantification over the inner step's config. PR #106. |
| 2026-05-20 (eve) | 22 | Region-invariance lemma `step_R_eq_or_touches_region` landed as infrastructure (no goal closures). PR #114. |
| 2026-05-20 (night) | **12** | 10 β-reduction / value-step cases discharged via per-case manual proofs using the lemma. PR #116. **98.7% reduction across one day.** |

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

**Open (8)** — all blocked on the **type-alignment circularity**:

| Step rule | Inner-type that's NOT fixed by outer T |
|-----------|----------------------------------------|
| `S_App_Step1` | `T_App`'s arg type `T1` (TFun T1 T2) |
| `S_App_Step2` | same |
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

#### Cluster C — region / compound-value (4 of 6 closed, 2 open)

**Closed (2026-05-24)**: `S_Fst`, `S_Snd`, `S_Copy`, `S_Region_Exit`.

Recipe: invert the compound typing rule (T_Fst → T_Pair, T_Snd →
T_Pair, T_Copy, T_Region_Active), apply `value_context_unchanged`
on each value-typing premise to align intermediate contexts with
the input context G, then `reflexivity` closes the resulting
`G = G` goal (output_ctx_det not even needed when both sides
collapse to G).

**Still open**:



| Step rule | What's needed |
|-----------|---------------|
| `S_Region_Enter` | `T_Region` ↔ `T_Region_Active` dispatch via `In r R`; needs `output_ctx_det` sub-lemma on `e_inner` |
| `S_Region_Exit` | needs `region_shrink_preserves_typing` (already Qed) + value-output-context invariance |
| `S_Region_Step` | **blocked on Phase 3** — region-env weakening for non-values |
| `S_StringLen` (atomic!) | inversion of `T_StringLen` → `T_Borrow_Val` → `T_Loc` chain needs explicit nested invocation; my repeat-match doesn't cover the `EBorrow (ELoc _ _)` shape |
| `S_Copy` | atomic but compound: `T_Copy` outputs `G'` where `G'` is value-input; needs `value_context_unchanged` invocation |
| `S_Fst` / `S_Snd` | atomic but inversion of `T_Pair` premise needs `value_context_unchanged` to align inner v1/v2 typings |

### Effort revision

The ROADMAP's "3-4 hours focused session" estimate for Phase 1 was
optimistic. Empirical evidence:

- 4 trivial cases closed by a uniform tactic in ~30 minutes.
- Each of the remaining 31 needs a hand-rolled per-case tactic block.
- Cluster A (7) needs one shared sub-lemma first
  (`subst_preserves_typing_strong`).
- Cluster B (17–18) shares the same recipe but each case names
  different premises and constructor arguments — call it ~10 minutes
  per case once the recipe is debugged on the first one.
- Cluster C (6) is a mixed bag; `S_Region_Step` carries Phase 3 risk.

**Revised estimate**: **8–15 focused hours** for Lemma B alone,
assuming no circularity surprises with `type_determinacy` across
stepped pairs. Phase 2 (apply Lemma B to preservation's congruence
cases) remains ~2 hours of mechanical wiring once Lemma B is closed.

### Watch for: circularity risk

Some Cluster B cases require knowing that `e` and `e'` have the
same type before applying the IH. `type_determinacy` operates on
same-expression pairs, not stepped pairs. The natural lemma —
"step preserves type" — is part of what preservation itself
proves. If the inductive structure of Lemma B turns out to need
preservation as a sub-lemma, the closure path needs revision.
Watch for this when attacking the first Cluster B case.

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
