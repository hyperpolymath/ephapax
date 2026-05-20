<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Hand-off: closing `preservation` in `formal/Semantics.v`

Diagnostic + remediation log. The proof is still `Admitted.`, but as of
2026-05-20 it's **down from 910 open goals to ~29 real ones** via the
standard preservation pattern. This file tells whoever picks it up
next exactly what's open and why.

## State at a glance

| Date | Open goals | Notes |
|------|-----------:|-------|
| 2026-04-27 | "fully closed" | In-file comment — but `coqc` rejected the `Qed.`. The claim was unsubstantiated; the proof never closed. |
| 2026-05-20 (am) | 910 | Discovered via `Show. Show Existentials.` before the `Admitted.`. Exactly 35 (step rules) × 26 (typing rules). The existing `try solve [...]` chain closes ZERO. |
| 2026-05-20 (pm) | **29** | After the standard preservation pattern (`remember (mu, R, e) as cfg` + symmetric for cfg', then `inversion Hcfg; subst; inversion Hcfg'; subst;` inside each case). 97% reduction. |

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
