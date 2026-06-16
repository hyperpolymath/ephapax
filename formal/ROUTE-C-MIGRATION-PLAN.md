<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Route C — count-map carrier migration plan (to close ADMIT 1)

**🛑 SUPERSEDED 2026-06-16 — DO NOT EXECUTE.** The Phase-1 gate proved ADMIT 1
(`region_shrink_preserves_typing_l1_gen_m`) is **FALSE as stated** (machine-checked
counterexample: `ERegion r (ERegion r EUnit)` consumes two ambient `r`s yet is
`expr_strictly_free_of_region r`; types at `[r;r]->[]` but not at `[r]`). No carrier
change can prove a false lemma, so route C is the wrong target. The honest fix is to
**restate region_shrink with the `expr_no_exit_of_region r e` guard** (vacates the
shadowed case) — closes ADMIT 1 on the existing list carrier, no migration, and
unifies with ADMIT 2. This document is retained only as the record of the
(now-moot) migration design + the A′ decouple analysis.

**Status: DRAFT for owner approval. No core edits made. 2026-06-16.**

## Why this, and why nothing cheaper

ADMIT 1 = the single `T_Region_Active_L1` *shadowed* sub-case (`rr = r`) of
`region_shrink_preserves_typing_l1_gen_m` (`Semantics_L1.v:576`). Closing it on
the **list** carrier is now proven impossible by any reorder/permutation/insertion
lemma: `T_Case_L1`/`T_If_L1` (`TypingL1.v:268-269`/`282-283`) require both branches
to land on the *same* output env, and `remove_first_L1`'s first-occurrence
semantics do not commute with reordering (`remove-first ∘ reorder ≠ reorder ∘
remove-first`). The count-map carrier removes "first occurrence" entirely — the
env is a function `region_name → nat` reasoned up to pointwise equality
`renv_eq`, so order is definitionally irrelevant. Stage 1 (`RegionEnvL1.v`,
committed `b283c3b`, axiom-free) already built the carrier + the keystone
`enter_exit_id : cntL1 r R >= 1 -> enterL1 r (exitL1 r R) =R= R`.

## Scope / blast radius (honest)

The L1 judgment `has_type_l1` is one inductive definition; changing its region-env
type is atomic — every downstream user breaks until fixed. References to the L1
region env / `TFunEff`:

| File | refs | role |
|---|---|---|
| `TypingL1.v` | judgment + ~33 rules | the definition; `_Eff` decouple lives here |
| `Semantics_L1.v` | ~42 | all L1 metatheory; ADMIT 1 closes here; bulk of the work |
| `TypingL2.v` | ~28 | L2 modality layer built on `has_type_l1` |
| `Counterexample_L2.v` | ~9 | L2 counterexamples; `eapply T_Lam_L1_Affine_Eff` |
| `Counterexample_L2_nested.v` | ~20 | ditto |

**Legacy stays untouched.** `Typing.v` / `Semantics.v` keep the list carrier
(`region_env := list region_name`, `Syntax.v:867`); `Counterexample.v` depends on
legacy falsity. The shared `ty` (and therefore `TFunEff`, used by legacy) is
**not** changed — which is exactly why the `_Eff` footprint must be decoupled
(below). This is a multi-session migration that may uncover lemmas that do not
translate; the phased sequence is designed to surface that early.

## Carrier & ops (Stage 1, done)

`region_env_l1 := region_name -> nat` (re-entry depth; 0 = dead), with
`renv_eq R1 R2 := forall r, R1 r = R2 r` (setoid, axiom-free). Ops: `cntL1`,
`liveL1` (`R r >= 1`), `enterL1` (increment), `exitL1` (saturating decrement),
`emptyL1`. Proper instances for all ops already proved.

## The NEW keystone needed: `Proper`-on-judgment

The migration's load-bearing addition is a congruence instance:

```coq
#[global] Instance has_type_l1_Proper :
  Proper (eq ==> renv_eq ==> eq ==> eq ==> eq ==> renv_eq ==> eq ==> iff)
         has_type_l1.
```

i.e. `renv_eq`-equal input/output envs are interchangeable in the judgment. This
is what lets the shadowed case rewrite `enterL1 r (exitL1 r R) =R= R` (the
keystone) *inside* a typing goal. It is proved by induction on the derivation,
using the op-level Proper instances — and it is **only sound because every rule
uses `liveL1`/`enterL1`/`exitL1` (which respect `renv_eq`) and never inspects
list structure.** Establishing this is the heart of Phase 2.

## Rule translation table (list → count-map)

| List | Count-map |
|---|---|
| `In r R` | `liveL1 R r` |
| `~ In r R` | `~ liveL1 R r` (i.e. `R r = 0`) |
| `r :: R` (push) | `enterL1 r R` |
| `remove_first_L1 r R` (pop) | `exitL1 r R` |
| `R = R'` (Leibniz) | `R =R= R'` (setoid) |
| `[]` | `emptyL1` |

## The A′ #18 decouple (the one real design decision)

`T_Lam_L1_Linear_Eff` / `_Affine_Eff` currently reuse `R_in`/`R_out` as **both**
the body judgment env **and** the `TFunEff` type annotation (`list region_name`,
in the shared `ty`). Migration splits the two roles:

```coq
| T_Lam_L1_Linear_Eff :
    forall R G T1 T2 e (Renv_in Renv_out : region_env_l1)
                       (Fin Fout : list region_name),
      (forall r, liveL1 R r -> liveL1 Renv_in r) ->
      Renv_in ; ctx_extend G T1 |=L1[Linear] e : T2 -| Renv_out ; (T1, true) :: G ->
      (forall r, In r Fin  <-> liveL1 Renv_in  r) ->   (* bridge: footprint = live-set *)
      (forall r, In r Fout <-> liveL1 Renv_out r) ->
      R ; G |=L1[Linear] ELam T1 e : TFunEff T1 T2 Fin Fout -| R ; G
```

- The judgment env is the count-map `Renv_*`; the `TFunEff` annotation keeps its
  `list` footprints `F*` (so `ty` is unchanged and legacy is untouched).
- The bridge is **relational** (`In r F <-> liveL1 R r`), *not* a `support`
  function — `region_name -> nat` is a total function with no computable finite
  support, so it cannot be enumerated to a list without a finiteness witness.
- **Cost at the L2 call sites:** the ~6 `eapply T_Lam_L1_Affine_Eff` in
  `Counterexample_L2*.v` must now discharge the two bridge premises. At those
  sites the envs are concrete (built from `emptyL1` by `enterL1`), so each bridge
  is provable by `unfold`/decision — but it is real per-site work.

## Phased sequence (fail-fast)

**Phase 1 — proof-of-concept (CHEAP, the go/no-go gate, ~100 lines, additive
scratch).** Before touching the real judgment, build a *mini* judgment on the
count-map carrier with only: the atomic rules, one sequencing rule, `T_Case`
(the join), and the four region rules. Prove the `has_type_l1_Proper` analogue
and the **shadowed region_shrink case** via `enter_exit_id`. This definitively
answers "does the count-map carrier actually close the shadowed case, and does
the `Proper` instance go through, and does `T_Case`'s join survive on the new
carrier?" at 3% of the cost. **If Phase 1 does not close cleanly, abort route C.**

**Phase 2 — migrate `TypingL1.v`.** Translate the judgment env type + all ~33
rules per the table; apply the `_Eff` decouple; add `has_type_l1_Proper`. Green
when `TypingL1.v` compiles.

**Phase 3 — migrate `Semantics_L1.v` (the bulk).** Translate all ~42 lemmas;
**close ADMIT 1** at the shadowed case (active sub-case via `Proper`+commutation;
cnt=1 corner via `enter_exit_id` switching to the fresh rule); keep admits 2/3/4
admitted (translated). Watch for list-structural inductions on `R` (must become
derivation inductions or use a finiteness witness) — flag any lemma that
enumerates `R`. Green when `Semantics_L1.v` compiles with admit count 4→3.

**Phase 4 — migrate `TypingL2.v` + `Counterexample_L2*.v`.** Thread the new env
type; discharge the `_Eff` bridge premises at each counterexample call site.

**Phase 5 — audit.** Full `make` from clean; `Print Assumptions` on
`region_shrink_preserves_typing_l1_gen_m` (and the L2 counterexamples) = "Closed
under the global context"; confirm honest admit count 4→3 and zero new axioms.

## How ADMIT 1 closes (the shadowed case)

`ERegion r e`, shrinking `r`, `e` strictly-free-of-`r`. With the count-map env,
`e` preserves `cnt r` (no exit of `r`), so:
- **cnt r R ≥ 2:** `r` still live after the shrink → rebuild via
  `T_Region_Active_L1`; the output equality is now a `renv_eq` fact
  (`exitL1` commutation), discharged by `Proper`.
- **cnt r R = 1:** after the shrink `r` is fresh → rebuild via `T_Region_L1`
  (fresh); `enter_exit_id` gives `enterL1 r (exitL1 r R) =R= R`, so the body
  re-types and the output matches up to `renv_eq`. This is the exact corner the
  list carrier could not express.

## Risk register / abort criteria

1. **Phase 1 fails** (shadowed case or `Proper` or `T_Case` join doesn't close on
   the mini-model) → **abort route C**, defer ADMIT 1. *Cheap to discover.*
2. **A Semantics_L1 lemma enumerates `R` as a list** (structural induction on the
   env) → needs a finiteness-witness refactor or a finite-map carrier instead of
   the total-function carrier; flag to owner, may re-scope Stage 1.
3. **An existing Qed lemma does not translate** → stop, surface; do not admit-shuffle.
4. **L2 bridge premises not dischargeable** at some counterexample site → stop,
   surface (would indicate the set-bridge loses needed footprint information).

## Owner sign-off needed before execution

- **Approve the `_Eff` decouple shape** (relational set-bridge `In r F <-> liveL1 R r`).
- **Approve big-bang vs branch-isolated** (recommend: dedicated branch off
  `proofs/l1-region-countmap-setoid`, build red until Phase 4, never merged until
  Phase 5 is green).
- **Net result:** honest admit count **4 → 3** (ADMIT 1 closed; 2/3/4 remain;
  legacy `preservation` untouched). Effort: multi-session.

**Recommended immediate next step:** execute **Phase 1 only** (additive scratch,
~100 lines, reversible) as the go/no-go gate. Report, then decide on Phases 2-5.
