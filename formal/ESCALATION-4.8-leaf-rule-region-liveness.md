<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Escalation: the §4.8 leaf-rule region-liveness decision (owner call)

**Status:** OPEN — needs an owner design decision before any further L1
preservation proof work. Raised 2026-06-16.

**Why this is an escalation and not a patch.** `CLAUDE.md` →
*Anti-pattern detector* lists "strengthened lemma signatures within the
current judgment shape" and "sibling-region-disjointness side conditions"
as **stop-and-escalate** triggers, and *DO #4* says "escalate before
patching." The fix below is exactly a leaf-rule strengthening of the
**surface typing judgment**, so it changes what programs ephapax accepts.
That is a language-design choice, not a proof trick — it is yours to make.

## The finding (ground-truthed with `coqc 8.18.0`, `Print Assumptions`)

The L1 development on `main` is green with **one** surfacing axiom
(`region_liveness_at_split_l1_gen`). The real open admits are four, all in
`formal/Semantics_L1.v`, and **all four collapse to one decision**:

| Lemma | Line | Internal admits | Nature |
|---|---|---|---|
| `region_shrink_preserves_typing_l1_gen_m` | :441 (Admitted :678) | 2 (:576, :646) | shadowed `rr = r` case of `T_Region_Active_L1{,_Echo}` |
| `region_liveness_at_split_l1_gen` | :1942 (Admitted :2028) | 2 (:1994, :2014) | **FALSE as stated** (see below) |
| `step_pop_disjoint_from_type_l1` | :3178 (Admitted :3433) | ~9 | inner step pops a region free in the sibling/outer type |
| `preservation_l1` | :3439 (Admitted :3452) | 1 outer (whole body deferred) | capstone, derivative of the three above |

Inventory corrections (verified): `subst_preserves_typing_l1` (:3067) is
`Qed`, **not** admitted. `TypingL2.v` has **zero** admits/axioms.
`preservation_l3` (:3568) is `Qed`, conditional only on
`region_shrink_preserves_typing_l1_gen_m`. So the opportunistic
honestly-closable wins are **already taken** — there is nothing for me to
close without the decision below.

### `region_liveness_at_split_l1_gen` is false as written

Statement: `In rv R -> In rv R'` after `R ; G |=L1[m] e : T -| R' ; G'`.
Counterexample in the source: `ERegion rv (EI32 5)` at `R = [rv]` — the
`T_Region_Active_L1` rule pops the only `rv`, so `rv ∈ R` but `rv ∉ R'`.
No tactic closes a false statement; the *judgment* must change.

## The single decision

**PRESERVATION-DESIGN.md §4.8, path (3): strengthen the leaf rules**
`T_Var_Lin_L1`, `T_Var_Unr_L1`, `T_Loc_L1` (and the `TString r` consumers
`T_StringConcat_L1` / `T_Drop_L1`) with the formation premise:

```
  In r (free_regions T) -> In r R
```

i.e. "a value whose type mentions region `r` can only be used where `r` is
live." This makes *region-liveness of a typed value* a **derivable
invariant of the judgment** rather than a side condition stated per
compound rule. Consequences, in order:

1. `region_liveness_at_split_l1_gen` becomes provable (the `T_Region_Active`
   `r = rv` case is now vacuous: a body whose *type* references `rv` cannot
   have popped `rv`).
2. `step_pop_disjoint_from_type_l1`'s ~9 hard cases discharge by structural
   induction (the missing inner-typing premise is now present at the
   variable/loc leaves).
3. `region_shrink_preserves_typing_l1_gen_m`'s shadowed case closes via the
   commutation already proved for the descend case.
4. `preservation_l1` is re-derived as the capstone (shape drafted in
   PRESERVATION-DESIGN.md §4.5).

Path (1) — effect-typed `TFunEff` lambdas — is **already in the codebase**
and additionally closes the `S_App_Step2` case; (3) is the complementary
leaf-rule half. They are one coherent layer-design change, not three.

## What the owner is actually choosing

This is **not** free. The premise `In r (free_regions T) -> In r R` is a
real restriction on the *surface language*: it rejects programs that hold a
value typed against a region that is no longer live. That is almost
certainly the intended discipline (it is the linear/region story ephapax is
built on), but it is a **semantics decision with UX consequences**, so it
needs your sign-off rather than my unilateral edit. Options:

- **(A) Adopt §4.8 path (3) leaf-rule strengthening** (recommended; unifies
  all four admits; matches the four-layer intent). Cost: the surface
  judgment gets stricter; a handful of `TypingL1.v` rules grow a premise and
  every leaf-rule inversion in `Semantics_L1.v` must thread it.
- **(B) Multiset reformulation of `remove_first_L1`** (the in-file option
  (b)). Heavier: loses list ordering, ripples through every
  `remove_first_eq_l1` user. Dispreferred fallback.
- **(C) Leave the four admits as documented L2-β follow-ups.** The build
  stays green-with-one-axiom; L3 stays conditional. No soundness regression,
  but the L1 capstone stays open.

## Off-limits (recorded so no one re-treads it)

`formal/Semantics.v` `Theorem preservation` (:8556, `Admitted` :9258) is the
**provably-false legacy theorem**; `Counterexample.v` depends on its
falsity. Per `CLAUDE.md` *DO NOT 1/2* and
`feedback_ephapax_no_patching_legacy_preservation.md`: never close, never
add helper lemmas toward it. This escalation does **not** touch it.

## Recommendation

Take **(A)**. But because it changes the accepted surface language, I am
not implementing it without your explicit go-ahead. On approval, the work
is: add the premise to the ~5 leaf rules in `TypingL1.v`, re-thread the
leaf-rule inversions, then close the four admits in dependency order
(region_liveness → step_pop → region_shrink → preservation_l1), keeping
`Counterexample.v` and the legacy theorem untouched.
