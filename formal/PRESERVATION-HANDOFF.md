<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Hand-off: closing `preservation` in `formal/Semantics.v`

Diagnostic written 2026-05-20 alongside the `Qed.` → `Admitted.`
honesty fix (ephapax#92). Whoever picks this up next: read this file
first; it tells you exactly what's open and why the existing proof
script does not close it.

## How this hand-off was produced

The proof script ends at `Semantics.v` L3326. Replace the `Admitted.`
on L3327 with:

```coq
    end).
Show.
Show Existentials.
Admitted.
```

Then:

```sh
cd formal
coq_makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
```

`coqc` prints the goal count + every open existential. Restore the
`Admitted.` afterwards.

## What's actually open

**910 goals** — exactly **35 (step rules) × 26 (typing rules)**, i.e.
the *full combinatorial after `induction Hstep; inversion Htype;
subst;`*. The chain of `try solve [...]` tactics in
`Semantics.v` L3228–L3326 closes **zero** of them.

The in-file comment block at L3269–L3296 says

> Only ONE case remains open: S_Region_Step + T_Region_Active.

That was true (or thought to be true) at one earlier moment of the
proof development; it is **not true now**. Either:

- the proof script regressed silently after the comment was written
  (no CI gate caught it because the Coq job has been failing for ≥3
  runs — see ephapax#92), **or**
- the comment was always optimistic about how many `try solve`
  branches actually fired.

Either way: **the proof closes nothing as it stands; the goal is to
write tactics that close the full 35 × 26 case split**, not just the
single S_Region_Step case the comment names.

## Why the existing `try solve` chain fails

The current shape is:

```coq
induction Hstep; intros G0 T0 G0' Htype;
  try (remember ... as e_orig eqn:He_orig);
  inversion Htype; subst;
  try solve [eexists; econstructor; eassumption];
  try solve [eexists; eassumption];
  try solve [eapply subst_preserves_typing; eassumption];
  try solve [exfalso; eapply values_dont_step; eassumption];
  try solve [exfalso; congruence];
  try solve [exfalso; discriminate];
  try solve [exfalso; ...inversion (EVar steps)...];
  ...
```

The `try solve` blocks are applied to *all* `inversion Htype`
subgoals. They fall into two outcomes:

1. **Diagonal cases** (step rule and typing rule are about the same
   expression head — e.g. `S_App_Fun` + `T_App`): need real
   reconstruction. The `try solve [eexists; econstructor;
   eassumption]` aims at these but `eassumption` rarely matches —
   typically the IH gives `R'; G |- body : T -| G_out` for some `G_out`
   but the reconstructor needs a fresh witness for the *step-result*
   expression. **Not closing.**

2. **Cross-cases** (step rule fires on one expression, typing rule
   inverts to a different head — ~33/35 of each step rule's
   cross-cases): should close as `exfalso` via `discriminate` /
   `congruence` on the typing-rule equation. But after `inversion
   Htype; subst`, the substitution direction can eliminate the
   step-side expression variable before the discriminating equation is
   in scope. The `remember ... as e_orig eqn:He_orig` was intended to
   pin the form, but it sits inside `try (...)` and only fires when
   the pattern matches; for many cross-cases it does not fire, and
   the chain falls through to `try solve [exfalso; congruence]` which
   then has no equation to discriminate on. **Not closing.**

Both cases need surgery on the script, not "one more tactic".

## What it would take to close

A realistic plan:

1. **Move the `remember` out of `try (...)`** — it should always fire.
   Use a less fragile pattern (e.g. `set (e_orig := e) in *` before
   `inversion`).

2. **Rewrite cross-case closure** to use an explicit `inversion
   Htype` arm-by-arm rather than `inversion Htype; subst; try solve
   [exfalso; ...]`. The arm-by-arm form lets you control the subst
   direction. Coq 8.18's `inv` tactic from `Coq.Program.Tactics` or
   `dependent destruction` can help.

3. **Write per-step-rule diagonal proofs**. For each of the 35 step
   rules, the diagonal typing rule case needs its own tactic block.
   The supporting lemmas already exist:
   - `subst_preserves_typing` (`Typing.v` Qed)
   - `region_env_perm_typing` (`Semantics.v` Qed, this proof's L~3100)
   - `region_add_typing` (`Semantics.v` Qed, this proof's L~3120)
   - `region_shrink_preserves_typing` (`Semantics.v` Qed, this
     proof's L~3150)
   - `values_dont_step` (`Semantics.v` Qed earlier in the file)

   The diagonal-case glue is the missing piece for each of the 35
   step rules. The author's comment block at L3269–L3296 has the
   right shape for `S_Region_Step + T_Region_Active`; analogous
   blocks are needed for the other 34.

4. **`S_Region_Step + T_Region_Active`** (the comment's named case):
   the proposed `apply T_Region + region_add_typing` to weaken `R'`
   to `r :: R'` is **not obviously valid without extra invariants on
   `e'`** — see the comment's own warning at L3281–L3284. This case
   may need a *region-env weakening lemma for non-values* which does
   not yet exist. Writing that lemma is a separable piece of work,
   probably 50–150 lines.

5. **Estimated effort**: not "one more tactic." A full close is on
   the order of **days–weeks of proof engineering**, depending on
   whether the region-env weakening lemma turns out to need
   additional language invariants. The 34 non-region-related diagonal
   cases are probably 1–2 days; the region-related ones are the hard
   part.

## What is not a fix

- Adding more `try solve [...]` lines to the existing chain. The
  problem isn't a missing single tactic — it's that the *structure*
  of the proof script is wrong for the cross-case discharge.
- Replacing `induction Hstep` with `inversion Hstep` — that loses
  the inductive hypotheses needed for the diagonal cases (e.g.
  `S_Region_Step` recurses on inner step).
- Mass-`Admitted.` per case — defeats the point and conflicts with
  the estate's "build is the only oracle" policy. The honest mark is
  one `Admitted.` on `preservation`, not 35.

## What to do until it's closed

The PR ephapax#92 (this branch) marks `preservation` as `Admitted.`
so the file builds. ROADMAP + PROOF-NEEDS reflect the honest state.
The Coq CI job will then go green. **This file remains as the precise
diagnosis** so the next session does not have to re-derive what is
open.

Once `preservation` is honestly closed:

1. Replace `Admitted.` with `Qed.`
2. Flip ROADMAP's admitted-proofs counter `1 → 0`
3. Flip PROOF-NEEDS' status row + delete the "what needs proving"
   item for `preservation`
4. Delete this file
5. Update `RUST-SPARK-STANCE.adoc`'s E1 row from OWED to DISCHARGED
   (and remove the "honest gap" entry about preservation)
6. Delete the comment block at `Semantics.v` L3328–L3336 (its
   contents will be obsolete)
