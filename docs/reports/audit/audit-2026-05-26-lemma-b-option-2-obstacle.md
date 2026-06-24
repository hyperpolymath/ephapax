<!--
  🛑 ARCHAEOLOGY DOCUMENT — preserved for the pathway-to-counterexample record.

  This audit was written 2026-05-26 BEFORE the verified Coq counterexample
  (formal/Counterexample.v, 5 Qed) showed that the preservation theorem
  it attempts to close is provably false.

  Its conclusions / closure plans / "just one more lemma" framings are
  pre-discovery. DO NOT apply them to current proof work.

  The post-discovery doctrine lives at:
    - STATUS.adoc (past / present / future map)
    - formal/PRESERVATION-DESIGN.md (four-layer architecture)
    - PROOF-NEEDS.md (per-sublanguage proof debt)
    - CLAUDE.md (owner directive 2026-05-27)

  This file is preserved because the audit text DOCUMENTS the obstacle
  that led to the counterexample discovery — useful historical record,
  not instructions.
-->

<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Audit Report: ephapax — 2026-05-26 — Lemma B Phase 2 Option 2 obstacle

## Classification: Proof closure analysis, follow-up to `audit-2026-05-26-standards-134-reconciliation.md`

---

## TL;DR

Pre-flight analysis of `formal/PRESERVATION-HANDOFF.md`'s Option 2
("inversion on Hstep with structural recursion, ~150 LOC") for the
shared S_Region_Step admit found a real obstacle in the
sibling-preserving congruence cases. The counterexample is:

```coq
e  = ELet (ERegion r v_inner) e2          (* well-typed at R with In r R *)
e' = ELet v_inner e2                       (* after S_Let_Step / S_Region_Exit *)
R' = remove_first r R                      (* r exited from inside *)
```

`e2` may syntactically reference `r` and was typed at `R` (which had `r`).
After the step, `R'` has no `r`. For preservation we need `e'` typed at
`R'`, but `e2`'s `r`-references prevent that.

The handoff doc anticipated this for the `expr_free_of_region` extraction
path ("a `step_exit_implies_free_of_exited_region` lemma would be FALSE
for congruence cases"). However, the doc's Option 2 (structural recursion
on `Hstep`) was framed as orthogonal to the freedom-extraction path. On
closer inspection, the same counterexample blocks Option 2's congruence
cases — they need to *rebuild* `e'`'s typing at `R'`, and that rebuild
requires `e2` to typecheck at `R'`, which `e2`'s `r`-references prevent.

## Verification of the counterexample

`T_Let` (`formal/Typing.v:103`) has no `~In r (free_regions T)` or
`expr_free_of_region` premise on the bound expression's environment:

```coq
| T_Let : forall R G G' G'' e1 e2 T1 T2,
    R; G |- e1 : T1 -| G' ->
    R; ctx_extend G' T1 |- e2 : T2 -| (T1, true) :: G'' ->
    R; G |- ELet e1 e2 : T2 -| G''
```

So `ELet (ERegion r v_inner) e2` with `e2` referencing `r` is well-typed
at any `R` with `In r R`. `S_Region_Exit`
(`formal/Semantics.v:216-221`) has `expr_free_of_region r v` only on the
value being lifted out — not on siblings.

The step rule `S_Let_Step` (`formal/Semantics.v` similar pattern) likewise
has no freedom-on-siblings premise.

So the counterexample is syntactically and semantically constructible
within the language as defined.

## Implication for the three resolution paths

| Path | Original assessment | After this audit |
|------|---------------------|------------------|
| 1. Simultaneous mutual induction w/ preservation | "significant restructuring touching both proofs" | Still the most robust; carries the cost of touching `step_preserves_type` + `step_output_context_eq` + `preservation` together |
| 2. Inversion + structural recursion on `Hstep` (~150 LOC) | "orthogonal to the current case split" | **Blocked** — congruence cases need to rebuild typings whose siblings may reference the exited region |
| 3. Type-preservation-under-step sub-lemma | Already implemented as `step_preserves_type`; it has the same admit | Same blocker — not a new path |

Two further options the handoff doc didn't enumerate:

| Path | Description | Cost |
|------|-------------|------|
| 4. Add typing invariant for siblings | E.g., extend `T_Let` (and other compound-typing rules) with `~In r (free_regions e2)` whenever the bound expression is region-exiting | Language change; would invalidate prior typed programs; potentially affects every congruence rule |
| 5. Add `expr_free_of_region` premises to `S_*_Step` rules | Make sibling-freedom a step precondition rather than a typing precondition | Language change at the step level; cleaner than (4) but still language-altering |

## Recommendation

Take Path 1 (mutual induction). Path 2's `~150 LOC` estimate was
keyed off the freedom-extraction worry alone; the actual obstacle is
more structural and the structural recursion cannot work in isolation
without one of paths 4/5 (which are language changes).

Path 1's structure:

```coq
Section Preservation.

  Lemma step_preserves_type : ...   (* with mutual IH *)
  with step_output_context_eq : ... (* aka Lemma B *)
  with preservation : ...

  Proof.
    (* simultaneous induction on Hstep, sharing congruence-case
       reconstruction across all three theorems *)
  Qed Qed Qed.

End Preservation.
```

Realistic wall-clock estimate revision (relative to the
2026-05-26 `4-6h` figure from `audit-2026-05-26-standards-134-reconciliation.md`):

- **Path 1 (mutual induction)**: 8-12 hours wall-clock. The
  restructuring is invasive but each of the three lemmas already has
  its cases mostly closed — the merge is mostly bookkeeping +
  shared-IH plumbing.
- **Path 4 or 5 (language change)**: 12-20 hours. Language change
  cascades through `Typing.v`, possibly `Syntax.v`, every backend's
  AST handler, plus re-verification of all previously-closed typing
  invariants. Outside the standards#134 scope.

## What this DOES NOT change

- The 4/5 sub-tasks of standards#134 that closed pre-2026-05-26
  remain closed (Idris2 partials, ABI seam, stance doc — all
  unaffected).
- The 12 cascading goals in `preservation` still depend on Lemma B
  closing; they're not independently hard.
- The case-count revision in `formal/PRESERVATION-HANDOFF.md` (1+1+12
  open obligations, with 1 mirrored structural admit as the
  independent variable) remains correct.

## Action

`lemma-b-phase2` branch retains the worktree + the two doc commits
(audit reconciliation + handoff case-count correction). This audit
adds a third doc commit; no proof code committed in this session
because the chosen path (Option 2) does not work and Option 1 needs
its own focused multi-hour session.
