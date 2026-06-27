<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# The eliminator fork — and whether choreographic typing across time segments closes it

The two admits the tropical re-foundation does **not** dissolve
(`step_pop_disjoint_from_type_l1`, ADMIT 3; `preservation_l1`, ADMIT 4 gated on
it). This note states the challenge precisely, explains why both prior fixes
failed, and assesses the proposal: **type region-liveness choreographically,
across time segments.** Verdict up front: it is the right *shape* — more so than
the grade-in-context patch — but it is unproven and can *relocate* rather than
*close*, so it needs the minimal-counterexample experiment in §5.

## 1. The challenge, precisely

Preservation needs: if `R ; G ⊢ e : T -| R' ; G'` and `(μ,R,e) → (μ',R₂,e')`,
then `R₂ ; G ⊢ e' : T -| … `. It fails on a single shape:

> A **subterm `e_sub` depends on a region `rv`** (its type mentions `rv`, e.g.
> `e_sub : TString rv`), but an **eliminator/context erases `rv` from the
> result type** (`EDrop(·):TUnit`, `Fst`, application, `Let`-body, `Case`-arm),
> and a step **exits `rv`** (`R → R₂`, `rv` gone). Now `e'` still contains
> `e_sub`, which needs `rv` live, but `R₂` no longer has it and `T` never
> showed it.

Minimal Coq-checked witness: `EDrop (EVar j : TString rv)` at `R = [rv]`. It
types; `expr_strictly_free_of_region rv` holds (no syntactic `rv`); the result
type `Unit` satisfies the Tofte–Talpin premise — yet shrinking `rv` leaves the
inner `EVar j` untypable.

**The root is a representational mismatch in *time*.** The judgment expresses
region liveness with:
- a **snapshot** `R` (the live set *at one point*), and
- a **result-type-local** view (`free_regions(T)`),

but the actual obligation is **temporally extended and non-local**: "`rv` must
be live *throughout the evaluation of `e_sub`*". A snapshot cannot say
"throughout"; a result type cannot say "of a subterm whose contribution I
erased". The information needed is *when*, and neither carrier carries time.

## 2. Why both prior fixes failed (the same wall)

- **Leaf-rule strengthening (path 3):** put `free_regions(T) ⊆ R` on `T_Var`.
  This forces liveness *at the variable use site*. But region-shrink/exit
  *wants to remove* `rv` while that very variable is in scope, so the premise
  and `region_shrink` **contradict** — the `EDrop` witness is exactly the
  contradiction. It moves the snapshot demand to the leaf; it does not add time.
- **Effect-typed lambdas (A′):** makes a *lambda's* footprint type-visible.
  Helps only `S_App_Step2`; the witness is a *free variable under an
  eliminator*, no lambda involved. It adds type-visibility for one binder
  shape; it does not add time.

Both stay inside the snapshot+result-type ontology. The wall is that ontology.

## 3. The proposal: liveness as a choreography over time segments

Replace "liveness = membership in a snapshot" with "liveness = a position in a
**global protocol over time segments**", and recover the per-subterm rule by
**projection**. Concretely:

- **Time segments.** A region scope `enter rv … exit rv` *is* a segment: the
  interval during which `rv` is live. Nesting/re-entry gives nested segments
  (depth = the tropical `cnt rv` grade — the two views meet here).
- **Regions as session-typed resources.** Each region is a participant whose
  lifecycle is a session `open → use* → close` (exactly a file-handle/typestate
  protocol). The whole program is the **choreography**: the interleaving of all
  regions' sessions across segments.
- **Local typing = endpoint projection.** A subterm `e_sub` is typed by
  *projecting* the choreography onto `e_sub`'s segment. Its dependency on `rv`
  is satisfied because the projection places `e_sub` *inside* `rv`'s `open…close`
  segment — **not** because `rv` appears in the result type.
- **Preservation = subject reduction for the choreography.** A step advances
  the global type to a coherent global type; the snapshot problem dissolves
  because the global type carries the *temporal* structure the snapshot lacked.

The eliminator's "hidden" dependency is then **not hidden**: the global type
records that `e_sub` runs in `rv`'s segment, even though the local/erased result
type does not. That is precisely the missing *when*.

## 4. Why this is the right shape — and the estate already has both halves

The dependency is temporal-and-global; choreographies are *the* device for
temporal-global protocols projected to local views. This is a structural match,
not an analogy. And it composes with the tropical re-foundation rather than
competing with it:

- `tropical-resource-typing` already ships **`TropicalSessionTypes.lean`**.
  Session types are the *local projections* of a choreography. So region
  liveness becomes a **tropical-graded choreography across time segments**: the
  grade (MinPlus `cnt`) carries the *resource quantity* (re-entry depth), the
  session/choreographic structure carries the *temporal protocol*. One object,
  two readings — the same `echo ≡ tropical ≡ epistemic` unification, now
  extended to include the *order of events*, not just their magnitude.
- Division of labour becomes clean: **tropical grade** closes the structural
  admits (1, 2 — quantity/carrier); **choreography over segments** is aimed at
  the eliminator admit (3 — time). `EchoBridge` already measures L3 residues
  into the grade; a choreography adds the missing temporal axis to the same
  grade.

## 5. The honest risks (why "right shape" ≠ "resolved")

1. **Sequential, not distributed.** Choreographies/session types were built for
   *concurrent* systems with communicating participants. The reinterpretation
   here — *regions* as participants, *scopes* as segments, region
   alloc/use/free as the "communication" — is principled (resource-usage
   protocols / typestate are exactly session-shaped) but **non-standard**; it
   needs a clean foundation, not an off-the-shelf import.
2. **Projection coherence is where the problem could re-appear.** The whole
   method rests on endpoint projection being *coherent* (locals recompose to the
   global). The eliminator case might project to a local type that is itself
   inconsistent — in which case the difficulty is **relocated** to a coherence
   side-condition, not closed. This is the single thing to check first.
3. **Close vs relocate.** Subject reduction for the choreography must genuinely
   *carry* "`rv` live throughout `e_sub`'s segment" through the exit step. If it
   does, ADMIT 3 closes; if the segment boundary and the exit step don't line up
   definitionally, you get a new obligation, not a discharge.
4. **Apparatus cost.** This is a research program (global types, projection,
   coherence, subject reduction for the region choreography), not a refactor —
   high-reward, high-cost. It should not gate the §`L1-REGION-REFOUNDATION-PLAN`
   clean win, which proceeds independently.

## 6. The deciding experiment (cheap, do this before committing)

Do **not** build the general theory first. Formulate the *minimal* choreography
that types just `EDrop (EVar j : TString rv)` over two segments —
`S₁ = [enter rv … (EVar j read) …]`, `S₂ = [exit rv …]` — and ask one question:

> Does the choreography's subject-reduction step for `S_Region_Exit rv`
> transform the global type into a **coherent** global type in which the
> (now-residual) `EVar j` no longer claims `rv`-liveness — *without* a snapshot
> premise?

- **If yes**, the segment carried the *when*, the projection stayed coherent,
  and ADMIT 3 closes choreographically → re-grade `region_liveness` *and*
  `step_pop` against the global type; the capstone follows. (This is the path
  to **0** admits.)
- **If no — i.e. coherence needs an extra side-condition** — the problem has
  *relocated* to that condition. Report it; it is likely the *same* eliminator
  obligation in choreographic clothing, and the honest count stays **2** until a
  different idea (or a restricted language fragment) lands.

Either outcome is decisive and cheap, and tells us whether choreographic typing
*resolves* the eliminator fork or merely *renames* it.

## 7. Verdict

Choreographic typing across time segments is the **best-shaped** candidate for
ADMIT 3 because it is the only proposal that adds the missing axis — *time* —
rather than re-arranging the snapshot. It also unifies cleanly with the tropical
re-foundation via `TropicalSessionTypes` (a tropically-graded choreography:
quantity × order in one structure). It is **not yet a resolution**: it can
relocate the difficulty into projection coherence, and the sequential-language
foundation is non-standard. The §5/§6 experiment is the inexpensive way to
learn which — and it is the recommended next step on the eliminator fork, run in
parallel with (not blocking) the clean-win carrier refactor.

## 8. Result of the §6 experiment (2026 — run in Coq)

The §6 deciding experiment was run against the live judgment. Outcome: the
verdict is the predicted **"no" — it relocates** — but the experiment also
produced a concrete simplification worth keeping.

**(a) `step_pop_disjoint_from_type_l1` reduces from 11 admits to 1.** Driving
the proof by `step_R_change_shape` (every step leaves `R` fixed, prepends a
fresh region, or removes exactly one) makes all ten eliminator/erasing
congruences trivial — a region free in the result type survives unless the
step exits *that exact* region. The 255-line induction with eleven `admit`s
becomes ~15 lines with one. (Landed; `coqc 8.18.0` + `Print Assumptions`
verified; outer `Admitted` count unchanged.)

**(b) The single residual obligation, exactly:** the step exits `r0` while
`r0 ∈ free_regions(T)` ⟹ `cnt r0 R ≥ 2` (i.e. `In r0 (remove_first r0 R)`).
Its **direct-exit** sub-case is *vacuous* — a head redex `ERegion r0 v` is
typed by `T_Region_Active_L1`, whose `~In r0 (free_regions T)` premise
contradicts `r0 ∈ free_regions(T)`. The residue is the **congruence-exit**
case (`ERegion r0` under an eliminator; `r0` from a sibling's type — a
distinct occurrence).

**(c) Why it relocates (the §2 wall, mechanically reconfirmed).** Discharging
the congruence case needs the sibling's `r0` proved a *distinct* occurrence
from the exiting one — exactly the temporal/segment coherence the snapshot
env + result type cannot express. Every closure route tried
(`free_regions ⊆ R_out`, `count_occ_le_l1_m`, linking the dynamic exit to the
static output) collapses to connecting the dynamic step to the static typing
output, which *is* preservation. Circular.

**(d) The §4.8 framing was wrong** and is corrected in the source: the
obstruction is not lambda-rigidity (the witness has no lambda) but
region-count coherence at a region exit. **Net: ADMIT 3 stays open at the
honest count (still 2 outer `Admitted`), but is now ONE minimal, precisely
characterised obligation** — the cleanest possible target for the §3 / §5.1
tropically-graded choreography. That choreographic closure is the
unchanged recommended next step.

## 9. Result of experiment 2 (2026 — `formal/L1ChoreoExperiment2.v`)

Experiment 1 (§5/§6, `L1ChoreoExperiment.v`) returned **"relocates"**, but its
own "honest gaps" §2 recorded *why* and prescribed the next move: it had
**collapsed** the projection onto the scalar predicate
`expr_no_exit_of_region` (discarding subterm-relative order) and had targeted
the **clean** `ERegion rv` exit (already `Qed`) rather than the genuinely-open
**congruence** cases (`S_Let_Step` / `S_App_Step2` / `S_Pair_Step2` /
`S_Case_Step` — *inner pop erased from the outer result type*). Experiment 2
builds the minimal **non-collapsed** apparatus that gap asked for and aims it at
the congruence boundary.

**The model.** One region `rv`'s lifecycle is a `Trace` of events
(`Open`/`Close`/`Use`) *relative to the subterm structure*, run from an initial
balance `k = cnt rv R`. The trace keeps the same open/close balance the scalar
`cnt rv R` keeps — but, unlike a snapshot, it keeps the **order**. `valid k t`
is the local well-nesting condition (a `Close` or `Use` requires balance `>= 1`
at that point).

**The decisive result (all `Qed`, axiom-free — `Print Assumptions` clean).**
The order is exactly enough to separate two configurations the snapshot
*conflates* at the `e1`/`e2` boundary:

- **Internal scope** — the stepping sibling is `rv`-net-neutral
  (`final_balance k t1 = k`): the surviving sibling is coherent at the original
  `k`, independent of `t1`'s internal region activity
  (`congruence_internal_scope_carries`).
- **Escaping close** — the stepping sibling closes an outer `rv` while the
  surviving sibling still uses it: **impossible in a coherent trace**. If the
  surviving sibling's dependence is a `Use` ordered after `t1`, the post-`t1`
  balance is forced `>= 1` (`sibling_use_keeps_region_live`). This is precisely
  the obligation `step_pop_disjoint_from_type_l1` *relocates to*
  (`In rv (free_regions T) -> In rv R -> In rv R'`), and it is proved here as a
  pure structural fact — **non-circularly**, with no appeal to preservation.
  The snapshot cannot state it because it carries only the final balance, not
  the witness that the `Use` is *ordered after* the stepping sibling.

**Verdict.** For the congruence cases — where experiment 1 located the
genuinely-open fork — the non-collapsed trace model **closes** the relocated
obligation *in the model*, and reduces the open question to **one wiring
lemma**: that `has_type_l1` of a congruence redex induces a `valid` trace at
`k = cnt rv R` with the surviving sibling's `rv`-dependence as a trailing
`Use` (`wiring_obligation`, stated honestly, never faked — mirroring
experiment 1's `close_derives_coherence`). Crucially, experiment 1's specific
failure mode (the relocated predicate is *false* at re-entry) **provably does
not recur**: the trace's `valid` is *defined* to permit re-entry (nested
`Open`/`Close`, balance `> 1`). So the verdict for the congruence boundary is
upgraded from **"relocates"** to **"closes in the trace model, reduced to one
wiring lemma"**, and the wiring lemma is named as the precise next target.

This experiment closes **no** admit and adds **no** axiom (honest count
unchanged); it is the consolidation+sharpening step, not the closure. The
remaining gate to an actual ADMIT-3 closure is `wiring_obligation` — extract a
`valid` trace from a typing derivation — which, unlike experiment 1's dead end,
is plausibly a *structural induction* on the typing derivation (each `Close` /
`Use` event's `>= 1` premise mirrors a local `In r R` premise in
`T_Region_Active_L1` / `T_Loc_L1`), not a preservation-strength obligation.
