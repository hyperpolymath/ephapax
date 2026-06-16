<!-- SPDX-License-Identifier: MPL-2.0 -->
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
