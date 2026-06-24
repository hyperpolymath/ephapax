<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Deciding experiment — does subject reduction carry region-liveness through a region exit?

**Status: RUN. Verdict: RELOCATES (not "carries coherently").** 2026-06-16.

This is the cheap, decisive experiment that
[`L1-ELIMINATOR-FORK.md`](./L1-ELIMINATOR-FORK.md) §5/§6 flagged as the
single thing to run before committing to the choreographic-foundational
route. Machine-checked skeleton:
[`L1ChoreoExperiment.v`](./L1ChoreoExperiment.v) (5 Qed lemmas, axiom-free,
in the build; closes no admit, adds no axiom).

## The question

Model one region `rv`'s lifecycle as a two-segment choreography

```
Gx ::= open[rv] . use[rv](j) . close[rv] . end
```

`seg1 = [open .. use]` (rv live), `seg2 = [close .. end]` (rv dead). Does
subject reduction at the `close[rv]` boundary **definitionally discharge**
"rv live throughout seg1", or does coherence of the post-close projection
become a **fresh hypothesis**?

## Method

3-phase adversarial workflow (`wf_300a9737`): parallel reconnaissance of the
exact Coq region-semantics shapes + the Lean tropical session-type
ingredients + the eliminator-fork framing → a design synthesising the
minimal model and a verdict → a 3-lens adversarial verify (soundness,
Coq-buildability/honesty, consistency with the locked ground truth). The
design's verdict survived consistency; soundness and buildability **did not
endorse it as framed** — and in failing they *sharpened* it into a stronger
negative result, recorded below and mechanised in the `.v`.

## Verdict: relocates — and two corrections that make it sharper

**The obligation does not vanish under the choreographic reframe; it
relocates into a projection-coherence side condition that is, definitionally,
exactly `expr_no_exit_of_region` — and at the genuine boundary that condition
is provably FALSE.** Two corrections to the naive framing, both now Qed:

1. **`EDrop (EVar j)` is the wrong probe.** It reduces by `S_Drop`, which
   leaves the region environment `R` unchanged, and **never fires
   `S_Region_Exit`**. It crosses no boundary; it is carried unconditionally
   (`edrop_evar_carries_liveness`, via the existing Qed
   `region_liveness_no_exit_l1_gen`, because
   `expr_no_exit_of_region rv (EDrop (EVar j)) = True`). The `close[rv]`
   boundary exists **only** when an `ERegion rv (…)` frame wraps the term —
   so the choreographic `close` action projects onto the `ERegion` frame,
   not onto `EDrop`.

2. **At the genuine boundary the relocated condition is unsatisfiable.**
   `projection_coherent_after_close rv e := expr_no_exit_of_region rv e`
   (`coherence_is_no_exit`, reflexivity), and on the only boundary-crossing
   term `expr_no_exit_of_region rv (ERegion rv e)` reduces to `rv <> rv ∧ …`
   = **False** (`region_frame_breaks_no_exit`). So the relocation does not
   *close* the obligation; it surfaces it where it is false unless the
   language forbids inner re-entry. Mechanised precisely as
   `close_derives_coherence_needs_no_inner_exit`: the apparatus-level
   proposition `close_derives_coherence` would force that **no** program with
   an inner same-region re-frame `ERegion rv (ERegion rv e0)` ever types with
   `rv` live.

`close_derives_coherence` itself is left as a bare `Definition` (a `Prop`),
**never proved** — the honest record of the open obligation, not a faked
`Qed` and not an `Admitted`.

## Where the real fork actually lives (verifier soundness lens)

**Not** in the clean `ERegion rv` region-exit case — that case is already
**Qed** (`Semantics_L1.v:3462-3493`), protected by the Tofte–Talpin premise
`~ In r (free_regions T)` in `T_Region_Active_L1`. The genuinely admitted
hard cases are the **congruence rules** `S_Let_Step` / `S_App_Step2` /
`S_Pair_Step2` / `S_Case_Step` (`Semantics_L1.v:3271-3284`), where an **inner
step pops a region erased from the outer result type**. The 2-segment
`EDrop`/`ERegion` experiment does not reach them — so the *corrected* next
experiment must target the congruence cases, not the clean exit.

## Implications for the four open L1 admits

The choreographic reframe **converts** the four admits (four faces of one
invariant — see the call-site audit at `Semantics_L1.v:2032-2052`) into a
single global-type coherence obligation = `expr_no_exit_of_region` promoted
to a foundational invariant. That is genuine consolidation (**4 → 1**, the
right shape) but **not closure** (1 ≠ 0). It confirms "four faces of ONE
invariant"; it does not dissolve them to `rfl`.

| Admit | Under the reframe |
|---|---|
| #1 `region_shrink` | the `close[rv]` action; coherent iff residual is `expr_no_exit_of_region rv` |
| #2 `region_liveness` (false as stated) | false snapshot `In rv R → In rv R'` replaced by "Gx advanced past `use[rv]`", valid only under coherence |
| #3 `step_pop` | the congruence-case fork; best-shaped face, but discharged **only** under projection coherence |
| #4 `preservation_l1` | the capstone = subject reduction for the choreography; closes iff `close_derives_coherence` holds at every exit |

## What this does NOT settle / next steps

1. `close_derives_coherence` is unproved (and false in general). A "carries
   coherently" verdict is unavailable for the full language.
2. No `has_type_global` / projection / `coherent(Gx)` / `close`-reduction
   apparatus is built — that is the **next experiment**, aimed at the
   **congruence cases** above.
3. The Lean tropical side supplies the monotonicity backbone
   (`matStar_mono`, `id_le_star`, `parametric_resource_transport`) but has no
   choreography, time segments, grade vector, reduction relation or liveness
   theorem; the graded unification is motivated, not mechanised.
4. **This must not gate** the clean-win deterministic carrier refactor for
   admits 1/2 ([`L1-REGION-REFOUNDATION-PLAN.md`](./L1-REGION-REFOUNDATION-PLAN.md));
   that route is independent of this choreographic research on admits 3/4.
