<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell -->

# CLAUDE.md — Ephapax agent guidance

> **Read this before touching `formal/`.** Several Claude sessions
> burned hours walking the pre-discovery patching path. This file
> exists so that doesn't happen again.

## TL;DR — the work, in one paragraph

Ephapax preservation as originally stated in `formal/Semantics.v` is
**provably false**. `formal/Counterexample.v` exhibits a concrete
configuration that types, steps, and lands at an untypable post-state
— all three lemmas `Qed`. The work is therefore **not** to close
`Theorem preservation` in `Semantics.v`. The work is the **four-layer
principled redesign** (L1 region capabilities / L2 modality / L3 echo
/ L4 dyadic mode) documented in `formal/PRESERVATION-DESIGN.md`.
Preservation is **re-derived** in the new architecture from explicit
invariants, not forced through the old one.

## DO NOT

These are anti-patterns that have wasted real session time. Refuse
them if asked; if asked anyway, push back and link this file.

1. **DO NOT close `Theorem preservation` in `formal/Semantics.v`.**
   It is FALSE. No proof technique closes it because no proof
   exists. The `Admitted.` is correct.

2. **DO NOT extend `formal/Semantics.v`** with new lemmas aimed at
   closing the legacy preservation: not Lemma B variants
   (`sibling_typing_transfers_across_step` /
   `step_output_context_eq` were earlier attempts in this class),
   not `region_add_typing_for_non_values`, not strengthened
   substitution lemmas. The legacy judgment lacks the structural
   invariant the counterexample demands; no lemma collection bolted
   onto it will help.

3. **DO NOT close the `region_liveness_at_split_l1` axiom in
   `formal/Semantics_L1.v` by adding proof tricks, side-conditions
   discharged ad-hoc, or strengthened lemma signatures within the
   current judgment shape.** This is *the same kind of patching
   that produced the legacy admits*, one layer up. The axiom is
   false-as-stated; it surfaces a real gap that L2/L3 close
   structurally (cross-layer dependency — see
   PRESERVATION-DESIGN.md §5.1).

4. **DO NOT follow the "Preservation closure plan" steps in
   historical PRs / branches / comments.** Anything dated before
   2026-05-26 (the counterexample landing) that proposes closing
   `preservation` to `Qed.` is pre-discovery. PRs #92, #102, #104,
   #106, #114, #116, #117, #121 are part of the historical
   reduction-from-910-goals record; treat them as archaeology, not
   instructions.

5. **DO NOT patch the legacy `Typing.v` judgment.** It is the
   pre-redesign judgment. Counterexample.v depends on its falsity
   for the regression theorem. Leave it.

## DO

1. **DO read `formal/PRESERVATION-DESIGN.md` first.** It is the
   canonical design source. The four-layer architecture, the
   missing-invariant statement, and the per-layer plan are all
   there.

2. **DO continue the layered build:**
   - L1 (`TypingL1.v` + `Semantics_L1.v`): R-threading, mostly in
     place; preservation_l1 has open admits — these are L1 design
     follow-ups, not legacy patching.
   - L2 (`TypingL2.v` + `Modality.v`): skeleton landed (#168);
     mode-specific rules + cross-layer integration are next.
   - L3 (`Echo.v`): forward-looking scaffold (#166, #167); not
     wired into L1 yet — that's L1 ⇒ L3 follow-up.
   - L4: not started; design in §7 of the design doc.

3. **DO derive preservation per-layer.** `preservation_l1` is
   proved in the L1 vocabulary, against the L1 judgment, using L1
   invariants. Same for L2, L3. There is no single
   `preservation` for the unified calculus until L4 composition.

4. **DO escalate before patching.** If a proof attempt requires
   adding a side-condition to fix a sibling-region-disjointness
   issue (or analogous cross-rule constraint), that is the signal
   to escalate to a layer-design discussion — the architecture is
   asking for a new invariant, not a clever lemma.

## File reference

| File | Status | What it is |
|---|---|---|
| `formal/Syntax.v` | shared AST | safe to edit (with care) |
| `formal/Typing.v` | **legacy** `has_type` | frozen — depends on counterexample's regression role |
| `formal/Semantics.v` | shared `step` + falsified `preservation` | frozen for the preservation theorem; `step` may need extension at L2/L3 |
| `formal/Counterexample.v` | three Qed lemmas | the verified soundness gap; do not edit the legacy section |
| `formal/TypingL1.v` | L1 judgment | active layered work |
| `formal/Semantics_L1.v` | L1 lemmas + `preservation_l1` | active layered work |
| `formal/Modality.v` | L2 thin-poset infrastructure | active |
| `formal/TypingL2.v` | L2 judgment skeleton | active |
| `formal/Echo.v` | L3 scaffold | forward-looking |
| `formal/PRESERVATION-DESIGN.md` | **canonical design source** | read this first |
| `formal/PRESERVATION-HANDOFF.md` | **superseded** diagnostic record | historical only |
| `ROADMAP.adoc` | scheduling | preservation entries point at design doc |

## If you're unsure

Two questions to ask before touching `formal/`:

1. **Am I about to add an `Admitted` or `Axiom` to close a gap in
   the old judgment?** If yes — stop. The old judgment is provably
   incomplete; the right answer is to encode the missing invariant
   in a new layer, not to admit it.

2. **Am I about to close an L1/L2/L3 admit by reasoning that
   crosses layers?** If yes — check
   `PRESERVATION-DESIGN.md §5.1` (cross-layer dependency). The
   layered design intentionally splits some closures across L1+L2
   or L1+L3; trying to close them within L1 alone is the trap.

If unsure: ask the owner before writing code. Pause to escalate
costs less than a 4-hour patching session.

## Memory hooks

If you have access to the user's auto-memory store, relevant entries
include:

- `project_ephapax_four_layer_redesign.md` — the canonical project
  state for this redesign.
- `feedback_ephapax_no_patching_legacy_preservation.md` — the
  durable directive captured from the 2026-05-27 conversation that
  produced this CLAUDE.md.
- `feedback_ephapax_affine_proofs_not_done.md` — what counts as
  "done" for the ephapax-affine half.
