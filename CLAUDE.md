<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# CLAUDE.md — Ephapax repo agent guidance

## 🚨 Disambiguation (read first)

**This repo is `hyperpolymath/ephapax`.** It is **NOT** `hyperpolymath/affinescript`.

| | This repo | NOT this repo |
|---|---|---|
| Name | **Ephapax** | AffineScript |
| Path | `hyperpolymath/ephapax` | `hyperpolymath/affinescript` |
| File extension | `.eph` | `.affine` (plus face dialects) |
| Build | `Cargo.toml` at root | `dune-project` at root |
| Type checker | `ephapax-linear/src/{linear,affine}.rs` (Rust) | `lib/borrow.ml` (OCaml) |
| Proofs | `formal/Semantics.v` (Coq), `src/abi/Ephapax/…` (Idris2) | None mechanized; `lib/borrow.ml` only |

**Internal naming trap.** Ephapax itself is dyadic. Inside this repo:
- **ephapax-linear** = strict, formally-verified core.
- **ephapax-affine** = versatile prototyping companion to ephapax-linear.

Both are *internal sublanguages*. They share one AST, one Rust crate (`ephapax-linear/`), one grammar directory. **The `ephapax-affine` sublanguage is NOT AffineScript.** The word `affine` is shared because both happen to be substructural-logic-family type systems — that's a logic-family fact, not a project relationship.

**Rule for agents:** before applying any prior-session lesson, memory entry, or snippet, check whether it was about *ephapax* or about *AffineScript*. They share zero AST / typing / borrow-checker / codegen. The only shared surface is the compile target (`hyperpolymath/typed-wasm`).

When in doubt: state the context shift explicitly ("switching from AffineScript context to ephapax context") so the user sees the boundary respected.

**Canonical disambiguation doc** (single source of truth):
https://github.com/hyperpolymath/nextgen-languages/blob/main/docs/disambiguation/ephapax-vs-affinescript.md

**Companion memory entry** (in user auto-memory):
`feedback_affinescript_ephapax_siblings_not_impl_proof.md`

---

## Machine-readable artefacts

Structured project metadata lives in `.machine_readable/6a2/` (7 files):

- `STATE.a2ml` — current project state and progress.
- `META.a2ml` — architecture decisions and development practices.
- `ECOSYSTEM.a2ml` — position in the ecosystem and related projects.
- `AGENTIC.a2ml` — AI agent interaction patterns (also carries an `@disambiguation` block).
- `NEUROSYM.a2ml` — neurosymbolic integration config.
- `PLAYBOOK.a2ml` — operational runbook.
- `ANCHOR.a2ml` — canonical authority and project recalibration trigger (template from `hyperpolymath/standards`); declares SSG / cartridge / parent-relationship metadata.

## The four orthogonal layers

When working in this repo, the typing system has four layers. Knowing which layer a question touches is the first step in answering it:

| Layer | One-line question to ask |
|---|---|
| **L1 — Region capabilities** | "Does this involve `R_in`, `R_out`, or `In r R`?" |
| **L2 — Structural modality** | "Is this about consumption, weakening, or Linear vs Affine?" |
| **L3 — Echo residue** | "Is this about *what was lost* when an irreversible step fired?" |
| **L4 — Dyadic mode** | "Is this a project-level mode declaration question?" |

Most questions touch exactly one layer. The design rationale is in `formal/PRESERVATION-DESIGN.md`. The verified counterexample that forced the redesign is in `formal/Counterexample.v` (3 lemmas under the legacy judgment + `bad_input_untypable_l1` under the new `has_type_l1`).

**Standing rule**: if a proposed change appears to require a side condition on a compound typing rule (e.g. "the sibling doesn't reference this region"), pause — the four-layer threading should make that side condition *derivable*, not stated.

**Disambiguation reminder**: the names L1/L2/L3/L4 (layer names), `ephapax-linear`/`ephapax-affine` (L2 modes / the Rust crate), and `Linear`/`Affine` as used in echo-types (L3 modes) deliberately overlap because the underlying thin-poset construction is shared. Agents must disambiguate by context.

## Standing reminders

- Formal-proof work touches `formal/Semantics.v` + `formal/TypingL1.v` (Coq) and `src/abi/Ephapax/…/*.idr` (Idris2). Both build oracles are authoritative; `coqc` and `idris2 --check` are the only "is this proved?" answers.
- The legacy preservation closure plan is superseded by `formal/PRESERVATION-DESIGN.md` (four-layer redesign). `formal/PRESERVATION-HANDOFF.md` carries the historical diagnostic record only.
- Ephapax-affine type proofs are **NOT** done — `formal/` mechanises a single legacy judgment + L1's `has_type_l1`; there is no separate mechanised ephapax-affine until L2 + the Linear ⇒ Affine weakening lemma land. See `PRESERVATION-DESIGN.md §12.15`.
- All commits GPG-signed (key `4A03639C1EB1F86C7F0C97A91835A14A2867091E`), email `6759885+hyperpolymath@users.noreply.github.com`. Auto-merge ON for every PR.

---

## 🛑 Owner directive 2026-05-27 — preservation work

> Read this before touching anything in `formal/`. Several Claude sessions
> burned hours walking the pre-discovery patching path. This block
> exists so that doesn't happen again.

### TL;DR

Ephapax preservation as originally stated in `formal/Semantics.v` is
**provably false**. `formal/Counterexample.v` exhibits a concrete
configuration that types, steps, and lands at an untypable post-state
— all three lemmas `Qed`. The work is therefore **not** to close
`Theorem preservation` in `Semantics.v`. The work is the **four-layer
principled redesign** (L1 region capabilities / L2 modality (now
`m`-indexed into `has_type_l1`) / L3 echo / L4 dyadic mode) documented
in `formal/PRESERVATION-DESIGN.md`. Preservation is **re-derived** in
the new architecture from explicit invariants, not forced through
the old one.

### DO NOT

These are anti-patterns that have wasted real session time. Refuse
them if asked; if asked anyway, push back and link this section.

1. **DO NOT close `Theorem preservation` in `formal/Semantics.v`.**
   It is FALSE. No proof technique closes it because no proof
   exists. The `Admitted.` is correct.

2. **DO NOT extend `formal/Semantics.v`** with new lemmas aimed at
   closing the legacy preservation: not Lemma B variants
   (`sibling_typing_transfers_across_step` /
   `step_output_context_eq` / `step_preserves_type_at_pre` /
   `step_output_context_eq_at_pre` were earlier attempts in this
   class), not `region_add_typing_for_non_values`, not strengthened
   substitution lemmas. The legacy judgment lacks the structural
   invariant the counterexample demands; no lemma collection bolted
   onto it will help.

3. **DO NOT close any residual axiom in `formal/Semantics_L1.v`
   (e.g. `region_liveness_at_split_l1` if it returns) by adding
   proof tricks, side-conditions discharged ad-hoc, or strengthened
   lemma signatures within the current judgment shape.** This is
   *the same kind of patching that produced the legacy admits*, one
   layer up. The post-L2-hybrid main carries the `Modality`
   parameter directly in `has_type_l1`; closures that previously
   looked like "an L1 fix" are now cross-layer and must be
   reasoned-about at the layered level.

4. **DO NOT follow the "Preservation closure plan" steps in
   historical PRs / branches / comments.** Anything dated before
   2026-05-26 (the counterexample landing) that proposes closing
   `preservation` to `Qed.` is pre-discovery. PRs #92, #102, #104,
   #106, #114, #116, #117, #121, #146 are part of the historical
   reduction-from-910-goals record; treat them as archaeology, not
   instructions.

5. **DO NOT patch the legacy `Typing.v` judgment.** It is the
   pre-redesign judgment. `Counterexample.v` depends on its
   falsity for the regression theorem. Leave it.

### DO

1. **DO read `formal/PRESERVATION-DESIGN.md` first.** It is the
   canonical design source. The four-layer architecture, the
   missing-invariant statement, and the per-layer plan are all
   there.

2. **DO continue the layered build:**
   - L1 (`TypingL1.v` + `Semantics_L1.v`): R-threading + modality
     parameter (post-L2-hybrid). Residual admits are L1 design
     follow-ups, not legacy patching.
   - L2: modality landed in-place via PRs #176 + #177
     (`has_type_l1` now carries `m : Modality`;
     `linear_to_affine` Qed with zero axioms). 6 L1 supporting
     lemmas in `Semantics_L1.v` regressed to Admitted post-L2 —
     bullet-structure rewrite needed for the 3 new Affine-only
     constructors.
   - L3 (`Echo.v`): K-free, forward-looking. Not wired into L1/L2
     judgments yet — that's L1 ⇒ L3 follow-up.
   - L4: not started; design in §7 of the design doc.

3. **DO derive preservation per-layer.** `preservation_l1` is
   proved in the L1 vocabulary, against the L1 judgment, using L1
   invariants. The same shape for L2 / L3 / L4 as each lands.

4. **DO escalate before patching.** If a proof attempt requires
   adding a side-condition to fix a sibling-region-disjointness
   issue (or analogous cross-rule constraint), that is the signal
   to escalate to a layer-design discussion — the architecture is
   asking for a new invariant, not a clever lemma.

### Anti-pattern detector

If your session is producing any of the following, stop and
escalate to the owner:

- `sibling-region-disjointness` side conditions on compound rules,
- region-weakening predicates indexed on syntactic shape,
- admit-shuffling between `Semantics.v` and a new lemma,
- "the previous-PR-line-of-attack just needs one more lemma,"
- proposing to close `Theorem preservation` in `Semantics.v` to
  `Qed.` by any chain of reasoning,
- adding new `Axiom` declarations to discharge L1/L2 gaps.

### If you're unsure

Two questions to ask before touching `formal/`:

1. **Am I about to add an `Admitted` or `Axiom` to close a gap in
   the old judgment?** If yes — stop. The old judgment is provably
   incomplete; the right answer is to encode the missing invariant
   in a new layer, not to admit it.

2. **Am I about to close an L1/L2/L3 admit by reasoning that
   crosses layers?** If yes — check `PRESERVATION-DESIGN.md` for
   the cross-layer dependency annotations. The layered design
   intentionally splits some closures across layers; trying to
   close them within one layer alone is the trap.

If unsure: ask the owner before writing code. Pause to escalate
costs less than a 4-hour patching session.

### Memory hooks

If you have access to the user's auto-memory store, relevant
entries include:

- `feedback_ephapax_no_patching_legacy_preservation.md` — the
  durable directive captured 2026-05-27 (this section).
- `project_ephapax_four_layer_redesign.md` — current project state.
- `project_ephapax_l2_modality_landed.md` — L2 hybrid landing
  (PRs #176 + #177).
- `feedback_ephapax_affine_proofs_not_done.md` — what counts as
  "done" for the ephapax-affine half.
