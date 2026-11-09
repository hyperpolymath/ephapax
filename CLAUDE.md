<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# CLAUDE.md — Ephapax repo agent guidance

## 🚨 Disambiguation (read first)

**This repo is `hyperpolymath/ephapax`.** It is **NOT** `hyperpolymath/affinescript`.

| Criterion | This repo | NOT this repo |
|---|---|---|
| Name | **Ephapax** | AffineScript |
| Path | `hyperpolymath/ephapax` | `hyperpolymath/affinescript` |
| File extension | `.eph` | `.affine` (plus face dialects) |
| Build | `Cargo.toml` at root | `dune-project` at root |
| Type checker | `ephapax-linear/src/{linear,affine}.rs` (Rust) | `lib/borrow.ml` (OCaml) |
| Proofs | `formal/Semantics.v` (Coq), `src/abi/Ephapax/…` (Idris2) | None mechanized; `lib/borrow.ml` only |

**Internal naming trap.** Ephapax itself is dyadic. Inside this repo:
- **ephapax-linear** = strict core with formal artifacts; no full language-soundness or implementation-refinement proof is claimed.
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

Proof and design history is in `formal/PRESERVATION-DESIGN.adoc`; current status is in `PROOF-NEEDS.adoc`. The legacy counterexample and the separate L1 regressions are in `formal/Counterexample.v`, `Counterexample_StepPop.v`, and `Counterexample_PreservationL1.v`. These prove exact counterexamples, not a sound replacement.

**Standing rule**: if a proposed change appears to require a side condition on a compound typing rule (e.g. "the sibling doesn't reference this region"), do not assume it is derivable. The pinned L1 witnesses show that the current judgment does not encode the temporal dependency. Pause and propose an explicit judgment/step redesign; do not patch the false preservation theorem by strengthening a helper lemma.

**Disambiguation reminder**: the names L1/L2/L3/L4 (layer names), `ephapax-linear`/`ephapax-affine` (L2 modes / the Rust crate), and `Linear`/`Affine` as used in echo-types (L3 modes) deliberately overlap because the underlying thin-poset construction is shared. Agents must disambiguate by context.

## Standing reminders

- Formal-proof work spans Coq, Idris2, and the applicable estate policy. Checker output is evidence only for the exact proposition and assumptions run; a green build does not establish general language soundness.
- The legacy preservation closure plan is obsolete. `formal/PRESERVATION-DESIGN.adoc` is design/history, not a proof result; `formal/PRESERVATION-HANDOFF.adoc` is historical diagnosis only.
- Modality and `linear_to_affine` artifacts are mechanised, but no unconditional L1/L2 preservation theorem is established. The modality-polymorphic L1 statement is refuted as stated; see `PROOF-NEEDS.adoc` and the EXPLAINME ledger.
- All commits GPG-signed (key `4A03639C1EB1F86C7F0C97A91835A14A2867091E`), email `6759885+hyperpolymath@users.noreply.github.com`. Auto-merge ON for every PR.

---

## Orientation: this language is gestating — engage with v2

**Read `V1-TO-V2.adoc` first.** Ephapax is part-way through a deliberate
second draft on grammar and proof design. The legacy preservation theorem
is false, and later counterexamples also refute the current unrestricted
L1 preservation claim; L2 has no unconditional preservation theorem.
Do not read this as "there is nothing to do here": the active work is to
redesign and state sound replacement theorems, not to prove refuted ones.

**Where the tractable work is (engage with this):**

- **Proof, L1** — do not attempt to close the unrestricted
  `step_pop_disjoint_from_type_l1` or `preservation_l1` statements:
  both are refuted by pinned Coq counterexamples. The open work is an
  owner-approved judgment/step redesign with an explicit temporal
  invariant, followed by a new theorem with a stated boundary.
- **Proof, L2** — no unconditional `preservation_l2` theorem exists.
  Keep the fresh-region and nested-`TFunEff` counterexamples visible;
  the existing β-case lemmas are conditional.
- **Proof, L3** — the Qed preservation result is scoped to matching
  echo-emitting typing/step rules; it is not general L1/L2 preservation.
- **Grammar, v2** — continue the phase work in
  `spec/ephapax-v2-grammar.ebnf` + the `v2_grammar_phase_*` CLI tests.
- **Proof, L4** — Phase A scaffold landed; mother–child dyadic
  semantics (`PRESERVATION-DESIGN.adoc §7`) is the next design step.

## 🛑 Owner directive snapshot (2026-05-27, revised 2026-11-05) — legacy fence plus later L1 regressions

> **2026-11-05 revision (owner-ratified D0 and D0b).** The three refuted
> statements are retired, not closed: `Semantics.preservation` is now
> `preservation_stmt : Prop`, refuted by `Counterexample.preservation_false`;
> `step_pop_disjoint_from_type_l1` and `preservation_l1` are now
> `…_stmt : Prop`, refuted by `Counterexample_StepPop.v` and
> `Counterexample_PreservationL1.v`. While they were `Admitted`, the build
> could derive `False`. `formal/` now has **0 `Admitted` and 0 `Axiom`**,
> and CI's no-False gate (`formal/scripts/no-false-gate.sh`, run by
> `coq-build.yml`) fails on any assumption vernacular or `admit` outside
> comments, on any kernel-check bypass, on any named result not closed under
> the global context, and on any Ephapax axiom that `coqchk` finds. The fence below is unchanged in spirit:
> never try to prove a refuted statement.

> The guardrails below protect pinned counterexamples and the false
> statements they refute. They do **not** mean "skip this repo." The
> active work is redesigning sound judgments and theorem boundaries;
> do not try to prove legacy or L1 statements that have already been
> refuted.

### TL;DR

Ephapax preservation as originally stated in `formal/Semantics.v` is
**provably false** — and that is a *result*, not a defeat:
`formal/Counterexample.v` exhibits a concrete configuration that types,
steps, and lands at an untypable post-state (now 6 lemmas `Qed`, incl. `preservation_false`), which
named an invariant missing from the legacy judgment. So the work is **not**
to close the legacy preservation in `Semantics.v` (no closure exists; it
is retired to `preservation_stmt : Prop`, refuted by `preservation_false`). Nor should the current unrestricted L1
preservation be treated as routine debt: `Counterexample_StepPop.v` and
`Counterexample_PreservationL1.v` refute its supporting claim and capstone.
There is no unconditional L2 preservation theorem; the L2 β-case helpers
are conditional and later counterexamples document distinct gaps. The
four-layer architecture in `formal/PRESERVATION-DESIGN.adoc` is a design
program, not proof that the language is sound. Preserve each local
counterexample and state any replacement theorem with its exact boundary.

### DO NOT

These are anti-patterns that have wasted real session time. Refuse
them if asked; if asked anyway, push back and link this section.

1. **DO NOT prove or restate the legacy preservation in
   `formal/Semantics.v`.** It is FALSE and is refuted by
   `Counterexample.preservation_false`. It stays `preservation_stmt : Prop`;
   never turn it back into a `Theorem`/`Lemma`, and never re-add an
   `Admitted.` for it.

2. **DO NOT extend `formal/Semantics.v`** with new lemmas aimed at
   closing the legacy preservation: not Lemma B variants
   (`sibling_typing_transfers_across_step` /
   `step_output_context_eq` / `step_preserves_type_at_pre` /
   `step_output_context_eq_at_pre` were earlier attempts in this
   class), not `region_add_typing_for_non_values`, not strengthened
   substitution lemmas. The legacy judgment lacks the structural
   invariant the counterexample demands; no lemma collection bolted
   onto it will help.

3. **DO NOT try to prove the unrestricted
   `step_pop_disjoint_from_type_l1_stmt` or `preservation_l1_stmt`
   statements in `formal/Semantics_L1.v`.** Both are refuted by pinned
   witnesses and retired to `Prop`; they are not debt. Results that need
   them take them as explicit hypotheses (as `preservation_l2_via_l1`
   now does).
   Do not route around the counterexamples with ad-hoc side conditions or
   helper-signature changes. A separately stated sound theorem after an
   owner-approved judgment/step redesign is allowed and expected.

4. **DO NOT follow the "Preservation closure plan" steps in
   historical PRs / branches / comments.** Anything dated before
   2026-05-26 (the counterexample landing) that proposes closing
   `preservation` to `Qed.` is pre-discovery. PRs #92, #102, #104,
   #106, #114, #116, #117, #121, #146 are part of the historical
   reduction-from-910-goals record; treat them as archaeology, not
   instructions.

5. **DO NOT patch the legacy `Typing.v` judgment.** It is the
   pre-redesign judgment. `Counterexample.v` depends on its
   falsity for `preservation_false`. Leave it.

### DO

1. **DO read `PROOF-NEEDS.adoc` and `EXPLAINME.adoc` for current status.**
   `formal/PRESERVATION-DESIGN.adoc` records the architecture and history;
   it is not evidence that a layer's preservation theorem is established.

2. **DO continue the layered build without overclaiming:**
   - L1 (`TypingL1.v` + `Semantics_L1.v`): the judgment and helper
     lemmas exist, but the unrestricted preservation claim is refuted.
     Replacement design is open; its theorem boundary must be explicit.
   - L2: modality is mechanised and `linear_to_affine` is Qed, but
     no unconditional `preservation_l2` theorem exists. Treat the
     β-case lemmas as conditional and retain both L2 counterexamples.
   - L3 (`Echo.v`): calculus and selected matching-rule preservation
     results are Qed; do not generalise them to L1/L2.
   - L4: scaffold/design only; no preservation theorem.

3. **DO state and prove only sound replacement theorems.** A theorem
   name or layer label does not make a statement true. First write the
   exact judgment, transition relation, hypotheses, and boundary; then
   prove it locally and report its assumptions and regressions.

4. **DO follow estate proofing and grading policy.** Consult
   `hyperpolymath/standards/3-practice/PROOF-POLICY.adoc` for prover
   mapping and for Proof Witness Grades (§8, which supersedes the grades in
   the mathesis brief). `PWG-3` requires a local Agda proof checked with
   `agda --safe --without-K --cubical-compatible`; Coq `Qed` is Coq
   evidence, not `PWG-3`, and counts as a recheck leg only once an Agda
   source exists and the statements are `RECONCILED`. Always write the
   `PWG-` prefix. Standards maps
   Ephapax-specific engineering claims to Idris2 unless an
   implementation-independent theory statement is explicitly defined.
   Do not assign a PWG until that classification and exact
   statement correspondence are recorded in `EXPLAINME.adoc` and
   `PROOF-NEEDS.adoc`.

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
- proposing to prove `preservation_stmt` (or turn it back into a
  `Theorem`) by any chain of reasoning,
- re-adding any `Admitted.` to `formal/` (the no-False gate will fail),
- adding new `Axiom` declarations to discharge L1/L2 gaps.

### If you're unsure

Two questions to ask before touching `formal/`:

1. **Am I about to add an `Admitted` or `Axiom` to close a gap in
   the old judgment?** If yes — stop. The old judgment is provably
   incomplete; the right answer is to encode the missing invariant
   in a new layer, not to admit it.

2. **Am I about to close an L1/L2/L3 admit by reasoning that
   crosses layers?** If yes — check `PRESERVATION-DESIGN.adoc` for
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
