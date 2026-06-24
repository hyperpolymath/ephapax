<!--
SPDX-License-Identifier: CC-BY-SA-4.0
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Proof Debt — ephapax (SUPERSEDED — archaeology only)

> ## 🛑 SUPERSEDED
>
> This document was written against the pre-2026-05-26 legacy-judgment
> closure plan and lists `step_preserves_type` / `step_output_context_eq` /
> `preservation` as (d) DEBT with a 2026-09-01 deadline. That framing is
> **banned** per owner directive 2026-05-27: the legacy
> `Theorem preservation` in `formal/Semantics.v` is *provably false*
> (`formal/Counterexample.v`, five `Qed` lemmas) and its `Admitted.`
> is correct + durable.
>
> **Canonical proof-debt sources**:
> - `PROOF-NEEDS.md` (root)
> - `formal/PRESERVATION-DESIGN.md §12`
> - `formal/PHASE-D-REDESIGN.md`
>
> Retained for traceability against the
> [trusted-base-reduction policy](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc)
> (standards#203). The classification framework `(a)–(d)` is still
> meaningful; the specific entries below are stale.

**Schema**: [hyperpolymath/standards `TRUSTED-BASE-REDUCTION-POLICY.adoc`](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc) (standards#203).

Markers in scope (from the 2026-05-26 estate proof-debt audit,
standards#195):
- Coq `Axiom`, `Admitted`, `admit.`
- Idris2 `believe_me`, `assert_total`, top-level `partial`
- `TODO PROOF` / `OWED:` / `FIXME PROOF` markers

## (a) DISCHARGED in this repo

*(None yet — entries move here when their proof lands.)*

## (b) BUDGETED — tested with a refutation budget

*(None — ephapax's proof targets are deductive, not property-tested. Items
in this section would belong here if/when we add adversarial-test budgets
for the Rust↔Idris2 ABI boundary code.)*

## (c) NECESSARY AXIOM

*(None — ephapax does not introduce any irreducible metatheoretic axioms
in the working Coq logic. If future work adds e.g. `funExt`, list it here
with a citation to its canonical formalisation.)*

## (d) DEBT — actively to be closed

### `formal/Semantics.v:4924` — `Admitted` inside `step_preserves_type`

- **Lemma**: `step_preserves_type` (declared at `formal/Semantics.v:3615`).
- **Statement (informal)**: small-step semantics preserve typing.
- **Owner**: @hyperpolymath
- **Plan**: discharge as part of [project_ephapax_preservation_closure_plan](https://github.com/hyperpolymath/standards/blob/main/docs/audits/2026-05-26-estate-proof-debt.md). Estimated 6–9 days. ~40 goals split into sub-buckets A/B/C/D; start with A.
- **Deadline**: 2026-09-01 (per closure plan).

### `formal/Semantics.v:5983` — `Admitted` inside `step_output_context_eq`

- **Lemma**: `step_output_context_eq` (declared at `formal/Semantics.v:4944`).
- **Statement (informal)**: output context is preserved across a step
  (modulo region marking).
- **Owner**: @hyperpolymath
- **Plan**: discharged as a corollary of the strengthened
  `step_preserves_type` proof; depends on the preservation closure plan.
- **Deadline**: 2026-09-01.

### `formal/Semantics.v:6572` — `Admitted` inside `preservation`

- **Theorem**: `preservation` (declared at `formal/Semantics.v:5985`).
- **Statement (informal)**: the main preservation theorem for the ephapax
  region-aware operational semantics.
- **Owner**: @hyperpolymath
- **Plan**: this is the top-level theorem the other two Admitteds feed
  into. Discharge order: `step_preserves_type` first → then
  `step_output_context_eq` → then `preservation` lands automatically
  modulo wiring.
- **Deadline**: 2026-09-01.

## Soundness-relevant escape hatches in non-Coq code

The 2026-05-26 audit also surfaced:
- 1 `believe_me` reference (a comment in
  `src/formal/Ephapax/Formal/RegionLinear.idr:127` explicitly stating
  "This is a REAL proof — not (), not believe_me, not assert_total" —
  no actual `believe_me` use; the comment is documentation about NOT
  using it).
- 1 `partial` (Idris2 totality waiver) — TBD if real or comment artefact.
- 14 `TODO PROOF` / `OWED:` markers — these were not located in this
  repo by the per-repo scan; they likely cluster around the same
  Admitteds above.

When `scripts/check-trusted-base.sh` lands, any genuine occurrence of
the above will require either a leading `TRUSTED:` / `AXIOM:` annotation
or a `§(d) DEBT` entry here.

## How to update this file

After each PR that closes one of the entries above:

1. Move the entry from §(d) → §(a) DISCHARGED.
2. Update the closure plan referenced.
3. Run `git cliff --output CHANGELOG.md` to regenerate the changelog
   (see [standards#206](https://github.com/hyperpolymath/standards/pull/206) for
   the canonical workflow).

## Companion documents

- [standards#195](https://github.com/hyperpolymath/standards/pull/195) — estate proof-debt audit
- [standards#203](https://github.com/hyperpolymath/standards/pull/203) — trusted-base reduction policy (the schema this file follows)
- `project_ephapax_preservation_closure_plan` (maintainer memory) — 6–9 day discharge plan

---

🤖 Initial seed by Claude Code, 2026-05-26.
