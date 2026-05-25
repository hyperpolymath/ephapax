<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Known Proof Debt — Hypatia Scan Findings Triage

The Hypatia neurosymbolic CI scan flags formal-verification escape
hatches (`Admitted`, `admit`, `believe_me`, `assert_total`, axioms) as
critical findings. This document **acknowledges** the known set and
explains why each is present, so they are tracked honestly rather than
silently allowlisted.

This is also the canonical place to look up "is this Admitted on
purpose, or did someone forget?" — every entry below is on purpose
pending a documented closure path.

## Coq — `formal/Semantics.v`

### `Admitted` lemmas (5 total)

All five sit on the `S_Region_Step` case where the inner step exits
the OUTER `ERegion`'s own region (`r1 = r0` sub-case). The root cause
is a single semantic obstacle: `expr_free_of_region`'s shadowing rule
returns `True` at the outer `ERegion r0 _` level, so outer hypotheses
on `safe_for_step` carry no information about deeply-nested sibling
references to `r0`.

| Lemma | Open sub-case | Resolution path |
|---|---|---|
| `step_preserves_type` | `T_Region_Active × T_Region` with `r1 = r0` | Path 1 (typing invariant) |
| `step_output_context_eq` (Lemma B) | same | same |
| `preservation` | same | same |
| `subst_typing_gen` | (downstream of the above) | same |
| (one more, downstream) | — | same |

Closure infrastructure landed (all `Qed`):
- `step_R_change_shape` (3-way disjunction)
- `remove_first_then_cons_membership_eq` (no NoDup required)
- `output_ctx_det_across_step` (bridges different R via permutation)
- `has_type_lift_across_step_no_shrink`
- `sibling_transport`
- `safe_for_step` + ~25 projection/discharge lemmas

What's left: add `expr_no_region_named` as a premise on
`T_Region_Active` (and possibly `T_Region`), plus
`step_preserves_no_region_named` (~80 LOC), plus the closure tactics
(~30 LOC per admit). See:
- `docs/sessions/SESSION-2026-05-24-preservation-handoff.md` for the
  full per-case status.
- `ROADMAP.adoc` § "Preservation closure plan" for the planned route.

### `admit` tactic occurrences (8 total)

These are sub-case admits inside structured proofs — each closes a
specific R-shape sub-case of the parent lemma's `S_Region_Step`. They
are the per-case granularity of the 5 `Admitted` lemmas above.

### Axioms (2 occurrences)

[TODO: enumerate the two — likely classical reasoning or string
decidability — and confirm they are kernel-acceptable vs imported
from `Coq.Logic.*` / `Coq.Strings.*`.]

## Idris2 — `src/formal/Ephapax/Formal/RegionLinear.idr`

### `believe_me` (1 occurrence)

[TODO: locate and document — this is the standard Idris2 escape hatch
for "I know better than the totality checker." Common usages are for
witness construction where the proof would be straightforward but
mechanically expensive. Should either be eliminated or annotated
inline with the reason.]

### `assert_total` (1 occurrence)

[TODO: locate. Usually marks recursive functions whose termination
the totality checker can't prove. Should be either eliminated or
annotated.]

## Rust — known acceptable patterns

These are NOT proof debt; they are tagged "code_safety" by Hypatia
but are deliberate by-design idioms:

### `expect()` in REPL hot paths (`src/ephapax-repl/src/lib.rs`, `src/ephapax-typing/src/lib.rs`)

The REPL's `expect(msg)` calls are on invariants that are themselves
established by surrounding type checks. They make the panic message
explicit when those invariants would otherwise indicate a logic bug
in the REPL itself, not a recoverable user-input error.

### `from_raw` in `src/ephapax-vram-cache/src/lib.rs`

The VRAM cache module necessarily traffics in raw pointers (it manages
GPU memory via a `c_void` handle to the underlying VRAM allocation).
The `from_raw` constructor is paired with documented invariants in
the module's safety comments.

### `unwrap()` in `src/ephapax-vram-cache/benches/cache_bench.rs`

Benchmark code is allowed to panic on unexpected input — benchmarks
crash on bad data rather than fall back to slower paths that would
distort the measurement.

## Workflow audit

### `unpinned_action` — `governance.yml` references `@main`

`hyperpolymath/standards/.github/workflows/governance-reusable.yml@main`
is referenced unpinned. This is an estate-internal action (the
"standards" repo is in the same org as ephapax); unpinning lets the
governance reusable workflow update centrally. Pinning to a SHA would
require a coordinated bump across every consumer repo on every change.

Acceptable per estate governance; flagged in scan for transparency.

## Update process

When a finding is resolved (e.g. an `Admitted` flips to `Qed`),
delete its row above and the next Hypatia run should show one fewer
critical / high finding. If the count goes UP from one run to the
next, a new debt has accrued — surface it here before merging.
