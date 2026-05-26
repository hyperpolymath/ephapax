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

### Preservation region-step debt — **CLOSED 2026-05-25**

The previous `S_Region_Step` preservation gap is closed in PR #135.
The source repair is semantic rather than a proof workaround:
`S_Region_Step` now carries the invariant that the enclosing region is
still active after the inner step. With that invariant, the three
affected proofs close normally:

| Lemma | Status | Closing idea |
|---|---|---|
| `step_preserves_type` | closed | a post-step active-region premise rules out the inactive typing branch |
| `step_output_context_eq` (Lemma B) | closed | same post-step activity contradiction, then IH on the inner step |
| `preservation` | closed | the `r1 = r` shrink case reuses the post-step activity premise to prove inner step safety |

The supporting infrastructure remains:
- `step_R_change_shape` (3-way disjunction)
- `remove_first_then_cons_membership_eq` (no NoDup required)
- `output_ctx_det_across_step` (bridges different R via permutation)
- `has_type_lift_across_step_no_shrink`
- `sibling_transport`
- `safe_for_step` + projection/discharge lemmas

Current verification:

    rg -n '\bAdmitted\.|\bADMITTED\b|\badmit\b|\bAxiom\b|axiom|believe_me|assert_total' formal/Semantics.v
    coqc -Q formal Ephapax formal/Syntax.v
    coqc -Q formal Ephapax formal/Typing.v
    coqc -Q formal Ephapax formal/Semantics.v

## Idris2 — `src/formal/Ephapax/Formal/RegionLinear.idr`

### `believe_me` (1 occurrence) — **FALSE POSITIVE**
### `assert_total` (1 occurrence) — **FALSE POSITIVE**

Both flagged occurrences are in a **single comment line** explicitly
asserting the opposite — i.e. that the proof below does NOT use
either escape hatch. From `RegionLinear.idr:127`:

    ||| This is a REAL proof — not (), not believe_me, not assert_total.
    public export
    0 noEscapeTheorem : (r : RegionId) -> NoRegionInType r (Scoped r a) -> Void
    noEscapeTheorem r (PlainType ns) = absurd ns
    noEscapeTheorem r (DifferentRegion notSame) = notSame Refl

Verified with:

    grep -rEn '\bbelieve_me\b|\bassert_total\b' src/ \
      | grep -v 'comment\|//\|--\|^Binary\||||'
    # (no actual uses — the regex hits only the negative-assertion comment)

No action; the comment stays because it's a useful negative
assertion for human reviewers.

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

### `unsafe` blocks (3 occurrences) in `src/ephapax-interp/src/lib.rs`

All three sit at FFI boundaries (`libloading::Library::new`,
`lib.get(name)`, calling the resolved `extern "C" fn` symbol). All
three now carry inline `// SAFETY: …` comments documenting the
relevant invariant (caller-trusted path, type-erasure contract,
Ephapax-level FFI typecheck). Inline annotation lands in the same
commit as this row.

### `as_ptr()` in `src/ephapax-interp/src/lib.rs`

A single `CString::as_ptr()` used to pass a UTF-8 string to a C
function. The CString is pushed into `cstrings` immediately to
extend its lifetime past the FFI call. Inline `// SAFETY:` comment
documents the contract.

### `unwrap_or(0)` in `src/ephapax-wasm/src/lib.rs` — **NOT actually dangerous**

Flagged "critical" by Hypatia's `unwrap_dangerous_default` rule but
the `0` default is meaningful: `None` ("no data constructor info")
behaves identically to `Some(_, 0)` because the immediately-following
`if total >= 2` dispatches both to the same else branch. Inline
`// NOTE:` comment explains the intent.

False positive at the rule level; left in place because annotating
silently with `#[allow(...)]` would hide the intent from future
readers. The `// NOTE` is the honest fix.

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
