<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# Ephapax L4 — Dyadic mode (labelling discipline)

> Scope: project / module-level labelling. **No proof obligations.**
> Companion mechanical scaffold: [`formal/L4.v`](L4.v).
> Canonical design source: [`formal/PRESERVATION-DESIGN.md §7`](PRESERVATION-DESIGN.md).

## What L4 is

L4 is the outermost ring of the four-layer redesign. Where L1 / L2 / L3
each carry a typing-layer judgment or per-layer proof obligation, L4
carries **none of that**. It is a *labelling discipline* applied at the
program / module boundary.

A closed Ephapax program declares one of three program modes:

| `ProgramMode` (L4) | Selects L2 modality | L3 echo discipline that follows |
|---|---|---|
| `EphapaxLinear` | `Linear` | Echoes must be **observed** before program end |
| `EphapaxAffine` | `Affine` | Echoes may be observed or silently lowered |
| `ModuleBoundaryMix` | per-module | Module's L2 modality determines its L3 echo discipline at each boundary crossing |

The declaration tells the type checker which L2 modality `m` to thread
through `has_type_l1`. Once `m` is selected, L3's echo observation
discipline follows from L2 with no further user input.

## Why L4 is not a separate proof layer

The four-layer redesign assigns proof obligations as follows:

| Layer | What it proves | Where the proof lives |
|---|---|---|
| **L1** | Region-capability soundness; preservation under R-threading | `formal/TypingL1.v` + `formal/Semantics_L1.v` |
| **L2** | Modality lifting (Linear ⇒ Affine) | `formal/Modality.v` (`linear_to_affine` Qed) |
| **L3** | Echo residue preservation under irreversible steps | `formal/Echo.v` + `preservation_l3` in `formal/Semantics_L1.v` |
| **L4** | (nothing — labelling only) | `formal/L4.v` (Definitions only, no theorems) |

L4 is the *user-facing surface* through which L1–L3's proofs are
applied to a concrete program. Selecting `EphapaxLinear` at L4 instructs
the system to:

1. Choose `Linear : Modality` at L2.
2. Enforce echo observation at L3.
3. Apply L1's preservation theorem to the resulting derivation.

No new theorem is needed at L4 because no new judgment is introduced.

## The mother–child dyad

The dyadic framing (PRESERVATION-DESIGN.md §7) reads the Linear /
Affine pair as an **asymmetric dyad**:

- **Linear** = the obligation-bearer (the *speaker* of the dyad).
  Linear-mode programs are responsible for discharging every echo
  before termination.
- **Affine** = the obligation-relaxer (the *listener*).
  Affine-mode programs may accept, observe, or silently drop echoes —
  the listener has the option of not engaging.

Both sides are needed because real systems contain both
obligation-bearing components (resource owners, audit trails, GDPR
deletion receipts) and obligation-relaxing components (loggers, UI,
diagnostics that may safely vanish).

The dyad **is not symmetric**: a Linear-mode component can call into
an Affine-mode component (the listener silently relaxes), but an
Affine-mode component cannot call into a Linear-mode component except
through a designated obligation-handoff (a `ModuleBoundaryMix`
declaration explicitly converts the obligation surface).

This asymmetry is exactly what L2's `linear_to_affine` lemma
mechanises: every Linear derivation can be viewed as an Affine
derivation, but not vice versa.

## Orthogonality to L1 / L2 / L3

L4 is orthogonal to the lower layers in the following sense:

- **L1 (region capabilities)** is the *same* in both Linear and
  Affine — both must track region exit precisely for soundness.
  Switching L4 program mode does not change L1's invariants.
- **L2 (modality)** gives the *direction* of the dyad — which side
  is obligation-bearing. L4 selects which L2 modality the program
  inhabits.
- **L3 (echo)** is the *protocol* of obligation discharge — what
  the observer must do with the residue. L4 selects the L3
  discipline indirectly through L2.

## What L4 declarations look like (illustrative)

L4 is currently a *design layer*. Surface syntax has not yet been
wired into the parser or borrow checker. The intended shape:

```ephapax
// Top of a closed program, before any imports
#![ephapax_linear]

// — or —

#![ephapax_affine]

// — or, at the boundary of a multi-module project —

#![module_boundary_mix(default = "ephapax_affine")]
mod critical_section {
    #![ephapax_linear]
    // every echo here must be observed before this module returns
}
```

The mechanical surface for downstream tools is in [`formal/L4.v`](L4.v):

- `ProgramMode` — three-constructor enum (`PModeLinear` /
  `PModeAffine` / `PModeBoundaryMix`).
- `program_mode_to_modality` — total function `ProgramMode -> Modality`
  (with `PModeBoundaryMix` mapped to a default; per-module modality is
  read from the surrounding declaration).
- No theorems; no admit; no axiom.

## What L4 does NOT do

L4 introduces **zero** new proof obligations. In particular:

- L4 does NOT introduce a new typing judgment.
- L4 does NOT introduce a new step relation.
- L4 does NOT introduce a new preservation theorem.
- L4 does NOT introduce a new echo discipline.
- L4 does NOT change the L1 region-threading invariants.
- L4 does NOT change the L2 modality-lifting lemma.

If a question about L4 leads to a proof obligation, the question is
not about L4 — it is about whichever lower layer the obligation lives
in (probably L2 if it concerns modality lifting, or L3 if it concerns
echo discipline).

## Cross-references

- [`formal/PRESERVATION-DESIGN.md §7`](PRESERVATION-DESIGN.md) —
  canonical design source.
- [`formal/PRESERVATION-DESIGN.md §8`](PRESERVATION-DESIGN.md) —
  per-layer proof-need separation between Linear and Affine.
- [`formal/L4.v`](L4.v) — the mechanical scaffold (Definitions only).
- [`formal/Modality.v`](Modality.v) — L2 thin poset; selected by L4.
- [`formal/Echo.v`](Echo.v) — L3 echo calculus; discipline selected
  by L2.
- [`CLAUDE.md`](../CLAUDE.md) — agent guidance; owner directive
  2026-05-27 (no patching of legacy preservation).
- [`PROOF-NEEDS.md`](../PROOF-NEEDS.md) — proof-debt accounting.
