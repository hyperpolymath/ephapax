<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-05-27 (post-counterexample doctrine landing) -->

> ## Post-counterexample doctrine — read before editing this file
>
> This TOPOLOGY map predates the 2026-05-26 counterexample landing in
> parts of its system architecture diagram. The canonical *current*
> architecture lives in:
>
> - [`STATUS.adoc`](STATUS.adoc) — past/present/future map
> - [`formal/PRESERVATION-DESIGN.md`](formal/PRESERVATION-DESIGN.md) — four-layer architecture
> - [`PROOF-NEEDS.md`](PROOF-NEEDS.md) — per-sublanguage proof debt
> - [`CLAUDE.md`](CLAUDE.md) — agent guidance + owner directive 2026-05-27
>
> ### Layer mapping (formal/ contents post-2026-05-27)
>
> | Layer | Concern | File(s) | Status |
> |---|---|---|---|
> | **L1** | Region capabilities + capability environment threading | `formal/TypingL1.v` + `formal/Semantics_L1.v` | judgment 100%, semantics 15 Qed / 9 admits (L2-integration debt) |
> | **L2** | Structural modality (Linear vs Affine) | `formal/Modality.v` + `m : Modality` in `has_type_l1` | core landed, `linear_to_affine` Qed with zero axioms |
> | **L3** | Echo / residue (irreversibility evidence) | `formal/Echo.v` + upstream `hyperpolymath/echo-types` | calculus done (12 Qed), wiring into typing pending |
> | **L4** | Dyadic interaction semantics | (none yet) | design in `PRESERVATION-DESIGN.md §7` |
> | 🛑 | Legacy `formal/Semantics.v` + `formal/Typing.v` | archaeology | preservation provably false — see `formal/Counterexample.v` |

# ephapax (selur) — Project Topology

## System Architecture

```
                        ┌─────────────────────────────────────────┐
                        │              AERIE SUITE                │
                        │        (Orchestration Layer)            │
                        └───────────────────┬─────────────────────┘
                                            │
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │           SELUR (IPC SEAL)              │
                        │    (Wait-free communication, FFI)       │
                        └──────────┬───────────────────┬──────────┘
                                   │                   │
                                   ▼                   ▼
                        ┌───────────────────────┐  ┌────────────────────────────────┐
                        │  ZIG IMPLEMENTATION   │  │  IDRIS2 ABI                    │
                        │ - Memory Safety       │  │ - Dependent Type Proofs        │
                        │ - C ABI Bridge        │  │ - Layout Verification          │
                        └───────────────────────┘  └────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │          REPO INFRASTRUCTURE            │
                        │  ABI-FFI Standards  .machine_readable/   │
                        │  Aerie Component    IndieWeb2 Bastion   │
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
CORE COMPONENT (SELUR)
  IPC Seal Logic                    ████████░░  80%    Wait-free primitives refined
  Zig FFI Implementation            ██████████ 100%    Stable C ABI bridge
  Idris2 ABI (Proofs)               ██████████ 100%    Type-level layout verified

REPO INFRASTRUCTURE
  ABI-FFI Standard                  ██████████ 100%    Compliance verified
  .machine_readable/                ██████░░░░  60%    STATE tracking in progress
  Aerie Integration                 ██████████ 100%    Component verified in Aerie

─────────────────────────────────────────────────────────────────────────────
OVERALL:                            ████████░░  ~80%   Component stable, repo refining
```

## Key Dependencies

```
Idris2 ABI ──────► Zig FFI ──────► Aerie (Vörðr) ──────► IPC Flow
```

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
