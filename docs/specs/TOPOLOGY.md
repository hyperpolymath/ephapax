<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-03-22 -->

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
