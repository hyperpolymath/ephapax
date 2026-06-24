# Ephapax Conformance Test Suite

<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

Type system conformance tests for the Ephapax compiler.

## Structure

- `valid/` — Programs that MUST type-check successfully.
- `invalid/` — Programs that MUST be rejected with specific error codes.

## Error Codes

| Code | Category | Description | `DisciplineViolation` variant |
|------|----------|-------------|-------------------------------|
| E001 | Linear | Linear variable not consumed | `WeakeningForbidden` |
| E002 | Linear | Variable used after consumption | `Contraction` |
| E003 | Region | Value escapes its region | (typing-rule `NoRegionInType`) |
| E004 | Region | Linear binding in region not consumed before region exit | `RegionLeakLinear` |
| E005 | Branch | Branches disagree on consumption of a linear variable | `BranchDisagreement` |

Ground-truth source: `DisciplineViolation` enum in `ephapax-linear/src/lib.rs`.

## Running

```bash
just conformance
```
