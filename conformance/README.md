# Ephapax Conformance Test Suite

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

Type system conformance tests for the Ephapax compiler.

## Structure

- `valid/` — Programs that MUST type-check successfully.
- `invalid/` — Programs that MUST be rejected with specific error codes.

## Error Codes

| Code | Category | Description |
|------|----------|-------------|
| E001 | Linear | Variable not consumed |
| E002 | Linear | Variable used after consumption |
| E003 | Region | Value escapes its region |
| E004 | Branch | Branches consume different linear resources |

## Running

```bash
just conformance
```
