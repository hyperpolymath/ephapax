<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# `spec/` — Language Specifications

This directory contains three coordinated artefacts:

| File | Purpose | Audience |
|------|---------|----------|
| [`SPEC.md`](SPEC.md) | Concise language spec — types, expressions, typing rules, operational semantics, type safety. ~540 LOC, version-dated. | Implementors who want the rules without exhaustive grammar productions. |
| [`ephapax-spec.md`](ephapax-spec.md) | Comprehensive prose spec — full lexical / syntax / type-system / runtime treatment, organised into PARTS. ~310 LOC. | Readers who want the language explained in narrative form. |
| [`ephapax-v2-grammar.ebnf`](ephapax-v2-grammar.ebnf) | Machine-readable v2 grammar (EBNF). ~750 LOC. | Parser implementors / tooling. |

The two `.md` specs cover overlapping ground from complementary
angles. If they disagree on a rule, **`SPEC.md` is canonical** (it's
the version-stamped reference); `ephapax-spec.md` is the prose
elaboration. Discrepancies should be reported as bugs in
`ephapax-spec.md`.

The `.ebnf` is authoritative for surface syntax. If `SPEC.md` § 4
disagrees with the EBNF, the EBNF is canonical (it's what the parser
actually consumes).

See also:
- [`../docs/specs/DESIGN-DECISIONS.adoc`](../docs/specs/DESIGN-DECISIONS.adoc) — why the spec is what it is
- [`../docs/specs/LANGUAGE-COMPARISON.adoc`](../docs/specs/LANGUAGE-COMPARISON.adoc) — how this differs from Rust, Idris2, Linear Haskell, etc.
- [`../formal/`](../formal/) — Coq mechanization of the typing rules and operational semantics from `SPEC.md` §§5-6.
