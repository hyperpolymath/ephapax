<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# CLAUDE.md — Ephapax repo agent guidance

## 🚨 Disambiguation (read first)

**This repo is `hyperpolymath/ephapax`.** It is **NOT** `hyperpolymath/affinescript`.

| | This repo | NOT this repo |
|---|---|---|
| Name | **Ephapax** | AffineScript |
| Path | `hyperpolymath/ephapax` | `hyperpolymath/affinescript` |
| File extension | `.eph` | `.affine` (plus face dialects) |
| Build | `Cargo.toml` at root | `dune-project` at root |
| Type checker | `ephapax-linear/src/{linear,affine}.rs` (Rust) | `lib/borrow.ml` (OCaml) |
| Proofs | `formal/Semantics.v` (Coq), `src/abi/Ephapax/…` (Idris2) | None mechanized; `lib/borrow.ml` only |

**Internal naming trap.** Ephapax itself is dyadic. Inside this repo:
- **ephapax-linear** = strict, formally-verified core.
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

Structured project metadata lives in `.machine_readable/6a2/`:

- `STATE.a2ml` — current project state and progress.
- `META.a2ml` — architecture decisions and development practices.
- `ECOSYSTEM.a2ml` — position in the ecosystem and related projects.
- `AGENTIC.a2ml` — AI agent interaction patterns (also carries an `@disambiguation` block).
- `NEUROSYM.a2ml` — neurosymbolic integration config.
- `PLAYBOOK.a2ml` — operational runbook.

## Standing reminders

- Formal-proof work touches `formal/Semantics.v` (Coq) and `src/abi/Ephapax/…/*.idr` (Idris2). Both build oracles are authoritative; `coqc` and `idris2 --check` are the only "is this proved?" answers.
- Preservation closure plan: see `ROADMAP.adoc` § "Preservation closure plan" and `formal/PRESERVATION-HANDOFF.md`.
- All commits GPG-signed (key `4A03639C1EB1F86C7F0C97A91835A14A2867091E`), email `6759885+hyperpolymath@users.noreply.github.com`. Auto-merge ON for every PR.
