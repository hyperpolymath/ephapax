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

## The four orthogonal layers

When working in this repo, the typing system has four layers. Knowing which layer a question touches is the first step in answering it:

| Layer | One-line question to ask |
|---|---|
| **L1 — Region capabilities** | "Does this involve `R_in`, `R_out`, or `In r R`?" |
| **L2 — Structural modality** | "Is this about consumption, weakening, or Linear vs Affine?" |
| **L3 — Echo residue** | "Is this about *what was lost* when an irreversible step fired?" |
| **L4 — Dyadic mode** | "Is this a project-level mode declaration question?" |

Most questions touch exactly one layer. The design rationale is in `formal/PRESERVATION-DESIGN.md`. The verified counterexample that forced the redesign is in `formal/Counterexample.v` (3 lemmas under the legacy judgment + `bad_input_untypable_l1` under the new `has_type_l1`).

**Standing rule**: if a proposed change appears to require a side condition on a compound typing rule (e.g. "the sibling doesn't reference this region"), pause — the four-layer threading should make that side condition *derivable*, not stated.

**Disambiguation reminder**: the names L1/L2/L3/L4 (layer names), `ephapax-linear`/`ephapax-affine` (L2 modes / the Rust crate), and `Linear`/`Affine` as used in echo-types (L3 modes) deliberately overlap because the underlying thin-poset construction is shared. Agents must disambiguate by context.

## Standing reminders

- Formal-proof work touches `formal/Semantics.v` + `formal/TypingL1.v` (Coq) and `src/abi/Ephapax/…/*.idr` (Idris2). Both build oracles are authoritative; `coqc` and `idris2 --check` are the only "is this proved?" answers.
- The legacy preservation closure plan is superseded by `formal/PRESERVATION-DESIGN.md` (four-layer redesign). `formal/PRESERVATION-HANDOFF.md` carries the historical diagnostic record only.
- Ephapax-affine type proofs are **NOT** done — `formal/` mechanises a single legacy judgment + L1's `has_type_l1`; there is no separate mechanised ephapax-affine until L2 + the Linear ⇒ Affine weakening lemma land. See `PRESERVATION-DESIGN.md §12.15`.
- All commits GPG-signed (key `4A03639C1EB1F86C7F0C97A91835A14A2867091E`), email `6759885+hyperpolymath@users.noreply.github.com`. Auto-merge ON for every PR.
