<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Ephapax

_ἐφάπαξ — once for all._

**A research language for principled handling of irreversible boundaries in compile-time-memory-safe WebAssembly.**

> ⚠️ **Not to be confused with AffineScript.** These are sibling projects that share zero AST/compiler/type checker. The word "affine" overlaps because both involve substructural logic — that's a logic-family fact, not a project relationship. Full disambiguation: [`nextgen-languages/docs/disambiguation/ephapax-vs-affinescript.md`](https://github.com/hyperpolymath/nextgen-languages/blob/main/docs/disambiguation/ephapax-vs-affinescript.md).

This wiki is the *signpost* — canonical docs live in the repo. Edit [`docs/wikis/`](https://github.com/hyperpolymath/ephapax/tree/main/docs/wikis) in the code repo, not directly in the wiki UI.

---

## Start here

| If you want to… | Go to |
|---|---|
| Understand what Ephapax is | [README.adoc](https://github.com/hyperpolymath/ephapax/blob/main/README.adoc) |
| See the current proof status | [STATUS.adoc](https://github.com/hyperpolymath/ephapax/blob/main/STATUS.adoc) |
| Understand the four-layer redesign | [formal/PRESERVATION-DESIGN.md](https://github.com/hyperpolymath/ephapax/blob/main/formal/PRESERVATION-DESIGN.md) |
| See the per-sublanguage proof debt | [PROOF-NEEDS.md](https://github.com/hyperpolymath/ephapax/blob/main/PROOF-NEEDS.md) |
| See the counterexample that invalidated the old design | [formal/Counterexample.v](https://github.com/hyperpolymath/ephapax/blob/main/formal/Counterexample.v) |
| See architecture decisions | [docs/specs/DESIGN-DECISIONS.adoc](https://github.com/hyperpolymath/ephapax/blob/main/docs/specs/DESIGN-DECISIONS.adoc) |
| See machine-readable state | [.machine_readable/6a2/STATE.a2ml](https://github.com/hyperpolymath/ephapax/blob/main/.machine_readable/6a2/STATE.a2ml) |

---

## What Ephapax is

Ephapax is a research language for **principled handling of irreversible boundaries** — region exits, key erasure, audit trails, database drops, OS deallocations — in compile-time-memory-safe WebAssembly.

Real systems are irreversible. Ephapax gives a disciplined, machine-checkable framework to handle those boundaries responsibly: the type system knows when something has been consumed, when it can never be undone, and when a "once for all" commitment has been made.

### The dyadic design

Ephapax is internally dyadic — two sublanguages, one AST, one Rust crate:

| Sublanguage | Binding | Semantics |
|---|---|---|
| **ephapax-linear** | `let! x = …` | Use **exactly once**; compile error if dropped without explicit discard |
| **ephapax-affine** | `let x = …` | Use **at most once**; implicit drop allowed |

Both compile to [typed-wasm](https://github.com/hyperpolymath/typed-wasm). The choice of sublanguage is a per-declaration annotation.

## Current formal proof status (2026-06-05)

> 🔄 **Foundational redesign in progress.** On 2026-05-26, a verified Coq counterexample ([`formal/Counterexample.v`](https://github.com/hyperpolymath/ephapax/blob/main/formal/Counterexample.v), 5 Qed lemmas) showed that preservation as stated in the legacy typing judgment is **provably false**. The old `Theorem preservation` in `Semantics.v` stays `Admitted` — this is correct. The work is the **four-layer principled redesign**.

The four layers and their current state:

| Layer | Description | Status |
|---|---|---|
| **L1** — Region capabilities | `R_in`, `R_out`, `In r R` threading | Substantially complete; `preservation_l1` proved conditional on L2 effect-typing |
| **L2** — Structural modality | `m : Modality` in `has_type_l1`; `linear_to_affine` | Core landed (PRs #176+#177); `linear_to_affine` Qed, zero axioms; 6 supporting lemmas regressed to Admitted pending Phase D Stages 2–4 |
| **L3** — Echo residue | What was lost at an irreversible step | `preservation_l3` + two companions Qed (conditional); wired into L1 |
| **L4** — Dyadic mode | Project-level mode declaration | Phase A scaffold landed (`formal/L4.v`): `PModeLinear`/`PModeAffine`/`PModeBoundaryMix` + round-trip; definitions only by design |

**Do not** attempt to close `Theorem preservation` in `formal/Semantics.v`. It is provably false. The authoritative do/do-not list is in [`CLAUDE.md`](https://github.com/hyperpolymath/ephapax/blob/main/CLAUDE.md) under "Owner directive 2026-05-27".

## Component map

| Layer | Technology |
|---|---|
| Language core (type checker, parser) | Rust (`ephapax-linear/src/`) |
| Formal proofs | Coq 8.18.0 (`formal/`) — 12 `.v` files |
| ABI verification | Idris2 (`src/abi/Ephapax/`) |
| Wasm codegen | Target: `hyperpolymath/typed-wasm` |
| Governance | 6-verb contractiles; k9-svc self-validation |

## Relationship to other projects

- **[Gossamer](https://github.com/hyperpolymath/gossamer)** — desktop shell; Ephapax is its backend language
- **[AffineScript](https://github.com/hyperpolymath/affinescript)** — **NOT the same project** (see disambiguation above)
- **[typed-wasm](https://github.com/hyperpolymath/typed-wasm)** — shared compile target
- **[IDApTIK](https://github.com/hyperpolymath/idaptik)** — game using Gossamer (Ephapax-backed) for desktop shell

## Governance

- **Licence**: MPL-2.0
- **Machine-readable state**: [`.machine_readable/6a2/`](https://github.com/hyperpolymath/ephapax/tree/main/.machine_readable/6a2/)
- **Contractiles**: 6-verb governance in [`.machine_readable/contractiles/`](https://github.com/hyperpolymath/ephapax/tree/main/.machine_readable/contractiles/)
- **Security policy**: [SECURITY.md](https://github.com/hyperpolymath/ephapax/blob/main/SECURITY.md)
- **Open issues**: [github.com/hyperpolymath/ephapax/issues](https://github.com/hyperpolymath/ephapax/issues)
