# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq operational semantics; `preservation` Qed (closed 2026-04-27, zero `Admitted` in this file)
- `formal/Typing.v` — Coq typing rules (clean)
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code
- Coq admitted proofs remaining in `formal/Semantics.v`: 0

## What needs proving
- **Linear type consumption**: Prove resources with linear types are consumed exactly once across all execution paths (region boundaries, exception handlers)
- **Effect system soundness**: Prove the effect type system correctly tracks side effects and that effect-free terms are truly pure
- **Region safety**: Prove that region-based memory management prevents use-after-free and dangling references across region boundaries
- **Compiler correctness**: Prove the Rust compiler preserves Ephapax semantics (at minimum, type-preserving compilation)

> Note: an earlier version of this list included "close `preservation` Admitted" and "complete `progress` proof". `preservation` was closed at Qed on 2026-04-27 (see in-file comment at `formal/Semantics.v` L3328); `progress` was deleted in the substitution-semantics rewrite and is not currently formalised in this tree. The previous "progress 92%" claim is stale.

## Recommended prover
- **Coq** for the existing soundness chain in `formal/` (already invested in Coq formalization)
- **Idris2** for region linearity and effect system properties (already in use, fits dependent type style)
- **Agda** as backup for metatheory if Coq proof terms become unwieldy

## Priority
- **MEDIUM** — Ephapax is a programming language whose core value proposition is linear types and memory safety. With `preservation` closed, the immediate soundness blocker is gone; remaining work is breadth-first (effect system, region safety, compiler correctness) rather than depth-first.
