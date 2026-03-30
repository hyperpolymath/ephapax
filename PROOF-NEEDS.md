# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq operational semantics (4 `Admitted`: context transfer ~line 916, substitution lemma ~1103, and two preservation sub-cases ~1261, ~1318)
- `formal/Typing.v` — Coq typing rules (clean)
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code

## What needs proving
- **Close 4 Admitted in Semantics.v**: Context transfer (ctx_transfer, 15/24 cases done), substitution lemma (subst_lemma), and two preservation sub-cases
- **Type soundness end-to-end**: Complete progress + preservation proof chain (preservation blocked by the Admitted gaps)
- **Linear type consumption**: Prove resources with linear types are consumed exactly once across all execution paths (region boundaries, exception handlers)
- **Effect system soundness**: Prove the effect type system correctly tracks side effects and that effect-free terms are truly pure
- **Region safety**: Prove that region-based memory management prevents use-after-free and dangling references across region boundaries
- **Compiler correctness**: Prove the Rust compiler preserves Ephapax semantics (at minimum, type-preserving compilation)

## Recommended prover
- **Coq** for closing existing Admitted gaps (already invested in Coq formalization)
- **Idris2** for region linearity and effect system properties (already in use, fits dependent type style)
- **Agda** as backup for metatheory if Coq proof terms become unwieldy

## Priority
- **HIGH** — Ephapax is a programming language whose core value proposition is linear types and memory safety. The 4 Admitted gaps in Semantics.v directly undermine the type soundness claim. Closing these is the single highest-priority proof task.
