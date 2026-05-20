# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq operational semantics; `preservation` **Admitted** (earlier in-file comment claiming "Qed, closed 2026-04-27" was unsubstantiated — `coqc` 8.18.0 rejects the proof script with remaining open goals)
- `formal/Typing.v` — Coq typing rules (clean)
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code
- Coq admitted proofs remaining in `formal/Semantics.v`: 1 (`preservation`)

## What needs proving
- **`preservation`**: Close the remaining ~29 open goals in the proof script at `formal/Semantics.v` L3215–L3339 so the `Qed` lands and the file builds without `Admitted.` Down from 910 open goals (full 35×26 cross-case combinatorial) after introducing the standard preservation pattern (`remember (mu, R, e) as cfg eqn:Hcfg` + symmetric for cfg', then `inversion Hcfg; subst; inversion Hcfg'; subst;` inside each case). The remaining 29 are real diagonal cases — see `formal/PRESERVATION-HANDOFF.md` for the per-case checklist. Supporting lemmas already Qed (`subst_preserves_typing`, `region_env_perm_typing`, `region_add_typing`, `region_shrink_preserves_typing`, `values_dont_step`). The S_Region_Step + T_Region_Active case still blocks on a region-env *weakening* lemma for non-values, which does not yet exist. An earlier ~40-goal diagnostic (PR #104) measured the PRE-`remember-cfg`-pattern state and is superseded.
- **Linear type consumption**: Prove resources with linear types are consumed exactly once across all execution paths (region boundaries, exception handlers)
- **Effect system soundness**: Prove the effect type system correctly tracks side effects and that effect-free terms are truly pure
- **Region safety**: Prove that region-based memory management prevents use-after-free and dangling references across region boundaries
- **Compiler correctness**: Prove the Rust compiler preserves Ephapax semantics (at minimum, type-preserving compilation)

> Note: an earlier version of this list claimed `preservation` was closed at Qed on 2026-04-27 (citing the in-file comment at `formal/Semantics.v` L3328) and that the prior "progress 92%" ROADMAP entry was the only stale item. Both claims were wrong: the cited in-file comment was itself unsubstantiated — `coqc` 8.18.0 rejects the `Qed.` with "Attempt to save an incomplete proof (there are remaining open goals)", which is why `rust-ci.yml`'s "Coq proofs" job has been failing on every push. The honest mark is `Admitted`. `progress` was deleted in the substitution-semantics rewrite and is genuinely not currently formalised in this tree.

## Recommended prover
- **Coq** for the existing soundness chain in `formal/` (already invested in Coq formalization)
- **Idris2** for region linearity and effect system properties (already in use, fits dependent type style)
- **Agda** as backup for metatheory if Coq proof terms become unwieldy

## Priority
- **MEDIUM-HIGH** — Ephapax is a programming language whose core value proposition is linear types and memory safety. `preservation` remains `Admitted` (the immediate soundness blocker is still in place, contrary to the previously-claimed-but-incorrect "closed 2026-04-27" status). The next highest-leverage item is closing the open goals in the `preservation` proof script so the `Qed` lands and the Coq CI gate goes green.
