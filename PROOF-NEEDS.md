# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq operational semantics; `preservation` **Admitted** (earlier in-file comment claiming "Qed, closed 2026-04-27" was unsubstantiated — `coqc` 8.18.0 rejects the proof script with remaining open goals)
- `formal/Typing.v` — Coq typing rules (clean)
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code
- Coq admitted proofs remaining in `formal/Semantics.v`: 1 (`preservation` — 12 open goals, plan below)

## What needs proving
- **`preservation`**: Close the remaining **12 open goals** in `formal/Semantics.v` so the `Qed` lands. Down from 910 at session start (98.7% reduction). Reduction story: 910 → 29 via remember-cfg (PR #102) → 22 via universal-IH revert (PR #106) → 12 via per-case manual closures (PR #116). The remaining 12 are 11 congruence cases (`S_*_Step` variants) + 1 region case (`S_Region_Step + T_Region_Active`).

  **Canonical closure path: `ROADMAP.adoc` § Preservation closure plan** — 5 phases:

  1. **Lemma B (linearity-context invariance for siblings)** — closes the IH-vs-sibling context mismatch blocking the 11 congruence cases. ~3–4 hours.
  2. **Apply Lemma B → close 11 congruence cases** — per-case manual proof scripts (PR #116 pattern). ~2 hours, parallelizable.
  3. **Region-env weakening lemma for non-values** — defines `safe_for_region_weakening` predicate + proves the weakening lemma. 1–2 days, genuine metatheoretic work.
  4. **Apply Phase 3 lemma → close S_Region_Step** — ~1 hour.
  5. **`Admitted.` → `Qed.` + docs sweep** — mechanical, ~1 hour.

  Total: 3 sessions / ~10 hours wall-clock with fan-out. See ROADMAP for full effort estimates and risk-adjusted forecast.

  Supporting lemmas already Qed: `subst_preserves_typing`, `region_env_perm_typing`, `region_add_typing`, `region_shrink_preserves_typing`, `values_dont_step`, and **`step_R_eq_or_touches_region`** (PR #114, the region-invariance lemma used by the per-case closures and required by Phase 2).
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
