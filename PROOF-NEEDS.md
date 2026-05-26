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

  **Canonical closure path: Path 1 — simultaneous mutual induction** (revised 2026-05-26). The earlier 5-phase plan assumed Lemma B + region-env weakening as independent lemmas; that decomposition's Option 2 ("structural recursion on `Hstep`, ~150 LOC, orthogonal") was found BLOCKED. Counterexample `ELet (ERegion r v_inner) e2` with `e2` referencing `r` shows `T_Let` has no sibling-freedom premise, so the structural-recursion congruence-case rebuild can't retype `e'` at `R'`. See `docs/reports/audit/audit-2026-05-26-lemma-b-option-2-obstacle.md`.

  Current shape (verified by `coqc 8.18` on 2026-05-26): **1 admit in `step_preserves_type` (Semantics.v:4885) + 1 in `step_output_context_eq` aka Lemma B (Semantics.v:5963) + 12 cascading goals in `preservation` (Semantics.v:6572)**. 14 total open, 1 independent variable — the shared S_Region_Step `r=r1` admit mirrored across the two upstream lemmas.

  Phases (re-stated 2026-05-26):

  1. **Mutual induction restructuring**: state `step_preserves_type`, `step_output_context_eq`, and `preservation` as a mutually-recursive trio, sharing IHs. The 2026-05-24 cluster closures (Clusters A, C, most of B) still apply unchanged. ~6-9 hours.
  2. **Cascade Lemma B → preservation's 12 congruence goals** — mechanical wiring once mutual recursion is sound. ~1-2 hours.
  3. **`Admitted.` → `Qed.` + unwind checklist** (this file, ROADMAP.adoc, RUST-SPARK-STANCE.adoc, delete `formal/PRESERVATION-HANDOFF.md`) — ~1 hour.

  Total: **8–12 focused hours wall-clock** (re-revised 2026-05-26 from "~10 hours / 3 sessions with fan-out", which assumed the now-blocked Option 2 + independent region-env weakening). See ROADMAP for full effort estimates.

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
