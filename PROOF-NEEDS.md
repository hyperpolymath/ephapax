# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq operational semantics
  - `step_preserves_type` — **Qed** (closed 2026-05-26 via [Path 3 at-pre helper](#path-3-at-pre-helper))
  - `step_output_context_eq` (Lemma B) — **Qed** (closed 2026-05-26 via Path 3)
  - `step_preserves_type_at_pre` — **Admitted** (NEW helper; 8 of 35 cases remain admitted, falls through to `all: admit.` catch-all)
  - `step_output_context_eq_at_pre` — **Admitted** (NEW helper; analogous shape)
  - `preservation` — **Admitted** (12 cascading goals — separate problem, region-env weakening for non-values)
- `formal/Typing.v` — Coq typing rules (clean)
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code

## Path 3 at-pre helper

The 2026-05-26 Path-1 (mutual induction) plan was superseded by a simpler approach: introduce two NEW helper lemmas whose typings are at the SAME pre-step env R (not R/R'). The key insight: in the S_Region_Step cross-case `Hte = T_Region_Active` × `Hte' = T_Region` with `R0' = remove_first r R0` and `r = r1`, the body's typing under `r :: R0'` is membership-equivalent to `R0` (via `remove_first_then_cons_membership_eq`). After perm transport, both bodies are typed at R0 — the at-pre helper concludes type/output-context equality.

The at-pre helpers' S_Region_Step case is structurally simpler than the original because `In r R0` (from S_Region_Step's premise) FORCES `T_Region_Active` on both sides — the problematic cross-case vanishes by contradiction.

Most of the helpers' OTHER cases were closed by copying step_preserves_type's and step_output_context_eq's tactic blocks verbatim (patterns use `?R`/`?R'` polymorphically and match at-pre framing trivially). What remains in each helper is the per-goal cases (~8 of 35), pending case-by-case closure.

## What needs proving
- **`step_preserves_type_at_pre`**: Close the remaining ~8 admitted cases (the per-goal cases of step_preserves_type's structure that need explicit blocks: S_StringConcat_Step2, S_Let_Step, S_LetLin_Step, S_App_Step2, S_If_Step, S_Pair_Step1, S_Pair_Step2, S_Case_Step). Each ~30 LOC, ported from step_preserves_type's "Per-goal" section (lines 5033-5562). Estimated 2-3h.
- **`step_output_context_eq_at_pre`**: Close ~11 remaining admitted cases (the per-goal cases + S_Region_Step). Patterns parallel step_output_context_eq's body. Estimated 2-3h.
- **`preservation`**: Close the remaining **12 open goals** — the RIGHT branch (R' = remove_first r R) sub-cases of each congruence step rule. These need a **region-env weakening for non-values** lemma that doesn't follow trivially from current infrastructure. Per the handoff doc, this is a deeper problem: when a binder steps to exit region r, the sibling expression might still mention r and not be typeable at the post-step R'. Closing requires either (a) a strengthened type invariant preventing such configurations, (b) a weakened preservation statement, or (c) a region-env weakening helper that case-analyses on the sibling's syntactic shape. Estimated 4-8h.

  Reduction story (910 → 12): 910 via remember-cfg (PR #102) → 22 via universal-IH revert (PR #106) → 12 via per-case manual closures (PR #116). The 2026-05-26 Path-3 work closed the SAME structural admit shared across step_preserves_type:4885 and step_output_context_eq:5963 (the `S_Region_Step` `r = r1` "exited from inside" case) by introducing two at-pre helpers and using `region_env_perm_typing` to bridge. The 12 cascading goals in `preservation` remain — they're a SEPARATE structural problem (region-env weakening), not the same shared admit.

  Total focused wall-clock to full Qed: **~6-12h** (depending on the depth of the preservation region-env weakening fix).

  Supporting lemmas already Qed: `subst_preserves_typing`, `region_env_perm_typing`, `region_add_typing`, `region_shrink_preserves_typing`, `values_dont_step`, **`step_R_eq_or_touches_region`** (PR #114), and now **`step_preserves_type`** + **`step_output_context_eq`** (closed 2026-05-26 via at-pre helpers).
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
