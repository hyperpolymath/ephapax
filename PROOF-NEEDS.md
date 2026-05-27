# Proof Requirements

## Current state
- `formal/Syntax.v` — Coq formalization of Ephapax syntax (clean)
- `formal/Semantics.v` — Coq legacy operational semantics; `preservation` **Admitted** (12 open goals; superseded by L1 redesign — see `formal/PRESERVATION-DESIGN.md`)
- `formal/Typing.v` — Coq typing rules, legacy (clean)
- `formal/TypingL1.v` — **L2** Coq typing rules: `has_type_l1` indexed by `m : Modality ∈ {Linear, Affine}`. 21 modality-polymorphic constructors + 3 mode-split rule pairs (T_Lam / T_Case / T_If Linear vs Affine). `linear_to_affine` **Qed (zero axioms)**. Mode-split mechanises the PRESERVATION-DESIGN.md §5 distinction.
- `formal/Modality.v` — K-free `Modality` datatype + `modality_le` thin poset + `_refl`/`_trans`/`_prop` lemmas. Mirrors `echo-types/proofs/agda/EchoLinear.agda:75-101`.
- `formal/Semantics_L1.v` — L1 operational semantics; `preservation_l1` Admitted under `forall m : Modality, ...`. Six supporting lemmas L2-β regressed (bullet-structure rewrite needed for the new Affine-only constructors).
- `formal/TypingL2.v` — thin re-indexing wrapper: `has_type_l2 m R G e T R' G' := L2_lift_l1 m (TypingL1.has_type_l1 m ...)`. `weaken_modality` dispatches through `TypingL1.linear_to_affine`.
- `formal/Echo.v` — **L3** echo residue scaffold (`Mode + LEcho + decoration-commuting weakening + EchoR + no-section irreversibility`).
- `formal/Counterexample.v` — `bad_input_untypable_l1 : forall m, ~ has_type_l1 m ...` Qed (regression witness under both modes).
- `src/formal/Ephapax/Formal/RegionLinear.idr` — Idris2 region-based linearity proof (explicitly states "REAL proof — not believe_me, not assert_total")
- 17 Idris2 files across formal verification layer
- No `believe_me`, `sorry`, or `assert_total` in Idris2 source code
- Coq Admitted proofs:
  - `formal/Semantics.v` `preservation` (legacy, 12 open goals — superseded but kept for back-compat)
  - `formal/Semantics_L1.v` `preservation_l1` (forall m; both Linear and Affine branches Admitted post-L2)
  - 6 L1 supporting lemmas in `Semantics_L1.v` Admitted as L2-β follow-up (region_shrink_preserves_typing_l1_gen, typing_preserves_bindings_l1, unrestricted_flag_unchanged_l1, shift_typing_gen_l1, subst_typing_gen_l1)

## What needs proving

### L2-β follow-up (post-PR #176)
- **6 L1 supporting lemmas in `Semantics_L1.v`** — bullet-structure rewrite of the `induction Htype` proofs to account for the 3 new Affine-only constructors (T_Lam_L1_Affine, T_Case_L1_Affine, T_If_L1_Affine). Each restoration adds 3 `discriminate` dispatches on the `Linear = Affine` equality and re-aligns case bullets. Mechanical; ~2-3 hours.
- **`preservation_l1` body** under `forall m`: Linear branch is the old partial proof (12 admits in R-weakening territory); Affine branch needs the supporting lemmas above plus mode-aware handling for T_Lam_Affine / T_Case_Affine / T_If_Affine. Estimated 3-4 sessions once the supporting lemmas are restored.

### Legacy preservation
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
