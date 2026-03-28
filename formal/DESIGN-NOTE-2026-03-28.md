# Design Note: Environment-Leaking Bug and Substitution-Based Fix

**Date**: 2026-03-28
**Author**: Jonathan D.A. Jewell (hyperpolymath)
**Status**: Implemented

## Problem: Environment Leaking in Congruence Rules

The original operational semantics used a runtime environment (`env = list runtime_val`)
in the configuration `(mem * region_env * env * expr)`. Binding reductions (S_Let_Val,
S_App_Fun, S_Case_Inl/Inr) extended the environment, and congruence rules (S_Let_Step,
S_App_Step1/2, etc.) propagated the post-step environment to sibling expressions.

This caused an **environment-leaking bug** where nested binding reductions leaked
environment extensions to sibling sub-expressions, making **preservation genuinely false**.

### Concrete Counterexample

```
let x = (let y = 42 in body) in e2
```

1. Inner step (S_Let_Val): `(mu, R, rho, let y = 42 in body) -> (mu, R, 42::rho, body)`
2. Outer congruence (S_Let_Step): `(mu, R, rho, let x = (let y = 42 in body) in e2) -> (mu, R, 42::rho, let x = body in e2)`
3. Now `e2` runs in `42::rho` — its De Bruijn index 1 points to `42` instead of `rho[0]`
4. `let x = body in e2` is **genuinely ill-typed**: `body`'s context has the extra binding
   that shifts `e2`'s indices, and no typing derivation exists in any context.

## Fix: Substitution-Based Semantics

The configuration was simplified to `(mem * region_env * expr)` — no runtime environment.

Binding reductions now use De Bruijn substitution:
- `S_Let_Val`: `let v in e2 -> subst 0 v e2`
- `S_App_Fun`: `(fn(T) -> body) v -> subst 0 v body`
- `S_Case_Inl`: `case (inl v) e1 e2 -> subst 0 v e1`
- `S_Case_Inr`: `case (inr v) e1 e2 -> subst 0 v e2`

The `S_Var` rule was removed — variables are resolved by substitution at binding sites.

Congruence rules no longer propagate environment changes (there is no environment).

## Impact on Proofs

| Theorem | Before | After |
|---------|--------|-------|
| values_dont_step | Qed | Qed (updated for new config) |
| no_leaks | Qed | Qed (updated for new config) |
| flags_only_increase | — | Qed (new) |
| typing_preserves_bindings | Qed | Qed (unchanged) |
| canonical forms (6) | Qed | Qed (unchanged) |
| memory_safety | Qed | Removed (env-dependent) |
| progress | Qed | Needs rewrite (no env_consistent) |
| preservation | Admitted (env-leak) | Admitted (needs subst lemma + ctx transfer) |

The preservation proof now has a clear path to Qed via:
1. **Substitution lemma**: handles reduction cases
2. **Context transfer lemma**: handles congruence cases
3. **flags_only_increase**: typing only changes used-flags false→true

## Key Insight

The previous preservation failure was not a proof technique limitation — it was a
**soundness bug in the semantics**. The substitution-based semantics is the standard
formulation for De Bruijn metatheory and makes preservation provable via well-known
techniques (substitution lemma + context weakening).
