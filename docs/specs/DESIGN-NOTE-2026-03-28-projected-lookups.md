<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Design Note: Projected Context Lookups (2026-03-28)

## Problem

Rocq 9.1.1 `congruence`, `discriminate`, and `injection` all fail on
hypotheses of the form `Some (T1, true) = Some (T0, false)` inside complex
inductive proofs (24-case typing rule induction). Works in standalone lemmas.

Root cause: `Coq.Strings.String.length` shadows `Coq.Lists.List.length`
across module boundaries. `Typing.v` exports lemmas with `List.length` in
their types, but `Semantics.v` (importing String) resolves `length` to
`String.length`, making `eapply`/`eassumption` fail silently.

## Solution

Added projected accessors to `Syntax.v`:

```coq
Definition ctx_lookup_ty (G : ctx) (i : var) : option ty := ...
Definition ctx_lookup_flag (G : ctx) (i : var) : option bool := ...
```

These decompose `option (ty * bool)` into simple `option ty` and `option bool`,
which Rocq can discriminate/inject without issue.

Key lemma:

```coq
Lemma ctx_lookup_cons_zero_flag_contra :
  forall (T1 : ty) (G'' : ctx) (T0 : ty),
    ctx_lookup ((T1, true) :: G'') 0 = Some (T0, false) -> False.
```

Uses `f_equal` with functional extraction to get `Some true = Some false`,
then `discriminate` on `option bool` (which works fine).

## Impact

- `flags_only_increase`: **Qed** (was primary blocker)
- `ctx_mark_used_flag_at`, `ctx_mark_used_flag_other`, `ctx_mark_used_ty_other`: all Qed
- T_Let/T_LetLin/T_Case idx=0 cases in `flags_only_increase`: closed via `ctx_lookup_cons_zero_flag_contra`

## Remaining

Same projected approach needed for:
- `ctx_mark_used_types_agree` (1 trivial case)
- `ctx_mark_used_false_preserved` (empty ctx case)
- `typing_ctx_transfer` T_Let/T_LetLin/T_Lam/T_Case (need consumption tracking conjunct)

## Import Order Fix

```coq
(* Typing.v and Semantics.v: import String BEFORE List *)
Require Import Coq.Strings.String. (* Before List so List.length wins *)
Require Import Coq.Lists.List.
```
