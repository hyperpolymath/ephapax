// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Dyadic Discipline Rules Reference
//!
//! This module documents the complete set of rules that differ between
//! the affine (`let`) and linear (`let!`) disciplines. It is a human-readable
//! reference, not executable dispatch logic. The rules are enforced inline
//! at each decision point in the type checker via `CtxEntry::demands_consumption()`.
//!
//! When the decision points grow (effects, contracts, generics), this module
//! should be promoted to executable code. Until then, it serves as the single
//! source of truth for "what does each discipline mean?"
//!
//! # The Dyadic Contract
//!
//! Both disciplines coexist per-binding in the same program. The binding form
//! (`let` vs `let!`) selects the discipline. There is no global mode.
//!
//! # Decision Points
//!
//! ## 1. Scope Exit (binding goes out of scope)
//!
//! | Discipline | Rule | Enforced at |
//! |------------|------|-------------|
//! | **Affine** (`let`) | Unconsumed is OK (implicit drop) | `check_let` — no consumption check (lib.rs) |
//! | **Linear** (`let!`) | Must be consumed — error if not | `check_let_lin` — `!entry.used` → error (lib.rs) |
//! | **Param** | Follows type: linear types must be consumed | `check_lambda`, `check_case` — `demands_consumption()` (lib.rs) |
//!
//! Note: `let!` enforces consumption for ALL types, not just linear types.
//! Writing `let! x: I32 = 42 in ()` is an error. The programmer opted into
//! exactly-once by choosing `let!`.
//!
//! ## 2. Branch Agreement (if/case arms)
//!
//! | Discipline | Rule | Enforced at |
//! |------------|------|-------------|
//! | **Affine** (`let`) | Branches may disagree — unconsuming branch implicitly drops | `check_branch_agreement` — skips if `!demands_consumption()` (lib.rs) |
//! | **Linear** (`let!`) | Branches MUST agree on consumption | `check_branch_agreement` — error if `used` differs (lib.rs) |
//!
//! ## 3. Region Exit (region scope closes)
//!
//! | Discipline | Rule | Enforced at |
//! |------------|------|-------------|
//! | **Affine** (`let`) | Implicitly dropped — arena frees memory | `check_region` — skips if `!demands_consumption()` (lib.rs) |
//! | **Linear** (`let!`) | Must consume before exit — error if not | `check_region` — `RegionLinearNotConsumed` error (lib.rs) |
//!
//! For non-memory resources (file handles, locks), affine implicit drop
//! may be a resource leak. The `ephapax-linear` `AffineChecker` emits
//! `ImplicitDropWarning` for these cases.
//!
//! ## 4. Pattern Wildcards (match arm discards a value)
//!
//! | Discipline | Rule | Enforced at |
//! |------------|------|-------------|
//! | **Affine** (scrutinee was `let`) | Wildcard = implicit drop (OK) | Case vars use `Param` — linear types still demand consumption, but affine scrutinee's components follow type discipline |
//! | **Linear** (scrutinee was `let!`) | Wildcard on linear component = error | Case vars use `Param` — linear types demand consumption via `demands_consumption()` |
//!
//! Note: The desugarer generates case variables with `BindingForm::Param`.
//! The discipline check depends on the component TYPE, not the scrutinee's
//! binding form. This is correct: `let` lets you drop the container, but
//! destructured linear components still follow their type's discipline.
//!
//! ## 5. Effect Resume (future — not yet implemented)
//!
//! | Discipline | Rule | Planned enforcement |
//! |------------|------|---------------------|
//! | **Affine** | No restriction on resume mode | Effect handler checks |
//! | **Linear** | One-shot only (`resume(once)`) when continuation captures linear values | Effect handler checks — `resume(multi)` is type error if linear captures |
//!
//! If a handler doesn't call `resume` (discards continuation), the `finally`
//! clause must consume any captured linear values.
//!
//! # The `demands_consumption()` Method
//!
//! All five decision points route through `CtxEntry::demands_consumption()`:
//!
//! ```text
//! BindingForm::LetBang → true   (always — this is the linear contract)
//! BindingForm::Let     → false  (never — this is the affine contract)
//! BindingForm::Param   → ty.is_linear()  (follows the type)
//! ```
//!
//! This is the single point of truth in the executable code. Everything
//! else in the type checker calls this method and branches on the result.
//!
//! # Correspondence with Formal Artefacts
//!
//! | Rule | EBNF grammar | Coq proof | ephapax-linear checker |
//! |------|-------------|-----------|----------------------|
//! | Scope exit | `grammar/linear.ebnf` §Linear Expressions | `formal/Typing.v` (T_Let, T_LetLin) | `LinearChecker::walk_expr` / `AffineChecker::walk_expr` |
//! | Branch agreement | `grammar/linear.ebnf` §case_expr, §if_expr | `formal/Typing.v` (T_Case) | `check_branch_agreement` in both checkers |
//! | Region exit | `grammar/linear.ebnf` §region_expr | `formal/RegionLinear.idr` (AllLinearsConsumed) | `LinearChecker` region check / `AffineChecker` ImplicitDropWarning |
//! | Wildcards | `grammar/affine.ebnf` §aff_expr (drop permitted) | — | `AffineChecker` allows, `LinearChecker` forbids |
//! | Effect resume | `spec/ephapax-v2-grammar.ebnf` §resume_mode | — (future) | — (future) |
