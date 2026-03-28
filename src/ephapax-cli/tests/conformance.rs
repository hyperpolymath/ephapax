// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Conformance test suite for the Ephapax language specification.
//!
//! Tests critical language invariants from the spec:
//! - Dyadic linearity (let = affine, let! = linear)
//! - Region-based memory safety
//! - Type system soundness properties
//!
//! Each test is tagged with the spec section it validates.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;

fn check(source: &str) -> Result<ephapax_syntax::Ty, String> {
    let expr = parse(source).map_err(|es| {
        es.into_iter()
            .map(|e| format!("{e}"))
            .collect::<Vec<_>>()
            .join("; ")
    })?;
    let mut tc = TypeChecker::new();
    tc.check(&expr).map_err(|e| format!("{e:?}"))
}

// =========================================================================
// SPEC: Dyadic linearity — let vs let!
// =========================================================================

/// SPEC 1.1: `let` bindings are affine — may be used 0 or 1 times
#[test]
fn spec_let_affine_unused_ok() {
    // let binding unused — affine allows this
    assert!(check("let x = 42 in 0").is_ok());
}

/// SPEC 1.2: `let` bindings are affine — used once is fine
#[test]
fn spec_let_affine_used_once_ok() {
    assert!(check("let x = 42 in x").is_ok());
}

/// SPEC 1.3: `let!` bindings are linear — must be used exactly once
#[test]
fn spec_let_bang_linear_used_once_ok() {
    assert!(check("let! x = 42 in x").is_ok());
}

/// SPEC 1.4: `let!` bindings are linear — unused is rejected
#[test]
fn spec_let_bang_linear_unused_rejected() {
    assert!(check("let! x = 42 in 0").is_err());
}

// =========================================================================
// SPEC: Type system basics
// =========================================================================

/// SPEC 2.1: Base types check correctly
#[test]
fn spec_base_types() {
    assert!(check("42").is_ok()); // I32
    assert!(check("true").is_ok()); // Bool
    assert!(check("false").is_ok()); // Bool
    assert!(check("()").is_ok()); // Unit
}

/// SPEC 2.2: If branches must agree on type
#[test]
fn spec_if_branch_agreement() {
    assert!(check("if true then 1 else 2").is_ok());
    assert!(check("if true then 1 else true").is_err());
}

/// SPEC 2.3: Function application type checks
#[test]
fn spec_function_application() {
    assert!(check("(fn(x: I32) -> x)(42)").is_ok());
}

/// SPEC 2.4: Function application type mismatch
#[test]
fn spec_function_application_mismatch() {
    assert!(check("(fn(x: I32) -> x)(true)").is_err());
}

// =========================================================================
// SPEC: Products
// =========================================================================

/// SPEC 3.1: Pair construction
#[test]
fn spec_pair() {
    assert!(check("(1, 2)").is_ok());
    assert!(check("(true, 42)").is_ok());
}

/// SPEC 3.2: Pair projections — fst() and snd() keyword syntax
#[test]
fn spec_projections() {
    assert!(check("fst((1, 2))").is_ok());
    assert!(check("snd((1, 2))").is_ok());
}

/// SPEC 3.3: Pair projections — .0 and .1 postfix syntax
#[test]
fn spec_projections_dot() {
    assert!(check("(1, 2).0").is_ok());
    assert!(check("(1, 2).1").is_ok());
}

// =========================================================================
// SPEC: Sums
// =========================================================================

/// SPEC 4.1: Sum injection
#[test]
fn spec_sum_injection() {
    assert!(check("inl[I32](true)").is_ok());
    assert!(check("inr[Bool](42)").is_ok());
}

// =========================================================================
// SPEC: Explicit resource management
// =========================================================================

/// SPEC 5.1: Drop only allowed on linear types — non-linear rejected
#[test]
fn spec_drop_nonlinear_rejected() {
    assert!(check("drop(42)").is_err());
}

/// SPEC 5.2: Copy only allowed on non-linear types — non-linear accepted
#[test]
fn spec_copy_nonlinear_ok() {
    assert!(check("copy(42)").is_ok());
}

// =========================================================================
// SPEC: Variable scoping
// =========================================================================

/// SPEC 6.1: Unbound variable is rejected
#[test]
fn spec_unbound_variable() {
    assert!(check("x").is_err());
}

/// SPEC 6.2: Variable in scope
#[test]
fn spec_bound_variable() {
    assert!(check("let x = 42 in x").is_ok());
}

/// SPEC 6.3: Unbound variable in outer scope
#[test]
fn spec_variable_scope_limited() {
    // z is never bound
    assert!(check("let y = 1 in z").is_err());
}
