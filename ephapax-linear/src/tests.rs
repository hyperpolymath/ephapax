// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Tests for the dual discipline checkers.
//!
//! Many tests run the SAME expression through both checkers to demonstrate
//! where the linear and affine grammars diverge.

use super::*;
use ephapax_syntax::{BaseTy, Expr, ExprKind, Literal, Span, Ty};

/// Helper: create an expression with a dummy span.
fn e(kind: ExprKind) -> Expr {
    Expr::new(kind, Span::dummy())
}

/// Helper: unit literal.
fn unit() -> Expr {
    e(ExprKind::Lit(Literal::Unit))
}

/// Helper: variable reference.
fn var(name: &str) -> Expr {
    e(ExprKind::Var(name.into()))
}

/// Helper: I32 literal.
fn i32_lit(n: i32) -> Expr {
    e(ExprKind::Lit(Literal::I32(n)))
}

// =========================================================================
// Contraction (both grammars reject)
// =========================================================================

#[test]
fn both_reject_contraction() {
    // let! x = String.new@r("hello") in (x, x)
    // Using x twice is contraction — forbidden in both disciplines.
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::LetLin {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(e(ExprKind::Pair {
                left: Box::new(var("x")),
                right: Box::new(var("x")),
            })),
        })),
    });

    let mut linear = LinearChecker::new();
    let result = linear.check(&expr);
    assert!(result.is_err(), "linear must reject contraction");
    let violations = result.unwrap_err();
    assert!(
        violations.iter().any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
        "must contain Contraction violation"
    );

    let mut affine = AffineChecker::new();
    let result = affine.check(&expr);
    assert!(result.is_err(), "affine must reject contraction");
    let violations = result.unwrap_err();
    assert!(
        violations.iter().any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
        "must contain Contraction violation"
    );
}

// =========================================================================
// Weakening (linear rejects, affine allows)
// =========================================================================

#[test]
fn linear_rejects_unconsumed_let_bang() {
    // let! x = 42 in ()
    // x is never consumed — linear rejects (WeakeningForbidden)
    let expr = e(ExprKind::LetLin {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(unit()),
    });

    let mut checker = LinearChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(violations.iter().any(|v| matches!(
        v,
        DisciplineViolation::WeakeningForbidden { name } if name == "x"
    )));
}

#[test]
fn affine_allows_unconsumed_let() {
    // let x = 42 in ()
    // x is never consumed — affine allows (implicit drop)
    let expr = e(ExprKind::Let {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(unit()),
    });

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_ok(), "affine must allow unconsumed let");
}

#[test]
fn affine_still_enforces_let_bang() {
    // let! x = 42 in ()
    // Even in affine grammar, let! demands exactly-once
    let expr = e(ExprKind::LetLin {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(unit()),
    });

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err(), "affine must enforce let! exactly-once");
}

// =========================================================================
// Drop (linear rejects, affine allows)
// =========================================================================

#[test]
fn linear_rejects_drop() {
    let expr = e(ExprKind::Drop(Box::new(i32_lit(42))));

    let mut checker = LinearChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(violations.iter().any(|v| matches!(v, DisciplineViolation::DropForbidden)));
}

#[test]
fn affine_allows_drop() {
    let expr = e(ExprKind::Drop(Box::new(i32_lit(42))));

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_ok(), "affine must allow drop");
}

// =========================================================================
// Branch agreement (linear requires, affine relaxes)
// =========================================================================

#[test]
fn linear_rejects_branch_disagreement() {
    // let! x = String.new@r("hello") in
    //   if true then x else ()
    // Left branch consumes x, right doesn't — linear rejects
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::LetLin {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(e(ExprKind::If {
                cond: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
                then_branch: Box::new(var("x")),
                else_branch: Box::new(unit()),
            })),
        })),
    });

    let mut checker = LinearChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(
        violations.iter().any(|v| matches!(v, DisciplineViolation::BranchDisagreement { .. })),
        "linear must reject branch disagreement"
    );
}

#[test]
fn affine_allows_branch_disagreement() {
    // Same program as above but through affine checker — should pass
    // (unconsumed branch implicitly drops x)
    let expr = e(ExprKind::Let {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(e(ExprKind::If {
            cond: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(var("x")),
            else_branch: Box::new(unit()),
        })),
    });

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_ok(), "affine must allow branch disagreement");
}

// =========================================================================
// let for linear types (linear grammar restricts)
// =========================================================================

#[test]
fn linear_rejects_let_for_linear_type() {
    // let x: String@r = ... in x
    // In linear grammar, linear types MUST use let!
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(var("x")),
        })),
    });

    let mut checker = LinearChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(violations.iter().any(|v| matches!(
        v,
        DisciplineViolation::LetForLinearType { name } if name == "x"
    )));
}

#[test]
fn affine_allows_let_for_linear_type() {
    // Same program in affine — let may bind any type
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(var("x")),
        })),
    });

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_ok(), "affine must allow let for linear types");
}

// =========================================================================
// Region leak (linear errors, affine warns)
// =========================================================================

#[test]
fn linear_errors_on_region_leak() {
    // region r { let! x = String.new@r("hello") in () }
    // x not consumed before region exit — linear error
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::LetLin {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(unit()),
        })),
    });

    let mut checker = LinearChecker::new();
    let result = checker.check(&expr);
    assert!(result.is_err());
    // Should have both WeakeningForbidden (from let!) and RegionLeakLinear
    let violations = result.unwrap_err();
    assert!(violations.iter().any(|v| matches!(
        v,
        DisciplineViolation::WeakeningForbidden { .. }
    )));
}

#[test]
fn affine_warns_on_region_implicit_drop() {
    // region r { let x: String@r = String.new@r("hello") in () }
    // x implicitly dropped at region exit — affine warns
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(unit()),
        })),
    });

    let mut checker = AffineChecker::new();
    let result = checker.check(&expr);
    // Warnings are violations too, but is_warning() is true
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(
        violations.iter().all(|v| v.is_warning()),
        "affine region leak should be a warning, not an error"
    );
}

// =========================================================================
// Unified entry point
// =========================================================================

#[test]
fn check_expr_unified_api() {
    let consumed = e(ExprKind::LetLin {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(var("x")),
    });

    assert!(check_expr(&consumed, Discipline::Linear).is_ok());
    assert!(check_expr(&consumed, Discipline::Affine).is_ok());
}

#[test]
fn consumed_binding_passes_both() {
    // let! x = 42 in x — consumed exactly once, both pass
    let expr = e(ExprKind::LetLin {
        name: "x".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(42)),
        body: Box::new(var("x")),
    });

    let mut linear = LinearChecker::new();
    assert!(linear.check(&expr).is_ok());

    let mut affine = AffineChecker::new();
    assert!(affine.check(&expr).is_ok());
}
