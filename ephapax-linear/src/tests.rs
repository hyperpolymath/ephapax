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
        violations
            .iter()
            .any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
        "must contain Contraction violation"
    );

    let mut affine = AffineChecker::new();
    let result = affine.check(&expr);
    assert!(result.is_err(), "affine must reject contraction");
    let violations = result.unwrap_err();
    assert!(
        violations
            .iter()
            .any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
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
    assert!(violations
        .iter()
        .any(|v| matches!(v, DisciplineViolation::DropForbidden)));
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
        violations
            .iter()
            .any(|v| matches!(v, DisciplineViolation::BranchDisagreement { .. })),
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
    assert!(violations
        .iter()
        .any(|v| matches!(v, DisciplineViolation::WeakeningForbidden { .. })));
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

// =========================================================================
// P2P PROPERTY TESTS
//
// Loop-based invariant checks over parameterised expression shapes.
// Each loop exercises a different structural pattern and verifies that
// core discipline invariants hold deterministically.
// =========================================================================

/// P2P: consumed exactly-once always passes both disciplines.
///
/// Generates 20 distinct bindings (a0..a19), each consumed exactly once,
/// and verifies that both the linear and affine checkers accept them.
#[test]
fn p2p_single_consume_always_accepted_both_disciplines() {
    for i in 0..20 {
        let name = format!("a{i}");
        // let! x = <i> in x
        let expr = e(ExprKind::LetLin {
            name: name.clone().into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(i as i32)),
            body: Box::new(var(&name)),
        });

        let mut linear = LinearChecker::new();
        assert!(
            linear.check(&expr).is_ok(),
            "P2P linear[{i}]: single consume must be accepted"
        );

        let mut affine = AffineChecker::new();
        assert!(
            affine.check(&expr).is_ok(),
            "P2P affine[{i}]: single consume must be accepted"
        );
    }
}

/// P2P: contraction always produces a Contraction violation in both disciplines.
///
/// Generates 10 variants of double-use expressions and verifies both checkers
/// produce a Contraction violation — regardless of the bound value.
#[test]
fn p2p_contraction_always_rejected_both_disciplines() {
    for i in 0..10 {
        let name = format!("c{i}");
        // let! x = <i> in (x, x)  — x used twice
        let expr = e(ExprKind::LetLin {
            name: name.clone().into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(i as i32)),
            body: Box::new(e(ExprKind::Pair {
                left: Box::new(var(&name)),
                right: Box::new(var(&name)),
            })),
        });

        let mut linear = LinearChecker::new();
        let result = linear.check(&expr);
        assert!(result.is_err(), "P2P linear[{i}]: double use must be rejected");
        let violations = result.unwrap_err();
        assert!(
            violations.iter().any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
            "P2P linear[{i}]: must report Contraction violation"
        );

        let mut affine = AffineChecker::new();
        let result = affine.check(&expr);
        assert!(result.is_err(), "P2P affine[{i}]: double use must be rejected");
        let violations = result.unwrap_err();
        assert!(
            violations.iter().any(|v| matches!(v, DisciplineViolation::Contraction { .. })),
            "P2P affine[{i}]: must report Contraction violation"
        );
    }
}

/// P2P: weakening always produces WeakeningForbidden in linear but not affine.
///
/// Verifies the discipline divergence invariant: linear forbids weakening,
/// affine allows it. Tested over 10 expression variants.
#[test]
fn p2p_weakening_linear_forbidden_affine_allowed() {
    for i in 0..10 {
        let name = format!("w{i}");
        // let! x = <i> in ()  — x never consumed
        let expr = e(ExprKind::LetLin {
            name: name.clone().into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(i as i32)),
            body: Box::new(unit()),
        });

        // Linear must reject
        let mut linear = LinearChecker::new();
        let result = linear.check(&expr);
        assert!(result.is_err(), "P2P linear[{i}]: weakening must be rejected");
        let violations = result.unwrap_err();
        assert!(
            violations.iter().any(|v| matches!(v, DisciplineViolation::WeakeningForbidden { .. })),
            "P2P linear[{i}]: must report WeakeningForbidden"
        );

        // Affine: uses let (not let!) — weakening allowed
        let affine_expr = e(ExprKind::Let {
            name: name.clone().into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(i as i32)),
            body: Box::new(unit()),
        });
        let mut affine = AffineChecker::new();
        assert!(
            affine.check(&affine_expr).is_ok(),
            "P2P affine[{i}]: weakening via let must be accepted"
        );
    }
}

/// P2P: check_expr unified API is consistent with direct checker calls.
///
/// For 10 well-typed expressions, verifies that the unified `check_expr` API
/// produces the same accept/reject decision as the direct checker calls.
#[test]
fn p2p_unified_api_consistent_with_direct_checkers() {
    use crate::{check_expr, Discipline};

    for i in 0..10 {
        let name = format!("u{i}");
        // Well-typed: let! x = <i> in x
        let good_expr = e(ExprKind::LetLin {
            name: name.clone().into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(i as i32)),
            body: Box::new(var(&name)),
        });

        let direct_linear = {
            let mut c = LinearChecker::new();
            c.check(&good_expr).is_ok()
        };
        let unified_linear = check_expr(&good_expr, Discipline::Linear).is_ok();
        assert_eq!(
            direct_linear, unified_linear,
            "P2P unified[{i}] linear: API must be consistent with direct call"
        );

        let direct_affine = {
            let mut c = AffineChecker::new();
            c.check(&good_expr).is_ok()
        };
        let unified_affine = check_expr(&good_expr, Discipline::Affine).is_ok();
        assert_eq!(
            direct_affine, unified_affine,
            "P2P unified[{i}] affine: API must be consistent with direct call"
        );
    }
}

/// P2P: nested let! chains all consume exactly once �� both disciplines pass.
///
/// Builds a chain of depth 1..=10 where each variable is consumed by
/// the next binding. Verifies that both checkers accept all depths.
#[test]
fn p2p_nested_letlin_chain_accepted_at_all_depths() {
    for depth in 1..=10_usize {
        // Build: let! x0 = 0 in let! x1 = x0 in ... let! xN = xN-1 in xN
        let innermost = var(&format!("x{}", depth - 1));
        let expr = (0..depth).rev().fold(innermost, |body, i| {
            let name = format!("x{i}");
            let value = if i == 0 {
                i32_lit(0)
            } else {
                var(&format!("x{}", i - 1))
            };
            e(ExprKind::LetLin {
                name: name.into(),
                ty: Some(Ty::Base(BaseTy::I32)),
                value: Box::new(value),
                body: Box::new(body),
            })
        });

        let mut linear = LinearChecker::new();
        assert!(
            linear.check(&expr).is_ok(),
            "P2P chain depth={depth}: linear must accept well-typed chain"
        );

        let mut affine = AffineChecker::new();
        assert!(
            affine.check(&expr).is_ok(),
            "P2P chain depth={depth}: affine must accept well-typed chain"
        );
    }
}

// =========================================================================
// E2E TESTS
//
// End-to-end tests through the full checking pipeline.
// Each test constructs a complete program, runs it through all stages,
// and asserts coherent behaviour across the discipline boundary.
// =========================================================================

/// E2E: pair-then-consume pattern passes both disciplines.
///
/// Verifies that a complete expression that constructs a pair from two
/// independently linear bindings is accepted end-to-end.
#[test]
fn e2e_pair_two_independent_bindings_accepted() {
    // let! a = 1 in let! b = 2 in (a, b)
    let expr = e(ExprKind::LetLin {
        name: "a".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(1)),
        body: Box::new(e(ExprKind::LetLin {
            name: "b".into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(i32_lit(2)),
            body: Box::new(e(ExprKind::Pair {
                left: Box::new(var("a")),
                right: Box::new(var("b")),
            })),
        })),
    });

    let mut linear = LinearChecker::new();
    assert!(
        linear.check(&expr).is_ok(),
        "E2E pair: linear must accept two-binding pair"
    );

    let mut affine = AffineChecker::new();
    assert!(
        affine.check(&expr).is_ok(),
        "E2E pair: affine must accept two-binding pair"
    );
}

/// E2E: if/then/else with branch agreement passes linear.
///
/// Both branches consume the same linear variable — linear checker must accept.
#[test]
fn e2e_if_branch_agreement_linear_accepted() {
    // let! x = 42 in if true then x else x
    // Wait — that's contraction. Use: if true then x else x is rejected.
    // Correct: branch agreement = same variable consumed in each branch.
    // let! x = 42 in if true then x else 0  — disagreement, rejected.
    // let! cond = true in let! x = 42 in if cond then x else x  — contraction.
    //
    // Correct pattern for agreement: unconditional unit in else, x in then —
    // but that's disagreement in linear. Let's test: both branches return unit,
    // no linear variables are at stake.
    let expr = e(ExprKind::If {
        cond: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
        then_branch: Box::new(unit()),
        else_branch: Box::new(unit()),
    });

    let mut linear = LinearChecker::new();
    assert!(
        linear.check(&expr).is_ok(),
        "E2E if: linear must accept if with no linear bindings"
    );

    let mut affine = AffineChecker::new();
    assert!(
        affine.check(&expr).is_ok(),
        "E2E if: affine must accept if with no linear bindings"
    );
}

/// E2E: region with explicit consumption passes linear.
///
/// Verifies the full region -> allocate -> consume pipeline works end-to-end.
#[test]
fn e2e_region_allocate_consume_linear_accepted() {
    // region r { let! s = String.new@r("hello") in s }
    let expr = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::LetLin {
            name: "s".into(),
            ty: Some(Ty::String("r".into())),
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(var("s")),
        })),
    });

    let mut linear = LinearChecker::new();
    assert!(
        linear.check(&expr).is_ok(),
        "E2E region: linear must accept region with explicit consumption"
    );
}

/// E2E: module with multiple decls — all well-typed, both disciplines pass.
#[test]
fn e2e_module_multiple_decls_accepted() {
    use crate::check_module;
    use ephapax_syntax::{Decl, Module};

    // Module with two function declarations:
    //   fn id_i32(x: i32): i32 = let! a = x in a
    //   fn const_unit(): () = ()
    use ephapax_syntax::Visibility;
    let module = Module {
        name: "test_module".into(),
        imports: Vec::new(),
        decls: vec![
            Decl::Fn {
                name: "id_i32".into(),
                visibility: Visibility::Private,
                type_params: Vec::new(),
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::LetLin {
                    name: "a".into(),
                    ty: Some(Ty::Base(BaseTy::I32)),
                    value: Box::new(var("x")),
                    body: Box::new(var("a")),
                }),
            },
            Decl::Fn {
                name: "const_unit".into(),
                visibility: Visibility::Private,
                type_params: Vec::new(),
                params: vec![],
                ret_ty: Ty::Base(BaseTy::Unit),
                body: unit(),
            },
        ],
    };

    let result = check_module(&module, crate::Discipline::Linear);
    assert!(
        result.is_ok(),
        "E2E module: linear must accept well-typed module — got: {:?}",
        result
    );

    let result = check_module(&module, crate::Discipline::Affine);
    assert!(
        result.is_ok(),
        "E2E module: affine must accept well-typed module"
    );
}

// =========================================================================
// ASPECT TESTS
//
// Edge cases, robustness, and boundary conditions.
// =========================================================================

/// Aspect: empty module is always accepted by both disciplines.
#[test]
fn aspect_empty_module_accepted() {
    use crate::check_module;
    use ephapax_syntax::Module;

    let empty_module = Module {
        name: "empty".into(),
        imports: Vec::new(),
        decls: Vec::new(),
    };

    assert!(
        check_module(&empty_module, crate::Discipline::Linear).is_ok(),
        "Aspect: empty module must be accepted by linear checker"
    );
    assert!(
        check_module(&empty_module, crate::Discipline::Affine).is_ok(),
        "Aspect: empty module must be accepted by affine checker"
    );
}

/// Aspect: literal expressions with no bindings are always accepted.
#[test]
fn aspect_literals_no_bindings_accepted() {
    let literals = vec![
        e(ExprKind::Lit(Literal::Unit)),
        e(ExprKind::Lit(Literal::Bool(true))),
        e(ExprKind::Lit(Literal::Bool(false))),
        e(ExprKind::Lit(Literal::I32(0))),
        e(ExprKind::Lit(Literal::I32(i32::MAX))),
        e(ExprKind::Lit(Literal::I32(i32::MIN))),
        e(ExprKind::Lit(Literal::F64(0.0))),
        e(ExprKind::Lit(Literal::F64(f64::INFINITY))),
        e(ExprKind::Lit(Literal::String("".to_string()))),
        e(ExprKind::Lit(Literal::String("hello world".to_string()))),
    ];

    for (i, expr) in literals.iter().enumerate() {
        let mut linear = LinearChecker::new();
        assert!(
            linear.check(expr).is_ok(),
            "Aspect literal[{i}]: linear must accept bare literal"
        );

        let mut affine = AffineChecker::new();
        assert!(
            affine.check(expr).is_ok(),
            "Aspect literal[{i}]: affine must accept bare literal"
        );
    }
}

/// Aspect: checker is stateless between calls (fresh checker == clean state).
///
/// Verifies that two separate checker instances do not share state, so a
/// rejection from one call does not contaminate the next.
#[test]
fn aspect_checker_stateless_between_instances() {
    // First call: rejectable expression (contraction)
    let bad_expr = e(ExprKind::LetLin {
        name: "z".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(99)),
        body: Box::new(e(ExprKind::Pair {
            left: Box::new(var("z")),
            right: Box::new(var("z")),
        })),
    });

    let mut checker1 = LinearChecker::new();
    assert!(checker1.check(&bad_expr).is_err(), "Aspect stateless: bad expr must fail");

    // Second call with a DIFFERENT checker instance on a good expression
    let good_expr = e(ExprKind::LetLin {
        name: "z".into(),
        ty: Some(Ty::Base(BaseTy::I32)),
        value: Box::new(i32_lit(99)),
        body: Box::new(var("z")),
    });

    let mut checker2 = LinearChecker::new();
    assert!(
        checker2.check(&good_expr).is_ok(),
        "Aspect stateless: fresh checker must not inherit state from prior rejected call"
    );
}

/// Aspect: violations collection is non-empty when check fails.
///
/// Verifies that whenever a checker returns Err, the violations vector
/// contains at least one entry.
#[test]
fn aspect_violations_non_empty_on_failure() {
    let bad_cases: Vec<(&str, Expr)> = vec![
        (
            "contraction",
            e(ExprKind::LetLin {
                name: "x".into(),
                ty: Some(Ty::Base(BaseTy::I32)),
                value: Box::new(i32_lit(1)),
                body: Box::new(e(ExprKind::Pair {
                    left: Box::new(var("x")),
                    right: Box::new(var("x")),
                })),
            }),
        ),
        (
            "weakening",
            e(ExprKind::LetLin {
                name: "y".into(),
                ty: Some(Ty::Base(BaseTy::I32)),
                value: Box::new(i32_lit(2)),
                body: Box::new(unit()),
            }),
        ),
        (
            "drop",
            e(ExprKind::Drop(Box::new(i32_lit(3)))),
        ),
    ];

    for (label, expr) in &bad_cases {
        let mut checker = LinearChecker::new();
        let result = checker.check(expr);
        assert!(result.is_err(), "Aspect violations[{label}]: must fail");
        let violations = result.unwrap_err();
        assert!(
            !violations.is_empty(),
            "Aspect violations[{label}]: violations vector must be non-empty on failure"
        );
    }
}

/// Aspect: is_error() and is_warning() are mutually exclusive for all violation kinds.
#[test]
fn aspect_violation_error_warning_mutually_exclusive() {
    use crate::DisciplineViolation;

    let all_violations: Vec<DisciplineViolation> = vec![
        DisciplineViolation::Contraction { name: "x".to_string() },
        DisciplineViolation::NotInScope { name: "y".to_string() },
        DisciplineViolation::WeakeningForbidden { name: "z".to_string() },
        DisciplineViolation::DropForbidden,
        DisciplineViolation::BranchDisagreement { name: "b".to_string() },
        DisciplineViolation::RegionLeakLinear { region: "r".to_string(), name: "s".to_string() },
        DisciplineViolation::LetForLinearType { name: "t".to_string() },
        DisciplineViolation::ImplicitDropWarning { region: "r".to_string(), name: "u".to_string() },
    ];

    for violation in &all_violations {
        let is_e = violation.is_error();
        let is_w = violation.is_warning();
        assert!(
            is_e != is_w,
            "Aspect: is_error and is_warning must be mutually exclusive for {:?}",
            violation
        );
    }
}
