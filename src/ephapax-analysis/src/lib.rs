#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// Static analysis passes for Ephapax compiler optimization

pub mod escape;
pub mod free_vars;
pub mod liveness;

pub use escape::{EscapeAnalysis, EscapeInfo};
pub use free_vars::{FreeVarAnalysis, FreeVars};
pub use liveness::{LiveVars, LivenessAnalysis};

/// Optimization result: variables that must be captured by closures
#[derive(Debug, Clone)]
pub struct CaptureSet {
    /// Variables that must be captured (free and escaping)
    pub must_capture: Vec<String>,
    /// Variables that could be optimized away
    pub can_elide: Vec<String>,
}

/// Combined analysis for closure optimization.
///
/// Given a lambda BODY (not the lambda itself) and the set of variables
/// in scope at the lambda definition point, computes which variables
/// must be captured in the closure environment.
///
/// A variable must be captured if it is FREE in the lambda body — meaning
/// it's referenced but not bound within the body. Variables that are not
/// free can be elided from the capture set.
///
/// The escape analysis refines this further: among captured variables,
/// those that escape (are passed to other lambdas or FFI) need heap
/// allocation; those that don't can stay on the stack.
pub fn analyze_closure_captures(
    lambda_body: &ephapax_syntax::Expr,
    scope_vars: &[String],
) -> CaptureSet {
    // Step 1: Find free variables in lambda body
    let free_vars = FreeVarAnalysis::analyze(lambda_body);

    // Step 2: Perform escape analysis for optimization hints
    let _escape_info = EscapeAnalysis::analyze(lambda_body);

    // Step 3: Compute capture set
    // All free variables from scope must be captured — they're referenced
    // in the lambda body but defined outside it.
    let mut must_capture = Vec::new();
    let mut can_elide = Vec::new();

    for var in scope_vars {
        if free_vars.is_free(var) {
            must_capture.push(var.clone());
        } else {
            can_elide.push(var.clone());
        }
    }

    CaptureSet {
        must_capture,
        can_elide,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::*;

    /// Helper to create an expression with a dummy span.
    fn e(kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: Span::dummy(),
        }
    }

    #[test]
    fn test_free_vars_simple() {
        // x + y — both x and y are free
        let expr = e(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(e(ExprKind::Var("x".into()))),
            right: Box::new(e(ExprKind::Var("y".into()))),
        });
        let free = FreeVarAnalysis::analyze(&expr);
        assert!(free.is_free("x"));
        assert!(free.is_free("y"));
        assert_eq!(free.len(), 2);
    }

    #[test]
    fn test_free_vars_let_binds() {
        // let x = 1 in x + y — only y is free (x is bound)
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            body: Box::new(e(ExprKind::BinOp {
                op: BinOp::Add,
                left: Box::new(e(ExprKind::Var("x".into()))),
                right: Box::new(e(ExprKind::Var("y".into()))),
            })),
        });
        let free = FreeVarAnalysis::analyze(&expr);
        assert!(!free.is_free("x"));
        assert!(free.is_free("y"));
        assert_eq!(free.len(), 1);
    }

    #[test]
    fn test_free_vars_lambda_binds_param() {
        // λ(x: I32) -> x + c — only c is free (x is param)
        let expr = e(ExprKind::Lambda {
            param: "x".into(),
            param_ty: Ty::Base(BaseTy::I32),
            body: Box::new(e(ExprKind::BinOp {
                op: BinOp::Add,
                left: Box::new(e(ExprKind::Var("x".into()))),
                right: Box::new(e(ExprKind::Var("c".into()))),
            })),
        });
        let free = FreeVarAnalysis::analyze(&expr);
        assert!(!free.is_free("x"));
        assert!(free.is_free("c"));
    }

    #[test]
    fn test_escape_lambda_captures() {
        // λ(x: I32) -> x + c — c escapes (captured by lambda)
        let expr = e(ExprKind::Lambda {
            param: "x".into(),
            param_ty: Ty::Base(BaseTy::I32),
            body: Box::new(e(ExprKind::BinOp {
                op: BinOp::Add,
                left: Box::new(e(ExprKind::Var("x".into()))),
                right: Box::new(e(ExprKind::Var("c".into()))),
            })),
        });
        let escape = EscapeAnalysis::analyze(&expr);
        assert!(escape.escapes("c"));
        assert!(escape.escapes("x")); // x is in lambda body = escaping context
    }

    #[test]
    fn test_liveness_simple() {
        // x + y — both x and y are live
        let expr = e(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(e(ExprKind::Var("x".into()))),
            right: Box::new(e(ExprKind::Var("y".into()))),
        });
        let live = LivenessAnalysis::analyze(&expr);
        assert!(live.is_live("x"));
        assert!(live.is_live("y"));
    }

    #[test]
    fn test_liveness_let_removes_binding() {
        // let x = 1 in x — x is live at the let body, but not before
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            body: Box::new(e(ExprKind::Var("x".into()))),
        });
        let live = LivenessAnalysis::analyze(&expr);
        // At the entry of the whole expression, x is NOT live
        // (it's defined by the let, not needed before)
        assert!(!live.is_live("x"));
    }

    #[test]
    fn test_minimal_capture_set() {
        // λ(x: I32) -> x + c
        // scope_vars = [a, b, c]
        // Only c is free and escaping → must_capture = [c]
        let lambda_body = e(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(e(ExprKind::Var("x".into()))),
            right: Box::new(e(ExprKind::Var("c".into()))),
        });

        let scope_vars = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let captures = analyze_closure_captures(&lambda_body, &scope_vars);

        assert!(captures.must_capture.contains(&"c".to_string()));
        assert!(!captures.must_capture.contains(&"a".to_string()));
        assert!(!captures.must_capture.contains(&"b".to_string()));
        assert!(captures.can_elide.contains(&"a".to_string()));
        assert!(captures.can_elide.contains(&"b".to_string()));
    }
}
