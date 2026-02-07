// SPDX-License-Identifier: PMPL-1.0-or-later
// Escape analysis: determine if variables escape their scope

use ephapax_syntax::{Expr, Pattern};
use smol_str::SmolStr;
use std::collections::HashSet;

/// Result of escape analysis
#[derive(Debug, Clone)]
pub struct EscapeInfo {
    /// Set of variables that escape their scope
    escaping: HashSet<SmolStr>,
}

impl EscapeInfo {
    pub fn new() -> Self {
        Self {
            escaping: HashSet::new(),
        }
    }

    pub fn escapes(&self, var: &str) -> bool {
        self.escaping.contains(var)
    }

    pub fn iter(&self) -> impl Iterator<Item = &SmolStr> {
        self.escaping.iter()
    }
}

/// Escape analysis pass
pub struct EscapeAnalysis;

impl EscapeAnalysis {
    /// Analyze an expression to find escaping variables
    ///
    /// A variable escapes if it:
    /// - Is captured by a lambda
    /// - Is returned from a function
    /// - Is passed to a function that might store it
    pub fn analyze(expr: &Expr) -> EscapeInfo {
        let mut escaping = HashSet::new();
        Self::analyze_expr(expr, &mut escaping, false);
        EscapeInfo { escaping }
    }

    fn analyze_expr(expr: &Expr, escaping: &mut HashSet<SmolStr>, in_escaping_context: bool) {
        match expr {
            Expr::Var(name, _) => {
                // Variable in escaping context escapes
                if in_escaping_context {
                    escaping.insert(name.clone());
                }
            }

            Expr::Lambda { body, .. } => {
                // Lambda body is an escaping context (captures free vars)
                Self::analyze_expr(body, escaping, true);
            }

            Expr::Let { value, body, .. } => {
                Self::analyze_expr(value, escaping, in_escaping_context);
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            Expr::LetBang { value, body, .. } => {
                Self::analyze_expr(value, escaping, in_escaping_context);
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            Expr::App { func, arg, .. } => {
                // Arguments passed to functions may escape
                Self::analyze_expr(func, escaping, in_escaping_context);
                Self::analyze_expr(arg, escaping, true);  // Arg always escaping
            }

            Expr::BinOp { left, right, .. } => {
                // Binary operators don't cause escape (primitive operations)
                Self::analyze_expr(left, escaping, in_escaping_context);
                Self::analyze_expr(right, escaping, in_escaping_context);
            }

            Expr::If { cond, then_branch, else_branch, .. } => {
                Self::analyze_expr(cond, escaping, in_escaping_context);
                // Return value may escape
                Self::analyze_expr(then_branch, escaping, in_escaping_context);
                Self::analyze_expr(else_branch, escaping, in_escaping_context);
            }

            Expr::Case { scrutinee, arms, .. } => {
                Self::analyze_expr(scrutinee, escaping, in_escaping_context);

                for arm in arms {
                    // Arm body may return (escape)
                    Self::analyze_expr(&arm.body, escaping, in_escaping_context);
                }
            }

            Expr::Drop { expr, body, .. } => {
                Self::analyze_expr(expr, escaping, in_escaping_context);
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            Expr::Region { body, .. } => {
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            // Literals never escape
            Expr::IntLit(_, _) |
            Expr::FloatLit(_, _) |
            Expr::BoolLit(_, _) |
            Expr::StringLit(_, _) |
            Expr::Unit(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::*;

    #[test]
    fn test_lambda_captures_escape() {
        // let x = 42 in λ(y) -> x + y
        // Expected: x escapes (captured by lambda)

        let lambda = Expr::Lambda {
            param: SmolStr::new("y"),
            body: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
                right: Box::new(Expr::Var(SmolStr::new("y"), Span::dummy())),
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };

        let let_expr = Expr::Let {
            name: SmolStr::new("x"),
            value: Box::new(Expr::IntLit(42, Span::dummy())),
            body: Box::new(lambda),
            span: Span::dummy(),
        };

        let escape_info = EscapeAnalysis::analyze(&let_expr);
        assert!(escape_info.escapes("x"));
        assert!(!escape_info.escapes("y"));  // y is bound, not captured
    }

    #[test]
    fn test_non_escaping_local() {
        // let x = 42 in x + 1
        // Expected: x does NOT escape (purely local)

        let let_expr = Expr::Let {
            name: SmolStr::new("x"),
            value: Box::new(Expr::IntLit(42, Span::dummy())),
            body: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
                right: Box::new(Expr::IntLit(1, Span::dummy())),
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };

        let escape_info = EscapeAnalysis::analyze(&let_expr);
        assert!(!escape_info.escapes("x"));
    }

    #[test]
    fn test_function_arg_escapes() {
        // f(x)  -- x escapes (passed to function)

        let app = Expr::App {
            func: Box::new(Expr::Var(SmolStr::new("f"), Span::dummy())),
            arg: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
            span: Span::dummy(),
        };

        let escape_info = EscapeAnalysis::analyze(&app);
        assert!(escape_info.escapes("x"));
        assert!(escape_info.escapes("f"));  // f also escapes (used in app)
    }
}
