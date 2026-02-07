// SPDX-License-Identifier: PMPL-1.0-or-later
// Free variable analysis for lambda expressions

use ephapax_syntax::{Expr, Pattern};
use smol_str::SmolStr;
use std::collections::HashSet;

/// Result of free variable analysis
#[derive(Debug, Clone)]
pub struct FreeVars {
    /// Set of free variables in the expression
    free: HashSet<SmolStr>,
}

impl FreeVars {
    pub fn new() -> Self {
        Self {
            free: HashSet::new(),
        }
    }

    pub fn is_free(&self, var: &str) -> bool {
        self.free.contains(var)
    }

    pub fn iter(&self) -> impl Iterator<Item = &SmolStr> {
        self.free.iter()
    }

    pub fn len(&self) -> usize {
        self.free.len()
    }

    pub fn is_empty(&self) -> bool {
        self.free.is_empty()
    }
}

/// Free variable analysis pass
pub struct FreeVarAnalysis;

impl FreeVarAnalysis {
    /// Analyze an expression to find free variables
    pub fn analyze(expr: &Expr) -> FreeVars {
        let mut bound = HashSet::new();
        let mut free = HashSet::new();
        Self::analyze_expr(expr, &mut bound, &mut free);
        FreeVars { free }
    }

    fn analyze_expr(expr: &Expr, bound: &mut HashSet<SmolStr>, free: &mut HashSet<SmolStr>) {
        match expr {
            Expr::Var(name, _) => {
                // Variable reference: free if not bound
                if !bound.contains(name.as_str()) {
                    free.insert(name.clone());
                }
            }

            Expr::Lambda { param, body, .. } => {
                // Lambda: param is bound in body
                let mut inner_bound = bound.clone();
                inner_bound.insert(param.clone());
                Self::analyze_expr(body, &mut inner_bound, free);
            }

            Expr::Let { name, value, body, .. } => {
                // Let: name is bound in body, not in value
                Self::analyze_expr(value, bound, free);

                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                Self::analyze_expr(body, &mut inner_bound, free);
            }

            Expr::LetBang { name, value, body, .. } => {
                // Let!: similar to let
                Self::analyze_expr(value, bound, free);

                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                Self::analyze_expr(body, &mut inner_bound, free);
            }

            Expr::App { func, arg, .. } => {
                // Application: analyze both parts
                Self::analyze_expr(func, bound, free);
                Self::analyze_expr(arg, bound, free);
            }

            Expr::BinOp { left, right, .. } => {
                // Binary operation: analyze both operands
                Self::analyze_expr(left, bound, free);
                Self::analyze_expr(right, bound, free);
            }

            Expr::If { cond, then_branch, else_branch, .. } => {
                // If: analyze all three parts
                Self::analyze_expr(cond, bound, free);
                Self::analyze_expr(then_branch, bound, free);
                Self::analyze_expr(else_branch, bound, free);
            }

            Expr::Case { scrutinee, arms, .. } => {
                // Case: analyze scrutinee and all arms
                Self::analyze_expr(scrutinee, bound, free);

                for arm in arms {
                    let mut arm_bound = bound.clone();
                    Self::bind_pattern(&arm.pattern, &mut arm_bound);
                    Self::analyze_expr(&arm.body, &mut arm_bound, free);
                }
            }

            Expr::Drop { expr, body, .. } => {
                // Drop: analyze both parts
                Self::analyze_expr(expr, bound, free);
                Self::analyze_expr(body, bound, free);
            }

            Expr::Region { body, .. } => {
                // Region: analyze body
                Self::analyze_expr(body, bound, free);
            }

            // Literals have no free variables
            Expr::IntLit(_, _) |
            Expr::FloatLit(_, _) |
            Expr::BoolLit(_, _) |
            Expr::StringLit(_, _) |
            Expr::Unit(_) => {}
        }
    }

    fn bind_pattern(pattern: &Pattern, bound: &mut HashSet<SmolStr>) {
        match pattern {
            Pattern::Var(name, _) => {
                bound.insert(name.clone());
            }
            Pattern::Constructor { fields, .. } => {
                for field in fields {
                    Self::bind_pattern(field, bound);
                }
            }
            Pattern::Wildcard(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::*;

    #[test]
    fn test_free_vars_simple() {
        // λ(x) -> x + y
        // Expected: {y}

        let lambda = Expr::Lambda {
            param: SmolStr::new("x"),
            body: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
                right: Box::new(Expr::Var(SmolStr::new("y"), Span::dummy())),
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };

        let free_vars = FreeVarAnalysis::analyze(&lambda);
        assert_eq!(free_vars.len(), 1);
        assert!(free_vars.is_free("y"));
        assert!(!free_vars.is_free("x"));
    }

    #[test]
    fn test_free_vars_nested() {
        // λ(x) -> λ(y) -> x + y + z
        // Expected: {z}

        let inner_lambda = Expr::Lambda {
            param: SmolStr::new("y"),
            body: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
                    right: Box::new(Expr::Var(SmolStr::new("y"), Span::dummy())),
                    span: Span::dummy(),
                }),
                right: Box::new(Expr::Var(SmolStr::new("z"), Span::dummy())),
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };

        let outer_lambda = Expr::Lambda {
            param: SmolStr::new("x"),
            body: Box::new(inner_lambda),
            span: Span::dummy(),
        };

        let free_vars = FreeVarAnalysis::analyze(&outer_lambda);
        assert_eq!(free_vars.len(), 1);
        assert!(free_vars.is_free("z"));
        assert!(!free_vars.is_free("x"));
        assert!(!free_vars.is_free("y"));
    }

    #[test]
    fn test_free_vars_let() {
        // let x = a in x + b
        // Expected: {a, b}

        let let_expr = Expr::Let {
            name: SmolStr::new("x"),
            value: Box::new(Expr::Var(SmolStr::new("a"), Span::dummy())),
            body: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
                right: Box::new(Expr::Var(SmolStr::new("b"), Span::dummy())),
                span: Span::dummy(),
            }),
            span: Span::dummy(),
        };

        let free_vars = FreeVarAnalysis::analyze(&let_expr);
        assert_eq!(free_vars.len(), 2);
        assert!(free_vars.is_free("a"));
        assert!(free_vars.is_free("b"));
        assert!(!free_vars.is_free("x"));
    }
}
