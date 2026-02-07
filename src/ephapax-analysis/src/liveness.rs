// SPDX-License-Identifier: PMPL-1.0-or-later
// Liveness analysis: determine which variables are live at each program point

use ephapax_syntax::{Expr, Pattern};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

/// Live variables at a program point
#[derive(Debug, Clone)]
pub struct LiveVars {
    /// Variables that are live (will be used later)
    live: HashSet<SmolStr>,
}

impl LiveVars {
    pub fn new() -> Self {
        Self {
            live: HashSet::new(),
        }
    }

    pub fn is_live(&self, var: &str) -> bool {
        self.live.contains(var)
    }

    pub fn insert(&mut self, var: SmolStr) {
        self.live.insert(var);
    }

    pub fn extend(&mut self, vars: impl Iterator<Item = SmolStr>) {
        self.live.extend(vars);
    }

    pub fn iter(&self) -> impl Iterator<Item = &SmolStr> {
        self.live.iter()
    }
}

/// Liveness analysis pass
pub struct LivenessAnalysis;

impl LivenessAnalysis {
    /// Analyze liveness backward from expression
    ///
    /// Returns variables that are live at the start of the expression
    pub fn analyze(expr: &Expr) -> LiveVars {
        let mut live = LiveVars::new();
        Self::analyze_expr(expr, &mut live);
        live
    }

    fn analyze_expr(expr: &Expr, live_after: &mut LiveVars) {
        match expr {
            Expr::Var(name, _) => {
                // Variable use: mark as live
                live_after.insert(name.clone());
            }

            Expr::Lambda { param, body, .. } => {
                // Analyze body
                Self::analyze_expr(body, live_after);
                // Remove param (it's defined here)
                live_after.live.remove(param.as_str());
            }

            Expr::Let { name, value, body, .. } => {
                // Backward analysis: body first, then value
                Self::analyze_expr(body, live_after);
                live_after.live.remove(name.as_str());  // Defined here
                Self::analyze_expr(value, live_after);
            }

            Expr::LetBang { name, value, body, .. } => {
                Self::analyze_expr(body, live_after);
                live_after.live.remove(name.as_str());
                Self::analyze_expr(value, live_after);
            }

            Expr::App { func, arg, .. } => {
                Self::analyze_expr(arg, live_after);
                Self::analyze_expr(func, live_after);
            }

            Expr::BinOp { left, right, .. } => {
                Self::analyze_expr(right, live_after);
                Self::analyze_expr(left, live_after);
            }

            Expr::If { cond, then_branch, else_branch, .. } => {
                // Union of live vars from both branches
                let mut then_live = live_after.clone();
                let mut else_live = live_after.clone();

                Self::analyze_expr(then_branch, &mut then_live);
                Self::analyze_expr(else_branch, &mut else_live);

                // Union
                live_after.extend(then_live.iter().cloned());
                live_after.extend(else_live.iter().cloned());

                // Condition
                Self::analyze_expr(cond, live_after);
            }

            Expr::Case { scrutinee, arms, .. } => {
                // Union of live vars from all arms
                let mut arms_live = Vec::new();

                for arm in arms {
                    let mut arm_live = live_after.clone();
                    Self::analyze_expr(&arm.body, &mut arm_live);

                    // Remove pattern-bound variables
                    Self::remove_pattern_vars(&arm.pattern, &mut arm_live);

                    arms_live.push(arm_live);
                }

                // Union all arms
                for arm_live in arms_live {
                    live_after.extend(arm_live.iter().cloned());
                }

                // Scrutinee
                Self::analyze_expr(scrutinee, live_after);
            }

            Expr::Drop { expr, body, .. } => {
                Self::analyze_expr(body, live_after);
                Self::analyze_expr(expr, live_after);
            }

            Expr::Region { body, .. } => {
                Self::analyze_expr(body, live_after);
            }

            // Literals: no live variables
            Expr::IntLit(_, _) |
            Expr::FloatLit(_, _) |
            Expr::BoolLit(_, _) |
            Expr::StringLit(_, _) |
            Expr::Unit(_) => {}
        }
    }

    fn remove_pattern_vars(pattern: &Pattern, live: &mut LiveVars) {
        match pattern {
            Pattern::Var(name, _) => {
                live.live.remove(name.as_str());
            }
            Pattern::Constructor { fields, .. } => {
                for field in fields {
                    Self::remove_pattern_vars(field, live);
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
    fn test_liveness_simple() {
        // x + y
        // Expected: {x, y} live

        let binop = Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Var(SmolStr::new("x"), Span::dummy())),
            right: Box::new(Expr::Var(SmolStr::new("y"), Span::dummy())),
            span: Span::dummy(),
        };

        let live = LivenessAnalysis::analyze(&binop);
        assert!(live.is_live("x"));
        assert!(live.is_live("y"));
    }

    #[test]
    fn test_liveness_let() {
        // let x = a in x + b
        // Expected: {a, b} live at start, NOT x

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

        let live = LivenessAnalysis::analyze(&let_expr);
        assert!(live.is_live("a"));
        assert!(live.is_live("b"));
        assert!(!live.is_live("x"));  // x is defined, not live before definition
    }

    #[test]
    fn test_liveness_dead_code() {
        // let x = 42 in 1
        // Expected: x NOT live (unused)

        let let_expr = Expr::Let {
            name: SmolStr::new("x"),
            value: Box::new(Expr::IntLit(42, Span::dummy())),
            body: Box::new(Expr::IntLit(1, Span::dummy())),
            span: Span::dummy(),
        };

        let live = LivenessAnalysis::analyze(&let_expr);
        assert!(!live.is_live("x"));
    }
}
