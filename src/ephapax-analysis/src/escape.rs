// SPDX-License-Identifier: PMPL-1.0-or-later
// Escape analysis: determine if variables escape their scope

use ephapax_syntax::{Expr, ExprKind};
use smol_str::SmolStr;
use std::collections::HashSet;

/// Result of escape analysis
#[derive(Debug, Clone)]
pub struct EscapeInfo {
    /// Set of variables that escape their scope
    escaping: HashSet<SmolStr>,
}

impl Default for EscapeInfo {
    fn default() -> Self {
        Self::new()
    }
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
        match &expr.kind {
            ExprKind::Var(name) => {
                if in_escaping_context {
                    escaping.insert(name.clone());
                }
            }

            ExprKind::Lambda { body, .. } => {
                // Lambda body is an escaping context (captures free vars)
                Self::analyze_expr(body, escaping, true);
            }

            ExprKind::Let { value, body, .. } => {
                Self::analyze_expr(value, escaping, in_escaping_context);
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            ExprKind::LetLin { value, body, .. } => {
                Self::analyze_expr(value, escaping, in_escaping_context);
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            ExprKind::App { func, arg } => {
                Self::analyze_expr(func, escaping, in_escaping_context);
                Self::analyze_expr(arg, escaping, true); // Arg always escaping
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::analyze_expr(cond, escaping, in_escaping_context);
                Self::analyze_expr(then_branch, escaping, in_escaping_context);
                Self::analyze_expr(else_branch, escaping, in_escaping_context);
            }

            ExprKind::Case {
                scrutinee,
                left_body,
                right_body,
                ..
            } => {
                Self::analyze_expr(scrutinee, escaping, in_escaping_context);
                Self::analyze_expr(left_body, escaping, in_escaping_context);
                Self::analyze_expr(right_body, escaping, in_escaping_context);
            }

            ExprKind::Region { body, .. } => {
                // Region body: values allocated here should NOT escape.
                // We track this separately — interior values in escaping
                // context means region escape violation.
                Self::analyze_expr(body, escaping, in_escaping_context);
            }

            ExprKind::Drop(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Copy(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Borrow(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Deref(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Pair { left, right } => {
                Self::analyze_expr(left, escaping, in_escaping_context);
                Self::analyze_expr(right, escaping, in_escaping_context);
            }

            ExprKind::Fst(inner) | ExprKind::Snd(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Inl { value, .. } | ExprKind::Inr { value, .. } => {
                Self::analyze_expr(value, escaping, in_escaping_context);
            }

            ExprKind::StringConcat { left, right } => {
                Self::analyze_expr(left, escaping, in_escaping_context);
                Self::analyze_expr(right, escaping, in_escaping_context);
            }

            ExprKind::StringLen(inner) => {
                Self::analyze_expr(inner, escaping, in_escaping_context);
            }

            ExprKind::Block(exprs) => {
                for e in exprs {
                    Self::analyze_expr(e, escaping, in_escaping_context);
                }
            }

            ExprKind::BinOp { left, right, .. } => {
                Self::analyze_expr(left, escaping, in_escaping_context);
                Self::analyze_expr(right, escaping, in_escaping_context);
            }

            ExprKind::UnaryOp { operand, .. } => {
                Self::analyze_expr(operand, escaping, in_escaping_context);
            }

            ExprKind::ListLit(exprs) | ExprKind::TupleLit(exprs) => {
                for e in exprs {
                    Self::analyze_expr(e, escaping, in_escaping_context);
                }
            }

            ExprKind::ListIndex { list, index } => {
                Self::analyze_expr(list, escaping, in_escaping_context);
                Self::analyze_expr(index, escaping, in_escaping_context);
            }

            ExprKind::TupleIndex { tuple, .. } => {
                Self::analyze_expr(tuple, escaping, in_escaping_context);
            }

            ExprKind::FFI { args, .. } => {
                // FFI args always escape (passed to native code)
                for arg in args {
                    Self::analyze_expr(arg, escaping, true);
                }
            }

            // Literals and string allocations never escape
            ExprKind::Lit(_) | ExprKind::StringNew { .. } => {}
        }
    }
}
