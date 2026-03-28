// SPDX-License-Identifier: PMPL-1.0-or-later
// Liveness analysis: determine which variables are live at each program point

use ephapax_syntax::{Expr, ExprKind};
use smol_str::SmolStr;
use std::collections::HashSet;

/// Result of liveness analysis
#[derive(Debug, Clone)]
pub struct LiveVars {
    /// Set of live variables at a given program point
    live: HashSet<SmolStr>,
}

impl Default for LiveVars {
    fn default() -> Self {
        Self::new()
    }
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

    pub fn iter(&self) -> impl Iterator<Item = &SmolStr> {
        self.live.iter()
    }

    pub fn len(&self) -> usize {
        self.live.len()
    }

    pub fn is_empty(&self) -> bool {
        self.live.is_empty()
    }
}

/// Liveness analysis pass
///
/// Computes the set of variables that are live (will be used before
/// being redefined) at each program point. Used for:
/// - Dead code elimination
/// - Register allocation
/// - Linear variable consumption verification
pub struct LivenessAnalysis;

impl LivenessAnalysis {
    /// Compute live variables at the entry of an expression
    pub fn analyze(expr: &Expr) -> LiveVars {
        let mut live = HashSet::new();
        Self::compute(expr, &mut live);
        LiveVars { live }
    }

    fn compute(expr: &Expr, live: &mut HashSet<SmolStr>) {
        match &expr.kind {
            ExprKind::Var(name) => {
                live.insert(name.clone());
            }

            ExprKind::Lambda { param, body, .. } => {
                let mut body_live = HashSet::new();
                Self::compute(body, &mut body_live);
                body_live.remove(param);
                live.extend(body_live);
            }

            ExprKind::Let {
                name, value, body, ..
            }
            | ExprKind::LetLin {
                name, value, body, ..
            } => {
                let mut body_live = HashSet::new();
                Self::compute(body, &mut body_live);
                body_live.remove(name);
                Self::compute(value, &mut body_live);
                live.extend(body_live);
            }

            ExprKind::App { func, arg } => {
                Self::compute(func, live);
                Self::compute(arg, live);
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let mut then_live = HashSet::new();
                let mut else_live = HashSet::new();
                Self::compute(then_branch, &mut then_live);
                Self::compute(else_branch, &mut else_live);
                live.extend(then_live);
                live.extend(else_live);
                Self::compute(cond, live);
            }

            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => {
                let mut left_live = HashSet::new();
                let mut right_live = HashSet::new();
                Self::compute(left_body, &mut left_live);
                Self::compute(right_body, &mut right_live);
                left_live.remove(left_var);
                right_live.remove(right_var);
                live.extend(left_live);
                live.extend(right_live);
                Self::compute(scrutinee, live);
            }

            ExprKind::Region { body, .. } => {
                Self::compute(body, live);
            }

            ExprKind::Drop(inner)
            | ExprKind::Copy(inner)
            | ExprKind::Borrow(inner)
            | ExprKind::Deref(inner)
            | ExprKind::Fst(inner)
            | ExprKind::Snd(inner)
            | ExprKind::StringLen(inner) => {
                Self::compute(inner, live);
            }

            ExprKind::Pair { left, right } | ExprKind::StringConcat { left, right } => {
                Self::compute(left, live);
                Self::compute(right, live);
            }

            ExprKind::Inl { value, .. } | ExprKind::Inr { value, .. } => {
                Self::compute(value, live);
            }

            ExprKind::Block(exprs) => {
                for e in exprs.iter().rev() {
                    Self::compute(e, live);
                }
            }

            ExprKind::BinOp { left, right, .. } => {
                Self::compute(left, live);
                Self::compute(right, live);
            }

            ExprKind::UnaryOp { operand, .. } => {
                Self::compute(operand, live);
            }

            ExprKind::ListLit(exprs) | ExprKind::TupleLit(exprs) => {
                for e in exprs.iter().rev() {
                    Self::compute(e, live);
                }
            }

            ExprKind::ListIndex { list, index } => {
                Self::compute(index, live);
                Self::compute(list, live);
            }

            ExprKind::TupleIndex { tuple, .. } => {
                Self::compute(tuple, live);
            }

            ExprKind::FFI { args, .. } => {
                for arg in args.iter().rev() {
                    Self::compute(arg, live);
                }
            }

            ExprKind::Lit(_) | ExprKind::StringNew { .. } => {}
        }
    }
}
