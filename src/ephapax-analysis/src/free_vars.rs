// SPDX-License-Identifier: PMPL-1.0-or-later
// Free variable analysis for Ephapax expressions

use ephapax_syntax::{Expr, ExprKind};
use smol_str::SmolStr;
use std::collections::HashSet;

/// Result of free variable analysis
#[derive(Debug, Clone)]
pub struct FreeVars {
    /// Set of free variables
    free: HashSet<SmolStr>,
}

impl Default for FreeVars {
    fn default() -> Self {
        Self::new()
    }
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
    /// Find all free variables in an expression
    pub fn analyze(expr: &Expr) -> FreeVars {
        let mut free = HashSet::new();
        let mut bound = HashSet::new();
        Self::collect(expr, &mut free, &mut bound);
        FreeVars { free }
    }

    fn collect(expr: &Expr, free: &mut HashSet<SmolStr>, bound: &mut HashSet<SmolStr>) {
        match &expr.kind {
            ExprKind::Var(name) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }

            ExprKind::Lambda { param, body, .. } => {
                let mut inner_bound = bound.clone();
                inner_bound.insert(param.clone());
                Self::collect(body, free, &mut inner_bound);
            }

            ExprKind::Let {
                name, value, body, ..
            } => {
                Self::collect(value, free, bound);
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                Self::collect(body, free, &mut inner_bound);
            }

            ExprKind::LetLin {
                name, value, body, ..
            } => {
                Self::collect(value, free, bound);
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                Self::collect(body, free, &mut inner_bound);
            }

            ExprKind::App { func, arg } => {
                Self::collect(func, free, bound);
                Self::collect(arg, free, bound);
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::collect(cond, free, bound);
                Self::collect(then_branch, free, bound);
                Self::collect(else_branch, free, bound);
            }

            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => {
                Self::collect(scrutinee, free, bound);
                let mut left_bound = bound.clone();
                left_bound.insert(left_var.clone());
                Self::collect(left_body, free, &mut left_bound);
                let mut right_bound = bound.clone();
                right_bound.insert(right_var.clone());
                Self::collect(right_body, free, &mut right_bound);
            }

            ExprKind::Region { body, .. } => {
                Self::collect(body, free, bound);
            }

            ExprKind::Drop(inner)
            | ExprKind::Copy(inner)
            | ExprKind::Borrow(inner)
            | ExprKind::Deref(inner)
            | ExprKind::Fst(inner)
            | ExprKind::Snd(inner)
            | ExprKind::StringLen(inner) => {
                Self::collect(inner, free, bound);
            }

            ExprKind::Pair { left, right } | ExprKind::StringConcat { left, right } => {
                Self::collect(left, free, bound);
                Self::collect(right, free, bound);
            }

            ExprKind::Inl { value, .. } | ExprKind::Inr { value, .. } => {
                Self::collect(value, free, bound);
            }

            ExprKind::Block(exprs) => {
                for e in exprs {
                    Self::collect(e, free, bound);
                }
            }

            ExprKind::BinOp { left, right, .. } => {
                Self::collect(left, free, bound);
                Self::collect(right, free, bound);
            }

            ExprKind::UnaryOp { operand, .. } => {
                Self::collect(operand, free, bound);
            }

            ExprKind::ListLit(exprs) | ExprKind::TupleLit(exprs) => {
                for e in exprs {
                    Self::collect(e, free, bound);
                }
            }

            ExprKind::ListIndex { list, index } => {
                Self::collect(list, free, bound);
                Self::collect(index, free, bound);
            }

            ExprKind::TupleIndex { tuple, .. } => {
                Self::collect(tuple, free, bound);
            }

            ExprKind::FFI { args, .. } => {
                for arg in args {
                    Self::collect(arg, free, bound);
                }
            }

            ExprKind::Lit(_) | ExprKind::StringNew { .. } => {}
        }
    }
}
