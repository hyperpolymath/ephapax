// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Linear Discipline Checker
//!
//! Enforces the linear substructural grammar:
//! - **No weakening**: every `let!` binding MUST be consumed exactly once.
//! - **No contraction**: no binding may be used more than once.
//! - **Branch agreement**: all branches of `if`/`case` must consume the
//!   same set of linear variables.
//! - **Region safety**: all region-bound linear values must be consumed
//!   before region exit.
//! - **`drop` forbidden**: explicit weakening is a grammar violation.
//! - **`let` restricted**: in linear discipline, `let` may only bind
//!   unrestricted types. Linear types MUST use `let!`.
//!
//! See `grammar/linear.ebnf` for the formal grammar specification.

use crate::context::{BindingForm, ConsumeResult, Context};
use crate::DisciplineViolation;
use ephapax_syntax::{Decl, Expr, ExprKind, Module, Var};

/// Linear discipline checker.
///
/// Walks the ephapax AST and verifies that every expression conforms to
/// the linear substructural grammar — no weakening, no contraction.
pub struct LinearChecker {
    ctx: Context,
    violations: Vec<DisciplineViolation>,
}

impl LinearChecker {
    /// Create a new linear discipline checker.
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
            violations: Vec::new(),
        }
    }

    /// Check a single expression under the linear discipline.
    /// Returns collected violations (if any).
    pub fn check(&mut self, expr: &Expr) -> Result<(), Vec<DisciplineViolation>> {
        self.walk_expr(expr);
        if self.violations.is_empty() {
            Ok(())
        } else {
            Err(self.violations.clone())
        }
    }

    /// Check an entire module under the linear discipline.
    pub fn check_module(&mut self, module: &Module) -> Result<(), Vec<DisciplineViolation>> {
        for decl in &module.decls {
            self.walk_decl(decl);
        }
        if self.violations.is_empty() {
            Ok(())
        } else {
            Err(self.violations.clone())
        }
    }

    /// Walk a top-level declaration.
    fn walk_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Fn {
                params,
                body,
                ..
            } => {
                // Bind parameters
                for (name, ty) in params {
                    self.ctx
                        .bind(name.clone(), BindingForm::Param, Some(ty.clone()));
                }

                // Check body
                self.walk_expr(body);

                // All linear params must be consumed
                for (name, ty) in params {
                    if ty.is_linear() {
                        if let Some(binding) = self.ctx.get(name) {
                            if !binding.consumed {
                                self.violations.push(DisciplineViolation::WeakeningForbidden {
                                    name: name.to_string(),
                                });
                            }
                        }
                    }
                    self.ctx.unbind(name);
                }
            }
            Decl::Type { .. } => { /* no discipline check needed */ }
        }
    }

    /// Walk an expression, enforcing linear discipline.
    fn walk_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            // --- Literals: no discipline implications ---
            ExprKind::Lit(_) => {}

            // --- Variable reference: consume the binding ---
            ExprKind::Var(name) => {
                self.consume_var(name);
            }

            // --- let! (linear binding) ---
            ExprKind::LetLin {
                name, ty, value, body,
            } => {
                self.walk_expr(value);
                self.ctx.bind(name.clone(), BindingForm::LetBang, ty.clone());
                self.walk_expr(body);

                // In linear discipline: MUST be consumed
                if let Some(binding) = self.ctx.get(name) {
                    if !binding.consumed {
                        self.violations.push(DisciplineViolation::WeakeningForbidden {
                            name: name.to_string(),
                        });
                    }
                }
                self.ctx.unbind(name);
            }

            // --- let (restricted in linear grammar) ---
            ExprKind::Let {
                name, ty, value, body,
            } => {
                self.walk_expr(value);

                // In linear grammar, `let` may only bind unrestricted types
                let is_linear_type = ty.as_ref().is_some_and(|t| t.is_linear());
                if is_linear_type {
                    self.violations.push(DisciplineViolation::LetForLinearType {
                        name: name.to_string(),
                    });
                }

                self.ctx.bind(name.clone(), BindingForm::Let, ty.clone());
                self.walk_expr(body);

                // Even `let` bindings of linear types must be consumed
                // (we already reported the LetForLinearType violation)
                if let Some(binding) = self.ctx.get(name) {
                    if binding.is_linear_type() && !binding.consumed {
                        self.violations.push(DisciplineViolation::WeakeningForbidden {
                            name: name.to_string(),
                        });
                    }
                }
                self.ctx.unbind(name);
            }

            // --- Lambda ---
            ExprKind::Lambda {
                param,
                param_ty,
                body,
            } => {
                self.ctx
                    .bind(param.clone(), BindingForm::Param, Some(param_ty.clone()));
                self.walk_expr(body);

                // Linear params must be consumed
                if param_ty.is_linear() {
                    if let Some(binding) = self.ctx.get(param) {
                        if !binding.consumed {
                            self.violations.push(DisciplineViolation::WeakeningForbidden {
                                name: param.to_string(),
                            });
                        }
                    }
                }
                self.ctx.unbind(param);
            }

            // --- Application: check both sides ---
            ExprKind::App { func, arg } => {
                self.walk_expr(func);
                self.walk_expr(arg);
            }

            // --- Pair: both sides consumed ---
            ExprKind::Pair { left, right } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }

            // --- Projections ---
            ExprKind::Fst(inner) | ExprKind::Snd(inner) => {
                self.walk_expr(inner);
            }

            // --- Sum injections ---
            ExprKind::Inl { value, .. } | ExprKind::Inr { value, .. } => {
                self.walk_expr(value);
            }

            // --- Case: branches MUST agree on linear consumption ---
            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => {
                self.walk_expr(scrutinee);

                // Snapshot before left branch
                let pre_snapshot = self.ctx.snapshot_consumption();

                // Check left branch
                self.ctx
                    .bind(left_var.clone(), BindingForm::Let, None);
                self.walk_expr(left_body);
                self.ctx.unbind(left_var);
                let left_snapshot = self.ctx.snapshot_consumption();

                // Restore and check right branch
                self.ctx.restore_consumption(&pre_snapshot);
                self.ctx
                    .bind(right_var.clone(), BindingForm::Let, None);
                self.walk_expr(right_body);
                self.ctx.unbind(right_var);
                let right_snapshot = self.ctx.snapshot_consumption();

                // Check branch agreement
                self.check_branch_agreement(&left_snapshot, &right_snapshot);

                // Merge: a variable is consumed if consumed in BOTH branches
                // (since they must agree, this is the same as either)
                self.ctx.restore_consumption(&left_snapshot);
            }

            // --- If: branches MUST agree ---
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk_expr(cond);

                let pre_snapshot = self.ctx.snapshot_consumption();

                self.walk_expr(then_branch);
                let then_snapshot = self.ctx.snapshot_consumption();

                self.ctx.restore_consumption(&pre_snapshot);
                self.walk_expr(else_branch);
                let else_snapshot = self.ctx.snapshot_consumption();

                self.check_branch_agreement(&then_snapshot, &else_snapshot);
                self.ctx.restore_consumption(&then_snapshot);
            }

            // --- Region: all linear region-bound values must be consumed ---
            ExprKind::Region { name, body } => {
                self.ctx.enter_region(name.clone());
                self.walk_expr(body);

                // Check all region-bound linears consumed
                let region_bindings = self.ctx.region_bindings(name);
                for (var_name, binding) in &region_bindings {
                    if binding.is_linear_type() && !binding.consumed {
                        self.violations.push(DisciplineViolation::RegionLeakLinear {
                            region: name.to_string(),
                            name: var_name.to_string(),
                        });
                    }
                }

                self.ctx.exit_region();
            }

            // --- Borrow/Deref: walk inner ---
            ExprKind::Borrow(inner) | ExprKind::Deref(inner) => {
                self.walk_expr(inner);
            }

            // --- Drop: FORBIDDEN in linear grammar ---
            ExprKind::Drop(inner) => {
                self.violations.push(DisciplineViolation::DropForbidden);
                self.walk_expr(inner);
            }

            // --- Copy: walk inner ---
            ExprKind::Copy(inner) => {
                self.walk_expr(inner);
            }

            // --- Block: walk all ---
            ExprKind::Block(exprs) => {
                for e in exprs {
                    self.walk_expr(e);
                }
            }

            // --- FFI: walk args ---
            ExprKind::FFI { args, .. } => {
                for arg in args {
                    self.walk_expr(arg);
                }
            }

            // --- Operators ---
            ExprKind::BinOp { left, right, .. } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }
            ExprKind::UnaryOp { operand, .. } => {
                self.walk_expr(operand);
            }

            // --- String operations ---
            ExprKind::StringNew { .. } => {}
            ExprKind::StringConcat { left, right } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }
            ExprKind::StringLen(inner) => {
                self.walk_expr(inner);
            }

            // --- Collections ---
            ExprKind::ListLit(elements) | ExprKind::TupleLit(elements) => {
                for e in elements {
                    self.walk_expr(e);
                }
            }
            ExprKind::ListIndex { list, index } => {
                self.walk_expr(list);
                self.walk_expr(index);
            }
            ExprKind::TupleIndex { tuple, .. } => {
                self.walk_expr(tuple);
            }
        }
    }

    /// Consume a variable, recording violations if needed.
    fn consume_var(&mut self, name: &Var) {
        match self.ctx.consume(name) {
            ConsumeResult::Ok => {}
            ConsumeResult::NotInScope => {
                self.violations.push(DisciplineViolation::NotInScope {
                    name: name.to_string(),
                });
            }
            ConsumeResult::AlreadyConsumed => {
                self.violations.push(DisciplineViolation::Contraction {
                    name: name.to_string(),
                });
            }
        }
    }

    /// Check that two branch snapshots agree on linear variable consumption.
    fn check_branch_agreement(
        &mut self,
        left: &std::collections::HashMap<Var, bool>,
        right: &std::collections::HashMap<Var, bool>,
    ) {
        for (name, &left_consumed) in left {
            if let Some(&right_consumed) = right.get(name) {
                // Only check bindings that are linear
                if let Some(binding) = self.ctx.get(name) {
                    if binding.is_linear_type() || binding.is_linear_form() {
                        if left_consumed != right_consumed {
                            self.violations.push(DisciplineViolation::BranchDisagreement {
                                name: name.to_string(),
                            });
                        }
                    }
                }
            }
        }
    }
}

impl Default for LinearChecker {
    fn default() -> Self {
        Self::new()
    }
}
