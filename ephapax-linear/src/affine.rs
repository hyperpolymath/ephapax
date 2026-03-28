// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Affine Discipline Checker
//!
//! Enforces the affine substructural grammar:
//! - **Weakening allowed**: unused bindings are implicitly dropped at scope exit.
//! - **No contraction**: no binding may be used more than once.
//! - **Branch freedom**: branches may disagree on consumption — unconsumed
//!   values are implicitly dropped in the non-consuming branch.
//! - **Region cleanup**: unconsumed region-bound values are implicitly dropped,
//!   but non-memory resources trigger a warning (item 6 of the roadmap).
//! - **`drop(e)` permitted**: explicit weakening is valid syntax.
//! - **`let` unrestricted**: `let` may bind values of any type, including
//!   linear types (implicit drop at scope exit is allowed).
//! - **`let!` islands**: `let!` is still valid and creates a linear island —
//!   the body MUST consume the binding exactly once even in affine context.
//!
//! See `grammar/affine.ebnf` for the formal grammar specification.

use crate::context::{BindingForm, ConsumeResult, Context};
use crate::DisciplineViolation;
use ephapax_syntax::{Decl, Expr, ExprKind, Module, Var};

/// Affine discipline checker.
///
/// Walks the ephapax AST and verifies that every expression conforms to
/// the affine substructural grammar — weakening allowed, no contraction.
pub struct AffineChecker {
    ctx: Context,
    violations: Vec<DisciplineViolation>,
}

impl AffineChecker {
    /// Create a new affine discipline checker.
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
            violations: Vec::new(),
        }
    }

    /// Check a single expression under the affine discipline.
    pub fn check(&mut self, expr: &Expr) -> Result<(), Vec<DisciplineViolation>> {
        self.walk_expr(expr);
        if self.violations.is_empty() {
            Ok(())
        } else {
            Err(self.violations.clone())
        }
    }

    /// Check an entire module under the affine discipline.
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
            Decl::Fn { params, body, .. } => {
                for (name, ty) in params {
                    self.ctx
                        .bind(name.clone(), BindingForm::Param, Some(ty.clone()));
                }

                self.walk_expr(body);

                // In affine: params do NOT need to be consumed (weakening OK)
                // But we clean up the context
                for (name, _) in params {
                    self.ctx.unbind(name);
                }
            }
            Decl::Type { .. } => {}
        }
    }

    /// Walk an expression, enforcing affine discipline.
    fn walk_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(_) => {}

            ExprKind::Var(name) => {
                self.consume_var(name);
            }

            // --- let (affine: any type allowed, implicit drop OK) ---
            ExprKind::Let {
                name,
                ty,
                value,
                body,
            } => {
                self.walk_expr(value);
                self.ctx.bind(name.clone(), BindingForm::Let, ty.clone());
                self.walk_expr(body);

                // In affine: unconsumed is OK (weakening), but warn if
                // the binding is linear-typed and region-bound (potential
                // non-memory resource leak at implicit drop).
                if let Some(binding) = self.ctx.get(name) {
                    if binding.is_linear_type() && !binding.consumed {
                        if let Some(region) = &binding.region {
                            self.violations
                                .push(DisciplineViolation::ImplicitDropWarning {
                                    region: region.to_string(),
                                    name: name.to_string(),
                                });
                        }
                    }
                }
                self.ctx.unbind(name);
            }

            // --- let! (linear island in affine context) ---
            // Even in affine grammar, let! demands exactly-once consumption.
            // This is the dyadic contract: let! always means linear.
            ExprKind::LetLin {
                name,
                ty,
                value,
                body,
            } => {
                self.walk_expr(value);
                self.ctx
                    .bind(name.clone(), BindingForm::LetBang, ty.clone());
                self.walk_expr(body);

                // let! MUST be consumed — even in affine grammar
                if let Some(binding) = self.ctx.get(name) {
                    if !binding.consumed {
                        self.violations
                            .push(DisciplineViolation::WeakeningForbidden {
                                name: name.to_string(),
                            });
                    }
                }
                self.ctx.unbind(name);
            }

            ExprKind::Lambda {
                param,
                param_ty,
                body,
            } => {
                self.ctx
                    .bind(param.clone(), BindingForm::Param, Some(param_ty.clone()));
                self.walk_expr(body);
                // Affine: unconsumed param is OK
                self.ctx.unbind(param);
            }

            ExprKind::App { func, arg } => {
                self.walk_expr(func);
                self.walk_expr(arg);
            }

            ExprKind::Pair { left, right } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }

            ExprKind::Fst(inner) | ExprKind::Snd(inner) => {
                self.walk_expr(inner);
            }

            ExprKind::Inl { value, .. } | ExprKind::Inr { value, .. } => {
                self.walk_expr(value);
            }

            // --- Case: branches may disagree (affine allows it) ---
            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => {
                self.walk_expr(scrutinee);

                let pre_snapshot = self.ctx.snapshot_consumption();

                self.ctx.bind(left_var.clone(), BindingForm::Let, None);
                self.walk_expr(left_body);
                self.ctx.unbind(left_var);
                let left_snapshot = self.ctx.snapshot_consumption();

                self.ctx.restore_consumption(&pre_snapshot);
                self.ctx.bind(right_var.clone(), BindingForm::Let, None);
                self.walk_expr(right_body);
                self.ctx.unbind(right_var);
                let right_snapshot = self.ctx.snapshot_consumption();

                // Affine: no branch agreement required.
                // Merge conservatively: consumed if consumed in EITHER branch
                // (the other branch implicitly drops).
                self.merge_affine_branches(&left_snapshot, &right_snapshot);
            }

            // --- If: branches may disagree ---
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

                // Affine merge: consumed if consumed in either branch
                self.merge_affine_branches(&then_snapshot, &else_snapshot);
            }

            // --- Region: implicit drop warnings emitted at binding site ---
            ExprKind::Region { name, body } => {
                self.ctx.enter_region(name.clone());
                self.walk_expr(body);
                self.ctx.exit_region();
            }

            ExprKind::Borrow(inner) | ExprKind::Deref(inner) => {
                self.walk_expr(inner);
            }

            // --- Drop: PERMITTED in affine grammar ---
            ExprKind::Drop(inner) => {
                self.walk_expr(inner);
                // No violation — explicit weakening is fine in affine
            }

            ExprKind::Copy(inner) => {
                self.walk_expr(inner);
            }

            ExprKind::Block(exprs) => {
                for e in exprs {
                    self.walk_expr(e);
                }
            }

            ExprKind::FFI { args, .. } => {
                for arg in args {
                    self.walk_expr(arg);
                }
            }

            ExprKind::BinOp { left, right, .. } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }
            ExprKind::UnaryOp { operand, .. } => {
                self.walk_expr(operand);
            }

            ExprKind::StringNew { .. } => {}
            ExprKind::StringConcat { left, right } => {
                self.walk_expr(left);
                self.walk_expr(right);
            }
            ExprKind::StringLen(inner) => {
                self.walk_expr(inner);
            }

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

            // --- Effects ---
            ExprKind::Perform { args, .. } => {
                for arg in args {
                    self.walk_expr(arg);
                }
            }
            ExprKind::Handle { body, clauses } => {
                self.walk_expr(body);
                for clause in clauses {
                    // Clause params are fresh bindings in the handler body
                    for param in &clause.params {
                        self.ctx.bind(param.clone(), BindingForm::Let, None);
                    }
                    self.walk_expr(&clause.body);
                    for param in clause.params.iter().rev() {
                        self.ctx.unbind(param);
                    }
                }
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

    /// Merge branch consumption for affine discipline.
    /// In affine: a variable is consumed if consumed in EITHER branch
    /// (the non-consuming branch implicitly drops it).
    fn merge_affine_branches(
        &mut self,
        left: &std::collections::HashMap<Var, bool>,
        right: &std::collections::HashMap<Var, bool>,
    ) {
        let mut merged = left.clone();
        for (name, &right_consumed) in right {
            let entry = merged.entry(name.clone()).or_insert(false);
            *entry = *entry || right_consumed;
        }
        self.ctx.restore_consumption(&merged);
    }
}

impl Default for AffineChecker {
    fn default() -> Self {
        Self::new()
    }
}
