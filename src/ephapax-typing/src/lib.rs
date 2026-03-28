#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Type Checker (Dyadic Design)
//!
//! Implements the dyadic type system where BOTH qualifiers coexist per-program:
//! - **`let` (affine)**: Values used ≤1 time (can be dropped implicitly)
//! - **`let!` (linear)**: Values used exactly 1 time (must be consumed)
//!
//! The dyadic property is per-binding, not a global mode. `let!` always means
//! exactly-once — there is no flag to weaken it. This matches the formal
//! semantics in Typing.v and the Orthogonality Lemma in RegionLinear.idr.
//!
//! Based on formal/Typing.v
//!
//! See [`discipline`] module for the complete rules reference.

pub mod discipline;

use ephapax_syntax::{
    BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, RegionName, Ty, UnaryOp, Var,
};
use std::collections::HashMap;
use thiserror::Error;

/// Type checking errors
#[derive(Error, Debug, Clone, PartialEq)]
pub enum TypeError {
    #[error("Linear variable `{0}` used more than once")]
    LinearVariableReused(Var),

    #[error("Linear variable `{0}` not consumed")]
    LinearVariableNotConsumed(Var),

    #[error("Variable `{0}` not found in scope")]
    UnboundVariable(Var),

    #[error("Region `{0}` not active")]
    InactiveRegion(RegionName),

    #[error("Type mismatch: expected {expected:?}, found {found:?}")]
    TypeMismatch { expected: Ty, found: Ty },

    #[error("Cannot copy linear type {0:?}")]
    CannotCopyLinear(Ty),

    #[error("Cannot drop unrestricted value (not needed)")]
    UnnecessaryDrop,

    #[error("Branch linearity mismatch: both branches must consume same linear variables")]
    BranchLinearityMismatch,

    #[error("Branch linearity mismatch: variable `{var}` is {then_status} in then-branch but {else_status} in else-branch")]
    BranchLinearityMismatchDetailed {
        var: Var,
        then_status: &'static str,
        else_status: &'static str,
    },

    #[error("Value of type {ty:?} escapes region `{region}`")]
    RegionEscape { region: RegionName, ty: Ty },

    #[error("Linear variable `{var}` in region `{region}` not consumed before region exit")]
    RegionLinearNotConsumed { var: Var, region: RegionName },

    #[error("String literal must be allocated with String.new@region(\"...\")")]
    UnallocatedStringLiteral,

    #[error("Type annotation mismatch: declared {declared:?}, but value has type {actual:?}")]
    AnnotationMismatch { declared: Ty, actual: Ty },
}

/// How a binding was introduced — determines the substructural discipline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingForm {
    /// `let x = ...` — affine discipline: use at most once, implicit drop OK.
    Let,
    /// `let! x = ...` — linear discipline: use exactly once, no implicit drop.
    LetBang,
    /// Function parameter — linear discipline if type is linear, affine otherwise.
    Param,
}

/// Typing context entry
#[derive(Debug, Clone)]
struct CtxEntry {
    ty: Ty,
    used: bool,
    /// How this binding was introduced — `let` (affine) vs `let!` (linear).
    binding_form: BindingForm,
    /// Which region this variable was bound in (None = top-level / no region).
    /// Used by the region-linear fusion to track which variables belong to
    /// which region, so we can check AllLinearsConsumed at region exit.
    region: Option<RegionName>,
}

impl CtxEntry {
    /// Whether this binding demands exactly-once consumption.
    /// - `let!`: ALWAYS demands consumption (the whole point of let!)
    /// - `let`: NEVER demands (affine — implicit drop is allowed)
    /// - param: demands if the type is linear
    fn demands_consumption(&self) -> bool {
        match self.binding_form {
            BindingForm::LetBang => true,
            BindingForm::Let => false,
            BindingForm::Param => self.ty.is_linear(),
        }
    }
}

/// Typing context: tracks variables and their usage
#[derive(Debug, Clone, Default)]
pub struct Context {
    /// Variable bindings: name -> (type, used)
    vars: HashMap<Var, CtxEntry>,
    /// Active regions
    regions: Vec<RegionName>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Extend context with new binding, tagged with the current region and binding form.
    pub fn extend(&mut self, name: Var, ty: Ty, binding_form: BindingForm) {
        let region = self.regions.last().cloned();
        self.vars.insert(
            name,
            CtxEntry {
                ty,
                used: false,
                binding_form,
                region,
            },
        );
    }

    /// Look up variable type
    pub fn lookup(&self, name: &Var) -> Option<&Ty> {
        self.vars.get(name).map(|e| &e.ty)
    }

    /// Mark variable as used (for linear variables)
    pub fn mark_used(&mut self, name: &Var) -> Result<(), TypeError> {
        if let Some(entry) = self.vars.get_mut(name) {
            if entry.ty.is_linear() && entry.used {
                return Err(TypeError::LinearVariableReused(name.clone()));
            }
            entry.used = true;
            Ok(())
        } else {
            Err(TypeError::UnboundVariable(name.clone()))
        }
    }

    /// Check all bindings that demand consumption have been consumed.
    /// - `let!` bindings: ALWAYS must be consumed (linear discipline)
    /// - `let` bindings: NEVER must be consumed (affine — implicit drop OK)
    /// - params: must be consumed if the type is linear
    pub fn check_all_consumed(&self) -> Result<(), TypeError> {
        for (name, entry) in &self.vars {
            if entry.demands_consumption() && !entry.used {
                return Err(TypeError::LinearVariableNotConsumed(name.clone()));
            }
        }
        Ok(())
    }

    /// Enter a new region
    pub fn enter_region(&mut self, name: RegionName) {
        self.regions.push(name);
    }

    /// Exit region
    pub fn exit_region(&mut self) {
        self.regions.pop();
    }

    /// Check if region is active
    pub fn region_active(&self, name: &RegionName) -> bool {
        self.regions.contains(name)
    }

    /// Create a snapshot of the current context for branch checking.
    /// Both branches will start from this same state.
    pub fn snapshot(&self) -> Self {
        self.clone()
    }

    /// Check that two contexts agree on linear variable usage.
    /// Both branches must consume exactly the same set of linear variables.
    /// Returns Ok(()) if they agree, or an error indicating which variable differs.
    pub fn check_branch_agreement(&self, other: &Context) -> Result<(), TypeError> {
        // Check all variables that demand consumption (let! and linear params).
        // Affine (let) bindings don't need branch agreement — one branch can
        // consume while the other implicitly drops.
        for (name, entry) in &self.vars {
            if !entry.demands_consumption() {
                continue; // Affine bindings don't need branch agreement
            }

            match other.vars.get(name) {
                Some(other_entry) => {
                    if entry.used != other_entry.used {
                        return Err(TypeError::BranchLinearityMismatchDetailed {
                            var: name.clone(),
                            then_status: if entry.used {
                                "consumed"
                            } else {
                                "not consumed"
                            },
                            else_status: if other_entry.used {
                                "consumed"
                            } else {
                                "not consumed"
                            },
                        });
                    }
                }
                None => {
                    // Variable exists in self but not in other - shouldn't happen
                    // if both started from the same snapshot
                    return Err(TypeError::BranchLinearityMismatch);
                }
            }
        }

        // Check for variables in other that aren't in self (shouldn't happen)
        for (name, entry) in &other.vars {
            if !entry.ty.is_linear() {
                continue;
            }
            if !self.vars.contains_key(name) {
                return Err(TypeError::BranchLinearityMismatch);
            }
        }

        Ok(())
    }

    /// Merge two contexts after branch checking.
    /// Assumes branch agreement has already been verified.
    /// Takes the "used" status from either branch (they should be identical).
    pub fn merge_branches(&mut self, _other: &Context) {
        // After branch agreement is verified, the usage should be identical.
        // The current context (self) already has the correct usage from one branch.
        // We keep it as-is since both branches agree.
    }
}

/// Type checker state
pub struct TypeChecker {
    ctx: Context,
}

impl TypeChecker {
    /// Create a new type checker.
    /// The dyadic property is per-binding (`let` vs `let!`), not a global mode.
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
        }
    }

    /// Type check an expression
    pub fn check(&mut self, expr: &Expr) -> Result<Ty, TypeError> {
        match &expr.kind {
            ExprKind::Lit(lit) => self.check_lit(lit),
            ExprKind::Var(name) => self.check_var(name),
            ExprKind::StringNew { region, .. } => self.check_string_new(region),
            ExprKind::StringConcat { left, right } => self.check_string_concat(left, right),
            ExprKind::Let {
                name,
                ty,
                value,
                body,
            } => self.check_let(name, ty.as_ref(), value, body),
            ExprKind::Lambda {
                param,
                param_ty,
                body,
            } => self.check_lambda(param, param_ty, body),
            ExprKind::App { func, arg } => self.check_app(func, arg),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.check_if(cond, then_branch, else_branch),
            ExprKind::Region { name, body } => self.check_region(name, body),
            ExprKind::Borrow(inner) => self.check_borrow(inner),
            ExprKind::Drop(inner) => self.check_drop(inner),
            ExprKind::Copy(inner) => self.check_copy(inner),
            ExprKind::StringLen(inner) => self.check_string_len(inner),
            ExprKind::LetLin {
                name,
                ty,
                value,
                body,
            } => self.check_let_lin(name, ty.as_ref(), value, body),
            ExprKind::Pair { left, right } => self.check_pair(left, right),
            ExprKind::Fst(inner) => self.check_fst(inner),
            ExprKind::Snd(inner) => self.check_snd(inner),
            ExprKind::Inl { ty, value } => self.check_inl(ty, value),
            ExprKind::Inr { ty, value } => self.check_inr(ty, value),
            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => self.check_case(scrutinee, left_var, left_body, right_var, right_body),
            ExprKind::Deref(inner) => self.check_deref(inner),
            ExprKind::Block(exprs) => self.check_block(exprs),
            ExprKind::BinOp { op, left, right } => self.check_binop(*op, left, right),
            ExprKind::UnaryOp { op, operand } => self.check_unaryop(*op, operand),
            ExprKind::ListLit(elements) => self.check_list_lit(elements),
            ExprKind::ListIndex { list, index } => self.check_list_index(list, index),
            ExprKind::TupleLit(elements) => self.check_tuple_lit(elements),
            ExprKind::TupleIndex { tuple, index } => self.check_tuple_index(tuple, *index),
            ExprKind::FFI { args, .. } => self.check_ffi(args),
        }
    }

    fn check_lit(&self, lit: &Literal) -> Result<Ty, TypeError> {
        Ok(match lit {
            Literal::Unit => Ty::Base(BaseTy::Unit),
            Literal::Bool(_) => Ty::Base(BaseTy::Bool),
            Literal::I32(_) => Ty::Base(BaseTy::I32),
            Literal::I64(_) => Ty::Base(BaseTy::I64),
            Literal::F32(_) => Ty::Base(BaseTy::F32),
            Literal::F64(_) => Ty::Base(BaseTy::F64),
            Literal::String(_) => {
                return Err(TypeError::UnallocatedStringLiteral);
            }
        })
    }

    fn check_var(&mut self, name: &Var) -> Result<Ty, TypeError> {
        let ty = self
            .ctx
            .lookup(name)
            .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?
            .clone();

        // Always mark as used — the demands_consumption() check at scope
        // exit decides whether non-use is an error, not this lookup.
        self.ctx.mark_used(name)?;

        Ok(ty)
    }

    fn check_string_new(&self, region: &RegionName) -> Result<Ty, TypeError> {
        if !self.ctx.region_active(region) {
            return Err(TypeError::InactiveRegion(region.clone()));
        }
        Ok(Ty::String(region.clone()))
    }

    fn check_string_concat(&mut self, left: &Expr, right: &Expr) -> Result<Ty, TypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        match (&left_ty, &right_ty) {
            (Ty::String(r1), Ty::String(r2)) if r1 == r2 => Ok(Ty::String(r1.clone())),
            _ => Err(TypeError::TypeMismatch {
                expected: left_ty,
                found: right_ty,
            }),
        }
    }

    fn check_let(
        &mut self,
        name: &Var,
        ty_ann: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;

        // If a type annotation is present, verify it matches the inferred type
        if let Some(declared) = ty_ann {
            if *declared != value_ty {
                return Err(TypeError::AnnotationMismatch {
                    declared: declared.clone(),
                    actual: value_ty,
                });
            }
        }

        self.ctx
            .extend(name.clone(), value_ty.clone(), BindingForm::Let);
        let body_ty = self.check(body)?;

        // `let` is AFFINE — unconsumed bindings are allowed (implicit drop).
        // No consumption check here. The affine discipline permits weakening.

        Ok(body_ty)
    }

    fn check_lambda(&mut self, param: &Var, param_ty: &Ty, body: &Expr) -> Result<Ty, TypeError> {
        self.ctx
            .extend(param.clone(), param_ty.clone(), BindingForm::Param);
        let body_ty = self.check(body)?;

        // Params use demands_consumption(): linear types must be consumed,
        // unrestricted types can be dropped.
        if let Some(entry) = self.ctx.vars.get(param) {
            if entry.demands_consumption() && !entry.used {
                return Err(TypeError::LinearVariableNotConsumed(param.clone()));
            }
        }

        Ok(Ty::Fun {
            param: Box::new(param_ty.clone()),
            ret: Box::new(body_ty),
        })
    }

    fn check_app(&mut self, func: &Expr, arg: &Expr) -> Result<Ty, TypeError> {
        let func_ty = self.check(func)?;
        let arg_ty = self.check(arg)?;

        match func_ty {
            Ty::Fun { param, ret } => {
                if *param == arg_ty {
                    Ok(*ret)
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: *param,
                        found: arg_ty,
                    })
                }
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Fun {
                    param: Box::new(arg_ty.clone()),
                    ret: Box::new(Ty::Base(BaseTy::Unit)),
                },
                found: func_ty,
            }),
        }
    }

    fn check_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Ty, TypeError> {
        let cond_ty = self.check(cond)?;

        if cond_ty != Ty::Base(BaseTy::Bool) {
            return Err(TypeError::TypeMismatch {
                expected: Ty::Base(BaseTy::Bool),
                found: cond_ty,
            });
        }

        // Snapshot context after condition - both branches start from here
        let ctx_after_cond = self.ctx.snapshot();

        // Check then-branch with current context
        let then_ty = self.check(then_branch)?;
        let ctx_after_then = self.ctx.snapshot();

        // Restore context to post-condition state for else-branch
        self.ctx = ctx_after_cond;

        // Check else-branch
        let else_ty = self.check(else_branch)?;
        let ctx_after_else = self.ctx.snapshot();

        // Types must match
        if then_ty != else_ty {
            return Err(TypeError::TypeMismatch {
                expected: then_ty,
                found: else_ty,
            });
        }

        // Both branches must consume the same linear variables
        ctx_after_then.check_branch_agreement(&ctx_after_else)?;

        // Merge contexts (they're identical for linear vars after agreement check)
        // Keep ctx_after_then as the result (could use either)
        self.ctx = ctx_after_then;

        Ok(then_ty)
    }

    /// Type check a region block: `region r: { body }`
    ///
    /// Implements the region-linear fusion rules from the formal proofs
    /// (RegionLinear.idr):
    ///
    /// 1. **NoRegionInType**: The return type of the body must NOT reference
    ///    region `r`. This prevents values from escaping their region.
    ///    This rule is ORTHOGONAL to the qualifier — it applies identically
    ///    to affine and linear bindings (Orthogonality Lemma).
    ///
    /// 2. **AllLinearsConsumed**: All linear variables bound within region `r`
    ///    must be consumed before the region exits. Affine variables may be
    ///    implicitly dropped (the region's arena deallocator handles cleanup).
    ///
    /// 3. **Region Safety**: After exit, the region is no longer active.
    ///    Any attempt to use a variable from this region is a type error
    ///    (InactiveRegion).
    fn check_region(&mut self, name: &RegionName, body: &Expr) -> Result<Ty, TypeError> {
        // Enter the region — all bindings created inside will be tagged with `name`
        self.ctx.enter_region(name.clone());

        // Type check the body
        let body_ty = self.check(body)?;

        // === Rule 1: NoRegionInType (No Escape) ===
        // The return type must not reference this region.
        // This is the ONE rule that prevents region escape, and it applies
        // to both affine and linear bindings identically.
        if body_ty.references_region(name) {
            // Exit region before returning error (maintain invariant)
            self.ctx.exit_region();
            return Err(TypeError::RegionEscape {
                region: name.clone(),
                ty: body_ty,
            });
        }

        // === Rule 2: Consumption at region exit ===
        // Only bindings that DEMAND consumption (let!, linear params) must
        // have been consumed. Affine (let) bindings are implicitly dropped —
        // the region's arena deallocator frees the memory.
        for (var_name, entry) in &self.ctx.vars {
            // Only check variables that belong to THIS region
            if entry.region.as_ref() != Some(name) {
                continue;
            }

            // Only check bindings that demand consumption
            if entry.demands_consumption() && !entry.used {
                let var = var_name.clone();
                let region = name.clone();
                self.ctx.exit_region();
                return Err(TypeError::RegionLinearNotConsumed { var, region });
            }

            // Affine (let) bindings: no error — implicit drop is fine.
            // The region's arena deallocator frees the memory.
        }

        // === Rule 3: Region Safety ===
        // Exit the region. After this, the region is no longer active.
        // Any StringNew@name or other allocation attempt will fail with
        // InactiveRegion.
        self.ctx.exit_region();

        Ok(body_ty)
    }

    fn check_borrow(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        // Borrowing does NOT consume the resource.
        // Per Coq rule T_Borrow: output context G is same as input.
        // We look up the type without marking as used.
        match &inner.kind {
            ExprKind::Var(name) => {
                // For variables, look up type without consuming
                let ty = self
                    .ctx
                    .lookup(name)
                    .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?
                    .clone();
                Ok(Ty::Borrow(Box::new(ty)))
            }
            _ => {
                // For complex expressions, we need to evaluate them but borrowing
                // only makes sense for lvalues (variables, field accesses).
                // For now, check the expression normally and wrap in Borrow.
                // This may consume linear resources, which is semantically correct
                // for temporary borrows of computed values.
                let inner_ty = self.check(inner)?;
                Ok(Ty::Borrow(Box::new(inner_ty)))
            }
        }
    }

    fn check_drop(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        if !inner_ty.is_linear() {
            return Err(TypeError::UnnecessaryDrop);
        }

        Ok(Ty::Base(BaseTy::Unit))
    }

    fn check_copy(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        if inner_ty.is_linear() {
            return Err(TypeError::CannotCopyLinear(inner_ty));
        }

        Ok(Ty::Prod {
            left: Box::new(inner_ty.clone()),
            right: Box::new(inner_ty),
        })
    }

    fn check_string_len(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::String(_) => Ok(Ty::Base(BaseTy::I32)),
            Ty::Borrow(ref boxed) => match boxed.as_ref() {
                Ty::String(_) => Ok(Ty::Base(BaseTy::I32)),
                _ => Err(TypeError::TypeMismatch {
                    expected: Ty::String("_".into()),
                    found: inner_ty,
                }),
            },
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::String("_".into()),
                found: inner_ty,
            }),
        }
    }

    fn check_let_lin(
        &mut self,
        name: &Var,
        ty_ann: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, TypeError> {
        // Same as let, but explicitly marked linear
        let value_ty = self.check(value)?;

        // If a type annotation is present, verify it matches the inferred type
        if let Some(declared) = ty_ann {
            if *declared != value_ty {
                return Err(TypeError::AnnotationMismatch {
                    declared: declared.clone(),
                    actual: value_ty,
                });
            }
        }

        self.ctx
            .extend(name.clone(), value_ty.clone(), BindingForm::LetBang);
        let body_ty = self.check(body)?;

        // let! bindings MUST be consumed — regardless of type.
        // This is the linear discipline: even I32 bound with let! must be used.
        // The programmer opted into exactly-once by choosing let!.
        if let Some(entry) = self.ctx.vars.get(name) {
            if !entry.used {
                return Err(TypeError::LinearVariableNotConsumed(name.clone()));
            }
        }

        Ok(body_ty)
    }

    fn check_pair(&mut self, left: &Expr, right: &Expr) -> Result<Ty, TypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        Ok(Ty::Prod {
            left: Box::new(left_ty),
            right: Box::new(right_ty),
        })
    }

    fn check_fst(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Prod { left, right } => {
                // In linear, projecting consumes the pair.
                // The other component must be dropped or the type must be unrestricted.
                if right.is_linear() {
                    // Can't just take first and discard linear second
                    return Err(TypeError::LinearVariableNotConsumed("_pair_snd".into()));
                }
                Ok(*left)
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Prod {
                    left: Box::new(Ty::Base(BaseTy::Unit)),
                    right: Box::new(Ty::Base(BaseTy::Unit)),
                },
                found: inner_ty,
            }),
        }
    }

    fn check_snd(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Prod { left, right } => {
                // In linear, projecting consumes the pair.
                if left.is_linear() {
                    return Err(TypeError::LinearVariableNotConsumed("_pair_fst".into()));
                }
                Ok(*right)
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Prod {
                    left: Box::new(Ty::Base(BaseTy::Unit)),
                    right: Box::new(Ty::Base(BaseTy::Unit)),
                },
                found: inner_ty,
            }),
        }
    }

    fn check_inl(&mut self, ty: &Ty, value: &Expr) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;

        // ty is the RIGHT type of the sum
        Ok(Ty::Sum {
            left: Box::new(value_ty),
            right: Box::new(ty.clone()),
        })
    }

    fn check_inr(&mut self, ty: &Ty, value: &Expr) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;

        // ty is the LEFT type of the sum
        Ok(Ty::Sum {
            left: Box::new(ty.clone()),
            right: Box::new(value_ty),
        })
    }

    fn check_case(
        &mut self,
        scrutinee: &Expr,
        left_var: &Var,
        left_body: &Expr,
        right_var: &Var,
        right_body: &Expr,
    ) -> Result<Ty, TypeError> {
        let scrutinee_ty = self.check(scrutinee)?;

        match scrutinee_ty {
            Ty::Sum { left, right } => {
                // Snapshot context after scrutinee - both branches start from here
                let ctx_after_scrutinee = self.ctx.snapshot();

                // Check left branch — case bindings follow Param discipline
                // (linear types must be consumed, unrestricted can be dropped)
                self.ctx
                    .extend(left_var.clone(), *left.clone(), BindingForm::Param);
                let left_result_ty = self.check(left_body)?;

                // Check consumption based on binding discipline
                if let Some(entry) = self.ctx.vars.get(left_var) {
                    if entry.demands_consumption() && !entry.used {
                        return Err(TypeError::LinearVariableNotConsumed(left_var.clone()));
                    }
                }

                // Remove branch-specific variable before comparison
                let mut ctx_after_left = self.ctx.snapshot();
                ctx_after_left.vars.remove(left_var);

                // Restore context for right branch
                self.ctx = ctx_after_scrutinee;

                // Check right branch
                self.ctx
                    .extend(right_var.clone(), *right.clone(), BindingForm::Param);
                let right_result_ty = self.check(right_body)?;

                // Check consumption based on binding discipline
                if let Some(entry) = self.ctx.vars.get(right_var) {
                    if entry.demands_consumption() && !entry.used {
                        return Err(TypeError::LinearVariableNotConsumed(right_var.clone()));
                    }
                }

                // Remove branch-specific variable before comparison
                let mut ctx_after_right = self.ctx.snapshot();
                ctx_after_right.vars.remove(right_var);

                // Both branches must have same type
                if left_result_ty != right_result_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: left_result_ty,
                        found: right_result_ty,
                    });
                }

                // Both branches must consume same linear variables from outer scope
                ctx_after_left.check_branch_agreement(&ctx_after_right)?;

                // Keep the left context as result (with left_var removed)
                self.ctx = ctx_after_left;

                Ok(left_result_ty)
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Sum {
                    left: Box::new(Ty::Base(BaseTy::Unit)),
                    right: Box::new(Ty::Base(BaseTy::Unit)),
                },
                found: scrutinee_ty,
            }),
        }
    }

    fn check_deref(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Borrow(boxed) => Ok(*boxed),
            Ty::Ref { inner, .. } => Ok(*inner),
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Borrow(Box::new(Ty::Base(BaseTy::Unit))),
                found: inner_ty,
            }),
        }
    }

    fn check_block(&mut self, exprs: &[Expr]) -> Result<Ty, TypeError> {
        if exprs.is_empty() {
            return Ok(Ty::Base(BaseTy::Unit));
        }

        let mut result_ty = Ty::Base(BaseTy::Unit);
        for expr in exprs {
            result_ty = self.check(expr)?;
        }
        Ok(result_ty)
    }

    fn check_binop(&mut self, op: BinOp, left: &Expr, right: &Expr) -> Result<Ty, TypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        // Both operands must be same numeric type
        if left_ty != right_ty {
            return Err(TypeError::TypeMismatch {
                expected: left_ty,
                found: right_ty,
            });
        }

        match op {
            // Arithmetic ops return same type
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => match &left_ty {
                Ty::Base(BaseTy::I32)
                | Ty::Base(BaseTy::I64)
                | Ty::Base(BaseTy::F32)
                | Ty::Base(BaseTy::F64) => Ok(left_ty),
                _ => Err(TypeError::TypeMismatch {
                    expected: Ty::Base(BaseTy::I32),
                    found: left_ty,
                }),
            },
            // Comparison ops return Bool
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                Ok(Ty::Base(BaseTy::Bool))
            }
            // Logical ops require Bool and return Bool
            BinOp::And | BinOp::Or => {
                if left_ty != Ty::Base(BaseTy::Bool) {
                    return Err(TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::Bool),
                        found: left_ty,
                    });
                }
                Ok(Ty::Base(BaseTy::Bool))
            }
        }
    }

    fn check_unaryop(&mut self, op: UnaryOp, operand: &Expr) -> Result<Ty, TypeError> {
        let operand_ty = self.check(operand)?;

        match op {
            UnaryOp::Not => {
                if operand_ty != Ty::Base(BaseTy::Bool) {
                    return Err(TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::Bool),
                        found: operand_ty,
                    });
                }
                Ok(Ty::Base(BaseTy::Bool))
            }
            UnaryOp::Neg => match &operand_ty {
                Ty::Base(BaseTy::I32)
                | Ty::Base(BaseTy::I64)
                | Ty::Base(BaseTy::F32)
                | Ty::Base(BaseTy::F64) => Ok(operand_ty),
                _ => Err(TypeError::TypeMismatch {
                    expected: Ty::Base(BaseTy::I32),
                    found: operand_ty,
                }),
            },
        }
    }

    fn check_list_lit(&mut self, elements: &[Expr]) -> Result<Ty, TypeError> {
        if elements.is_empty() {
            // Empty list - we need a type annotation to know the element type
            // For now, default to [I32]
            return Ok(Ty::List(Box::new(Ty::Base(BaseTy::I32))));
        }

        // Check first element to determine list type
        let elem_ty = self.check(&elements[0])?;

        // Verify all elements have the same type
        for elem in &elements[1..] {
            let ty = self.check(elem)?;
            if ty != elem_ty {
                return Err(TypeError::TypeMismatch {
                    expected: elem_ty.clone(),
                    found: ty,
                });
            }
        }

        Ok(Ty::List(Box::new(elem_ty)))
    }

    fn check_list_index(&mut self, list: &Expr, index: &Expr) -> Result<Ty, TypeError> {
        let list_ty = self.check(list)?;
        let index_ty = self.check(index)?;

        // Index must be I32
        if index_ty != Ty::Base(BaseTy::I32) {
            return Err(TypeError::TypeMismatch {
                expected: Ty::Base(BaseTy::I32),
                found: index_ty,
            });
        }

        // List must be List(T)
        match list_ty {
            Ty::List(elem_ty) => Ok(*elem_ty),
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::List(Box::new(Ty::Base(BaseTy::I32))), // example
                found: list_ty,
            }),
        }
    }

    fn check_tuple_lit(&mut self, elements: &[Expr]) -> Result<Ty, TypeError> {
        if elements.is_empty() {
            return Ok(Ty::Base(BaseTy::Unit));
        }

        if elements.len() == 1 {
            // Single element - just return its type (not a tuple)
            return self.check(&elements[0]);
        }

        if elements.len() == 2 {
            // 2-element tuple - use Pair for backward compatibility
            let left_ty = self.check(&elements[0])?;
            let right_ty = self.check(&elements[1])?;
            return Ok(Ty::Prod {
                left: Box::new(left_ty),
                right: Box::new(right_ty),
            });
        }

        // 3+ elements - use Tuple
        let mut elem_types = Vec::new();
        for elem in elements {
            elem_types.push(self.check(elem)?);
        }
        Ok(Ty::Tuple(elem_types))
    }

    fn check_tuple_index(&mut self, tuple: &Expr, index: usize) -> Result<Ty, TypeError> {
        let tuple_ty = self.check(tuple)?;

        match &tuple_ty {
            // 2-element tuple (Prod)
            Ty::Prod { left, right } => {
                if index == 0 {
                    Ok((**left).clone())
                } else if index == 1 {
                    Ok((**right).clone())
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::Unit), // placeholder
                        found: tuple_ty,
                    })
                }
            }
            // N-element tuple
            Ty::Tuple(elem_types) => {
                if index < elem_types.len() {
                    Ok(elem_types[index].clone())
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::Unit), // placeholder
                        found: Ty::Tuple(elem_types.clone()),
                    })
                }
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::Tuple(vec![]), // placeholder
                found: tuple_ty.clone(),
            }),
        }
    }

    /// Type-check an FFI call.
    ///
    /// FFI calls are the boundary between Ephapax and native code (Zig/C).
    /// String literal arguments are allowed WITHOUT region allocation — they
    /// become temporary C strings (null-terminated pointers) at the FFI boundary.
    /// This is safe because the C function receives a copy; the string doesn't
    /// need to be region-managed.
    ///
    /// Linear variables passed to FFI are consumed (counts as consumption).
    /// Return type is I64 (opaque C handle).
    fn check_ffi(&mut self, args: &[Expr]) -> Result<Ty, TypeError> {
        for arg in args {
            match &arg.kind {
                // Allow bare string literals in FFI context — they become
                // temporary C strings, not region-allocated Ephapax strings.
                ExprKind::Lit(Literal::String(_)) => {
                    // OK — string literal is passed as C string pointer
                }
                _ => {
                    self.check(arg)?;
                }
            }
        }
        Ok(Ty::Base(BaseTy::I64))
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

// Re-export for backward compatibility during migration.
// These will be removed once all downstream crates are updated.
/// Deprecated: The dyadic property is per-binding, not a global mode.
/// This type exists only for backward compatibility and will be removed.
#[deprecated(
    note = "Mode removed: dyadic property is per-binding (let vs let!), not a global switch"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Linear (the only real mode — kept for migration)
    Linear,
}

/// Deprecated: Use `type_check_module` directly.
#[deprecated(note = "Use type_check_module() — Mode parameter removed")]
#[allow(deprecated)]
pub fn type_check_module_with_mode(module: &Module, _mode: Mode) -> Result<(), TypeError> {
    type_check_module(module)
}

/// Deprecated: Use `type_check_expr` directly.
#[deprecated(note = "Use type_check_expr() — Mode parameter removed")]
#[allow(deprecated)]
pub fn type_check_expr_with_mode(expr: &Expr, _mode: Mode) -> Result<Ty, TypeError> {
    type_check_expr(expr)
}

/// Type check an entire module.
///
/// The dyadic property is per-binding: `let` is affine, `let!` is linear.
/// There is no global mode — `let!` always means exactly-once consumption.
pub fn type_check_module(module: &Module) -> Result<(), TypeError> {
    let mut tc = TypeChecker::new();

    // First pass: collect all function signatures
    for decl in &module.decls {
        if let Decl::Fn {
            name,
            params,
            ret_ty,
            ..
        } = decl
        {
            // Build function type from params and return type
            let fn_ty = params
                .iter()
                .rev()
                .fold(ret_ty.clone(), |acc, (_, param_ty)| Ty::Fun {
                    param: Box::new(param_ty.clone()),
                    ret: Box::new(acc),
                });
            tc.ctx.extend(name.clone(), fn_ty, BindingForm::Let);
        }
    }

    // Second pass: type check each function body
    for decl in &module.decls {
        match decl {
            Decl::Fn {
                name: _,
                params,
                ret_ty,
                body,
            } => {
                // Create a fresh context for function body with params
                let saved_ctx = tc.ctx.clone();

                for (param_name, param_ty) in params {
                    tc.ctx
                        .extend(param_name.clone(), param_ty.clone(), BindingForm::Param);
                }

                // Type check the body
                let body_ty = tc.check(body)?;

                // Verify return type matches
                if body_ty != *ret_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: ret_ty.clone(),
                        found: body_ty,
                    });
                }

                // Params that demand consumption must be consumed
                for (param_name, _param_ty) in params {
                    if let Some(entry) = tc.ctx.vars.get(param_name) {
                        if entry.demands_consumption() && !entry.used {
                            return Err(TypeError::LinearVariableNotConsumed(param_name.clone()));
                        }
                    }
                }

                // Restore context for next function
                tc.ctx = saved_ctx;
            }
            Decl::Type { .. } => {
                // Type aliases don't need runtime checking
            }
        }
    }

    Ok(())
}

/// Type check a single expression.
pub fn type_check_expr(expr: &Expr) -> Result<Ty, TypeError> {
    let mut tc = TypeChecker::new();
    tc.check(expr)
}

/// Type check a single expression (alias for type_check_expr).
pub fn type_check(expr: &Expr) -> Result<Ty, TypeError> {
    type_check_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::Span;

    fn dummy_expr(kind: ExprKind) -> Expr {
        Expr::new(kind, Span::dummy())
    }

    #[test]
    fn test_literal_typing() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Lit(Literal::I32(42)));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_linear_variable_reuse() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        // First use - OK
        let var = dummy_expr(ExprKind::Var("s".into()));
        assert!(tc.check(&var).is_ok());

        // Second use - Error
        let var2 = dummy_expr(ExprKind::Var("s".into()));
        assert!(matches!(
            tc.check(&var2),
            Err(TypeError::LinearVariableReused(_))
        ));
    }

    #[test]
    fn test_if_branch_agreement_both_consume() {
        // if true then drop(s) else drop(s)
        // Both branches consume s - should pass
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
            else_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
        });

        assert!(tc.check(&expr).is_ok());
    }

    #[test]
    fn test_if_branch_agreement_neither_consume() {
        // if true then 1 else 2
        // Neither branch consumes s - should pass (s unconsumed error later)
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });

        // The if itself passes - s is not consumed in either branch (agreement)
        assert!(tc.check(&expr).is_ok());
    }

    #[test]
    fn test_if_branch_disagreement_then_consumes() {
        // if true then drop(s) else 1
        // then-branch consumes s, else-branch does not - should FAIL
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        let result = tc.check(&expr);
        assert!(
            matches!(
                result,
                Err(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Expected BranchLinearityMismatchDetailed, got {:?}",
            result
        );
    }

    #[test]
    fn test_if_branch_disagreement_else_consumes() {
        // if true then 1 else drop(s)
        // then-branch does not consume s, else-branch does - should FAIL
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
            else_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
        });

        let result = tc.check(&expr);
        assert!(
            matches!(
                result,
                Err(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Expected BranchLinearityMismatchDetailed, got {:?}",
            result
        );
    }

    #[test]
    fn test_borrow_does_not_consume() {
        // Borrowing a variable should not consume it
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        // &s - borrow s
        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        let result = tc.check(&borrow_expr);
        assert!(result.is_ok());

        // s should still be available (not consumed)
        let var = dummy_expr(ExprKind::Var("s".into()));
        let result2 = tc.check(&var);
        assert!(result2.is_ok(), "Variable should not be consumed by borrow");
    }

    #[test]
    fn test_borrow_then_consume_ok() {
        // let len = String.len(&s) in drop(s)
        // Borrow s for len, then consume s - should pass
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        // First borrow
        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(tc.check(&borrow_expr).is_ok());

        // Then consume
        let drop_expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(tc.check(&drop_expr).is_ok());

        // Now s should be consumed
        let var = dummy_expr(ExprKind::Var("s".into()));
        assert!(matches!(
            tc.check(&var),
            Err(TypeError::LinearVariableReused(_))
        ));
    }

    // ===== String literal error (no longer panics) =====

    #[test]
    fn test_string_literal_error() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Lit(Literal::String("hello".to_string())));
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::UnallocatedStringLiteral)
        ));
    }

    // ===== Type annotation mismatch =====

    #[test]
    fn test_let_annotation_match() {
        // let x: I32 = 42 in x  — annotation matches, should pass
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::Base(BaseTy::I32)),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_let_annotation_mismatch() {
        // let x: Bool = 42 in x  — annotation doesn't match, should fail
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::Base(BaseTy::Bool)),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::AnnotationMismatch { .. })
        ));
    }

    // ===== Pair tests =====

    #[test]
    fn test_pair_typing() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        });
        assert_eq!(
            tc.check(&expr).unwrap(),
            Ty::Prod {
                left: Box::new(Ty::Base(BaseTy::I32)),
                right: Box::new(Ty::Base(BaseTy::Bool)),
            }
        );
    }

    #[test]
    fn test_fst_unrestricted() {
        // fst (1, true) — both components unrestricted, should pass
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Fst(Box::new(dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        }))));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_fst_linear_snd_rejected() {
        // fst (1, s) where s is linear — can't discard linear second component
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Fst(Box::new(dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Var("s".into()))),
        }))));
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::LinearVariableNotConsumed(_))
        ));
    }

    // ===== Sum type tests =====

    #[test]
    fn test_inl_typing() {
        let mut tc = TypeChecker::new();
        // inl[Bool] 42  → Sum(I32, Bool)
        let expr = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::Bool),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
        });
        assert_eq!(
            tc.check(&expr).unwrap(),
            Ty::Sum {
                left: Box::new(Ty::Base(BaseTy::I32)),
                right: Box::new(Ty::Base(BaseTy::Bool)),
            }
        );
    }

    #[test]
    fn test_case_analysis() {
        let mut tc = TypeChecker::new();
        // case (inl[Bool] 42) of { x => x, y => 0 }
        let expr = dummy_expr(ExprKind::Case {
            scrutinee: Box::new(dummy_expr(ExprKind::Inl {
                ty: Ty::Base(BaseTy::Bool),
                value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            })),
            left_var: "x".into(),
            left_body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
            right_var: "y".into(),
            right_body: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(0)))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    // ===== Region tests =====

    #[test]
    fn test_region_string_allocation() {
        let mut tc = TypeChecker::new();
        // region r { String.new@r("hello") } — string escapes region, should fail
        let expr = dummy_expr(ExprKind::Region {
            name: "r".into(),
            body: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
        });
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::RegionEscape { .. })
        ));
    }

    #[test]
    fn test_region_non_escaping() {
        let mut tc = TypeChecker::new();
        // region r { let! s = String.new@r("hi") in drop(s); () }
        // String is consumed inside region — should pass
        let expr = dummy_expr(ExprKind::Region {
            name: "r".into(),
            body: Box::new(dummy_expr(ExprKind::Block(vec![
                dummy_expr(ExprKind::LetLin {
                    name: "s".into(),
                    ty: None,
                    value: Box::new(dummy_expr(ExprKind::StringNew {
                        region: "r".into(),
                        value: "hi".to_string(),
                    })),
                    body: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                        ExprKind::Var("s".into()),
                    ))))),
                }),
                dummy_expr(ExprKind::Lit(Literal::Unit)),
            ]))),
        });
        assert!(tc.check(&expr).is_ok());
    }

    #[test]
    fn test_inactive_region_error() {
        let mut tc = TypeChecker::new();
        // String.new@r("hello") without entering region r — should fail
        let expr = dummy_expr(ExprKind::StringNew {
            region: "r".into(),
            value: "hello".to_string(),
        });
        assert!(matches!(tc.check(&expr), Err(TypeError::InactiveRegion(_))));
    }

    // ===== Function/lambda tests =====

    #[test]
    fn test_lambda_typing() {
        let mut tc = TypeChecker::new();
        // fn(x: I32) -> x
        let expr = dummy_expr(ExprKind::Lambda {
            param: "x".into(),
            param_ty: Ty::Base(BaseTy::I32),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        assert_eq!(
            tc.check(&expr).unwrap(),
            Ty::Fun {
                param: Box::new(Ty::Base(BaseTy::I32)),
                ret: Box::new(Ty::Base(BaseTy::I32)),
            }
        );
    }

    #[test]
    fn test_function_application() {
        let mut tc = TypeChecker::new();
        // (fn(x: I32) -> x) 42
        let expr = dummy_expr(ExprKind::App {
            func: Box::new(dummy_expr(ExprKind::Lambda {
                param: "x".into(),
                param_ty: Ty::Base(BaseTy::I32),
                body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
            })),
            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_application_type_mismatch() {
        let mut tc = TypeChecker::new();
        // (fn(x: I32) -> x) true  — passing Bool to I32 param
        let expr = dummy_expr(ExprKind::App {
            func: Box::new(dummy_expr(ExprKind::Lambda {
                param: "x".into(),
                param_ty: Ty::Base(BaseTy::I32),
                body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
            })),
            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        });
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::TypeMismatch { .. })
        ));
    }

    // ===== Copy/drop tests =====

    #[test]
    fn test_copy_unrestricted_ok() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Copy(Box::new(dummy_expr(ExprKind::Lit(
            Literal::I32(42),
        )))));
        assert_eq!(
            tc.check(&expr).unwrap(),
            Ty::Prod {
                left: Box::new(Ty::Base(BaseTy::I32)),
                right: Box::new(Ty::Base(BaseTy::I32)),
            }
        );
    }

    #[test]
    fn test_copy_linear_rejected() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Copy(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::CannotCopyLinear(_))
        ));
    }

    #[test]
    fn test_drop_linear_ok() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::Unit));
    }

    #[test]
    fn test_drop_unrestricted_rejected() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Lit(
            Literal::I32(42),
        )))));
        assert!(matches!(tc.check(&expr), Err(TypeError::UnnecessaryDrop)));
    }

    // ===== Module-level type checking =====

    #[test]
    fn test_module_basic() {
        let module = Module {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "add".into(),
                params: vec![
                    ("a".into(), Ty::Base(BaseTy::I32)),
                    ("b".into(), Ty::Base(BaseTy::I32)),
                ],
                ret_ty: Ty::Base(BaseTy::I32),
                body: dummy_expr(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(dummy_expr(ExprKind::Var("a".into()))),
                    right: Box::new(dummy_expr(ExprKind::Var("b".into()))),
                }),
            }],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_module_return_type_mismatch() {
        let module = Module {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "bad".into(),
                params: vec![],
                ret_ty: Ty::Base(BaseTy::Bool),
                body: dummy_expr(ExprKind::Lit(Literal::I32(42))),
            }],
        };
        assert!(matches!(
            type_check_module(&module),
            Err(TypeError::TypeMismatch { .. })
        ));
    }

    // ===== DYADIC DESIGN: let (affine) vs let! (linear) Tests =====
    //
    // The dyadic property is PER-BINDING, not a global mode.
    // `let!` always means exactly-once. `let` means at-most-once.
    // There is no flag to weaken this.

    #[test]
    fn test_let_bang_rejects_unconsumed() {
        // let! binding NOT consumed — must be rejected (linear discipline)
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::LetLin {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            // s is NOT consumed in body
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        // Must FAIL — let! demands exactly-once consumption
        assert!(
            matches!(
                tc.check(&expr),
                Err(TypeError::LinearVariableNotConsumed(_))
            ),
            "let! unconsumed must be rejected"
        );
    }

    #[test]
    fn test_let_allows_unconsumed_linear() {
        // let binding of linear type NOT consumed — must be ACCEPTED (affine)
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::Let {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            // s is NOT consumed — affine discipline allows this
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        // Must PASS — let is affine, implicit drop is allowed
        assert!(
            tc.check(&expr).is_ok(),
            "let (affine) should allow unconsumed linear values"
        );
    }

    #[test]
    fn test_let_bang_rejects_unconsumed_unrestricted() {
        // let! binding of I32 (unrestricted type) NOT consumed — still rejected
        // let! opts into linear discipline regardless of type
        let mut tc = TypeChecker::new();

        let expr = dummy_expr(ExprKind::LetLin {
            name: "x".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            matches!(
                tc.check(&expr),
                Err(TypeError::LinearVariableNotConsumed(_))
            ),
            "let! of unrestricted type must still reject unconsumed"
        );
    }

    #[test]
    fn test_linear_rejects_double_use() {
        // Linear variable used twice — must be rejected
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        // First use - OK
        let var1 = dummy_expr(ExprKind::Var("s".into()));
        assert!(tc.check(&var1).is_ok());

        // Second use - Error
        let var2 = dummy_expr(ExprKind::Var("s".into()));
        assert!(
            matches!(tc.check(&var2), Err(TypeError::LinearVariableReused(_))),
            "Double use of linear variable must be rejected"
        );
    }

    #[test]
    fn test_module_rejects_unconsumed_linear_param() {
        // Function with linear param that isn't consumed — must be rejected
        let module = Module {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "forget".into(),
                params: vec![("s".into(), Ty::String("r".into()))],
                ret_ty: Ty::Base(BaseTy::Unit),
                body: dummy_expr(ExprKind::Lit(Literal::Unit)), // s not consumed
            }],
        };

        assert!(
            type_check_module(&module).is_err(),
            "Unconsumed linear param must be rejected"
        );
    }

    #[test]
    fn test_if_branches_must_agree_on_linear_consumption() {
        // Branches disagree on consuming a linear variable — must be rejected
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            // then consumes, else doesn't - DISAGREEMENT
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            matches!(
                tc.check(&expr),
                Err(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Branch disagreement on linear consumption must be rejected"
        );
    }

    // ===== Binop/unaryop tests =====

    #[test]
    fn test_arithmetic_typing() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_comparison_returns_bool() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::BinOp {
            op: BinOp::Lt,
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::Bool));
    }

    #[test]
    fn test_negation_typing() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
        });
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }
}
