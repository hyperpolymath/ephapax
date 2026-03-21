// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Type Checker (Dyadic: Affine + Linear modes)
//!
//! Implements typing rules for BOTH affine and linear modes:
//! - **Affine mode**: Values used ≤1 time (can be dropped implicitly)
//! - **Linear mode**: Values used exactly 1 time (must be consumed)
//!
//! Based on formal/Typing.v

use ephapax_syntax::{BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, RegionName, Ty, UnaryOp, Var};
use std::collections::HashMap;
use thiserror::Error;

/// Type checking mode (dyadic design)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Affine mode: values used ≤1 time (permissive, allows implicit drops)
    Affine,
    /// Linear mode: values used exactly 1 time (strict, no implicit drops)
    Linear,
}

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

    #[error("String escapes its region `{0}`")]
    RegionEscape(RegionName),

    #[error("String literal must be allocated with String.new@region(\"...\")")]
    UnallocatedStringLiteral,

    #[error("Type annotation mismatch: declared {declared:?}, but value has type {actual:?}")]
    AnnotationMismatch { declared: Ty, actual: Ty },
}

/// Typing context entry
#[derive(Debug, Clone)]
struct CtxEntry {
    ty: Ty,
    used: bool,
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

    /// Extend context with new binding
    pub fn extend(&mut self, name: Var, ty: Ty) {
        self.vars.insert(name, CtxEntry { ty, used: false });
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

    /// Check all linear variables have been used (mode-aware)
    /// - In Linear mode: MUST consume all linear variables
    /// - In Affine mode: CAN leave linear variables unconsumed (implicit drop)
    pub fn check_all_linear_used(&self, mode: Mode) -> Result<(), TypeError> {
        // In affine mode, unconsumed variables are allowed (implicit drop)
        if mode == Mode::Affine {
            return Ok(());
        }

        // In linear mode, all linear variables MUST be consumed
        for (name, entry) in &self.vars {
            if entry.ty.is_linear() && !entry.used {
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
        // Check all variables in self
        for (name, entry) in &self.vars {
            if !entry.ty.is_linear() {
                continue; // Only check linear variables
            }

            match other.vars.get(name) {
                Some(other_entry) => {
                    if entry.used != other_entry.used {
                        return Err(TypeError::BranchLinearityMismatchDetailed {
                            var: name.clone(),
                            then_status: if entry.used { "consumed" } else { "not consumed" },
                            else_status: if other_entry.used { "consumed" } else { "not consumed" },
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
    mode: Mode,
}

impl TypeChecker {
    /// Create a new type checker in the specified mode
    pub fn new_with_mode(mode: Mode) -> Self {
        Self {
            ctx: Context::new(),
            mode,
        }
    }

    /// Create a new type checker in linear mode (strict, default)
    pub fn new() -> Self {
        Self::new_with_mode(Mode::Linear)
    }

    /// Get the current checking mode
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Set the checking mode
    pub fn set_mode(&mut self, mode: Mode) {
        self.mode = mode;
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

        // Mark linear variables as used
        if ty.is_linear() {
            self.ctx.mark_used(name)?;
        }

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

        self.ctx.extend(name.clone(), value_ty.clone());
        let body_ty = self.check(body)?;

        // In Linear mode: linear variable MUST be consumed
        // In Affine mode: linear variable CAN be unconsumed (implicit drop OK)
        if self.mode == Mode::Linear {
            if let Some(entry) = self.ctx.vars.get(name) {
                if entry.ty.is_linear() && !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(name.clone()));
                }
            }
        }

        Ok(body_ty)
    }

    fn check_lambda(&mut self, param: &Var, param_ty: &Ty, body: &Expr) -> Result<Ty, TypeError> {
        self.ctx.extend(param.clone(), param_ty.clone());
        let body_ty = self.check(body)?;

        // Check linear param was consumed (mode-aware)
        if self.mode == Mode::Linear {
            if let Some(entry) = self.ctx.vars.get(param) {
                if entry.ty.is_linear() && !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(param.clone()));
                }
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

    fn check_region(&mut self, name: &RegionName, body: &Expr) -> Result<Ty, TypeError> {
        self.ctx.enter_region(name.clone());
        let body_ty = self.check(body)?;
        self.ctx.exit_region();

        // Check no strings from this region escape
        if let Ty::String(r) = &body_ty {
            if r == name {
                return Err(TypeError::RegionEscape(name.clone()));
            }
        }

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

        self.ctx.extend(name.clone(), value_ty.clone());
        let body_ty = self.check(body)?;

        // Ensure linear variable was consumed (mode-aware)
        if self.mode == Mode::Linear {
            if let Some(entry) = self.ctx.vars.get(name) {
                if entry.ty.is_linear() && !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(name.clone()));
                }
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

                // Check left branch
                self.ctx.extend(left_var.clone(), *left.clone());
                let left_result_ty = self.check(left_body)?;

                // Check linear branch variable was consumed (mode-aware)
                if self.mode == Mode::Linear {
                    if let Some(entry) = self.ctx.vars.get(left_var) {
                        if entry.ty.is_linear() && !entry.used {
                            return Err(TypeError::LinearVariableNotConsumed(left_var.clone()));
                        }
                    }
                }

                // Remove branch-specific variable before comparison
                let mut ctx_after_left = self.ctx.snapshot();
                ctx_after_left.vars.remove(left_var);

                // Restore context for right branch
                self.ctx = ctx_after_scrutinee;

                // Check right branch
                self.ctx.extend(right_var.clone(), *right.clone());
                let right_result_ty = self.check(right_body)?;

                // Check linear branch variable was consumed (mode-aware)
                if self.mode == Mode::Linear {
                    if let Some(entry) = self.ctx.vars.get(right_var) {
                        if entry.ty.is_linear() && !entry.used {
                            return Err(TypeError::LinearVariableNotConsumed(right_var.clone()));
                        }
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
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                match &left_ty {
                    Ty::Base(BaseTy::I32)
                    | Ty::Base(BaseTy::I64)
                    | Ty::Base(BaseTy::F32)
                    | Ty::Base(BaseTy::F64) => Ok(left_ty),
                    _ => Err(TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::I32),
                        found: left_ty,
                    }),
                }
            }
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
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// Type check an entire module (mode-aware)
pub fn type_check_module_with_mode(module: &Module, mode: Mode) -> Result<(), TypeError> {
    let mut tc = TypeChecker::new_with_mode(mode);

    // First pass: collect all function signatures
    for decl in &module.decls {
        if let Decl::Fn { name, params, ret_ty, .. } = decl {
            // Build function type from params and return type
            let fn_ty = params.iter().rev().fold(ret_ty.clone(), |acc, (_, param_ty)| {
                Ty::Fun {
                    param: Box::new(param_ty.clone()),
                    ret: Box::new(acc),
                }
            });
            tc.ctx.extend(name.clone(), fn_ty);
        }
    }

    // Second pass: type check each function body
    for decl in &module.decls {
        match decl {
            Decl::Fn { name: _, params, ret_ty, body } => {
                // Create a fresh context for function body with params
                let saved_ctx = tc.ctx.clone();

                for (param_name, param_ty) in params {
                    tc.ctx.extend(param_name.clone(), param_ty.clone());
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

                // Check all linear params were consumed (mode-aware)
                if mode == Mode::Linear {
                    for (param_name, param_ty) in params {
                        if param_ty.is_linear() {
                            if let Some(entry) = tc.ctx.vars.get(param_name) {
                                if !entry.used {
                                    return Err(TypeError::LinearVariableNotConsumed(param_name.clone()));
                                }
                            }
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

/// Type check an entire module (defaults to Linear mode)
pub fn type_check_module(module: &Module) -> Result<(), TypeError> {
    type_check_module_with_mode(module, Mode::Linear)
}

/// Type check a single expression with specified mode
pub fn type_check_expr_with_mode(expr: &Expr, mode: Mode) -> Result<Ty, TypeError> {
    let mut tc = TypeChecker::new_with_mode(mode);
    tc.check(expr)
}

/// Type check a single expression (defaults to Linear mode)
pub fn type_check_expr(expr: &Expr) -> Result<Ty, TypeError> {
    type_check_expr_with_mode(expr, Mode::Linear)
}

/// Type check a single expression (alias for type_check_expr)
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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        // &s - borrow s
        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(
            ExprKind::Var("s".into()),
        ))));
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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        // First borrow
        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(
            ExprKind::Var("s".into()),
        ))));
        assert!(tc.check(&borrow_expr).is_ok());

        // Then consume
        let drop_expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
            ExprKind::Var("s".into()),
        ))));
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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

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
            Err(TypeError::RegionEscape(_))
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
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::InactiveRegion(_))
        ));
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
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        let expr = dummy_expr(ExprKind::Copy(Box::new(dummy_expr(
            ExprKind::Var("s".into()),
        ))));
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::CannotCopyLinear(_))
        ));
    }

    #[test]
    fn test_drop_linear_ok() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
            ExprKind::Var("s".into()),
        ))));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::Unit));
    }

    #[test]
    fn test_drop_unrestricted_rejected() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Lit(
            Literal::I32(42),
        )))));
        assert!(matches!(
            tc.check(&expr),
            Err(TypeError::UnnecessaryDrop)
        ));
    }

    // ===== Module-level type checking =====

    #[test]
    fn test_module_basic() {
        let module = Module {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "add".into(),
                params: vec![("a".into(), Ty::Base(BaseTy::I32)), ("b".into(), Ty::Base(BaseTy::I32))],
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

    // ===== DYADIC DESIGN: Affine vs. Linear Mode Tests =====

    #[test]
    fn test_affine_mode_allows_unconsumed_linear() {
        // In AFFINE mode: unconsumed linear variables are OK (implicit drop)
        let mut tc = TypeChecker::new_with_mode(Mode::Affine);
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::Let {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            // s is NOT consumed in body - just return unit
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        // In affine mode, this should PASS (implicit drop allowed)
        assert!(tc.check(&expr).is_ok(), "Affine mode should allow unconsumed linear variables");
    }

    #[test]
    fn test_linear_mode_rejects_unconsumed_linear() {
        // In LINEAR mode: unconsumed linear variables are ERROR
        let mut tc = TypeChecker::new_with_mode(Mode::Linear);
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::Let {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            // s is NOT consumed in body - just return unit
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        // In linear mode, this should FAIL (must consume s)
        assert!(
            matches!(tc.check(&expr), Err(TypeError::LinearVariableNotConsumed(_))),
            "Linear mode should reject unconsumed linear variables"
        );
    }

    #[test]
    fn test_affine_mode_still_rejects_double_use() {
        // AFFINE mode: can drop, but still can't use twice
        let mut tc = TypeChecker::new_with_mode(Mode::Affine);
        tc.ctx.enter_region("r".into());
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        // First use - OK
        let var1 = dummy_expr(ExprKind::Var("s".into()));
        assert!(tc.check(&var1).is_ok());

        // Second use - Error (even in affine mode!)
        let var2 = dummy_expr(ExprKind::Var("s".into()));
        assert!(
            matches!(tc.check(&var2), Err(TypeError::LinearVariableReused(_))),
            "Affine mode should still reject double use"
        );
    }

    #[test]
    fn test_mode_switching() {
        // Test that we can switch modes
        let mut tc = TypeChecker::new_with_mode(Mode::Linear);
        assert_eq!(tc.mode(), Mode::Linear);

        tc.set_mode(Mode::Affine);
        assert_eq!(tc.mode(), Mode::Affine);
    }

    #[test]
    fn test_module_affine_mode() {
        // Module with function that doesn't consume linear param
        let module = Module {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "forget".into(),
                params: vec![("s".into(), Ty::String("r".into()))],
                ret_ty: Ty::Base(BaseTy::Unit),
                body: dummy_expr(ExprKind::Lit(Literal::Unit)),  // s not consumed
            }],
        };

        // Should FAIL in linear mode
        assert!(
            type_check_module_with_mode(&module, Mode::Linear).is_err(),
            "Linear mode should reject unconsumed param"
        );

        // Should PASS in affine mode
        assert!(
            type_check_module_with_mode(&module, Mode::Affine).is_ok(),
            "Affine mode should allow unconsumed param"
        );
    }

    #[test]
    fn test_affine_mode_if_branch_can_not_consume() {
        // In affine mode, branches don't HAVE to consume linear vars
        let mut tc = TypeChecker::new_with_mode(Mode::Affine);
        tc.ctx.enter_region("r".into());
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            // Neither branch consumes s
            then_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });

        // In affine mode, this should PASS
        assert!(tc.check(&expr).is_ok(), "Affine mode allows unconsumed vars in branches");
    }

    #[test]
    fn test_linear_mode_if_branch_must_agree() {
        // In linear mode, both branches must agree on consumption
        let mut tc = TypeChecker::new_with_mode(Mode::Linear);
        tc.ctx.enter_region("r".into());
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            // then consumes, else doesn't - DISAGREEMENT
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        // In linear mode, this should FAIL (branch disagreement)
        assert!(
            matches!(tc.check(&expr), Err(TypeError::BranchLinearityMismatchDetailed { .. })),
            "Linear mode requires branch agreement"
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
