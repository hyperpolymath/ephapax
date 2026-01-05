// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Linear Type Checker
//!
//! Implements the typing rules from formal/Typing.v

use ephapax_syntax::{BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, RegionName, Ty, UnaryOp, Var};
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

    #[error("String escapes its region `{0}`")]
    RegionEscape(RegionName),
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

    /// Check all linear variables have been used
    pub fn check_all_linear_used(&self) -> Result<(), TypeError> {
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
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { ctx: Context::new() }
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
                // String literals need a region - this is a parse error
                panic!("String literals must be allocated with String.new@r")
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
        _ty: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;
        self.ctx.extend(name.clone(), value_ty);
        let body_ty = self.check(body)?;

        // Ensure linear variable was consumed
        if let Some(entry) = self.ctx.vars.get(name) {
            if entry.ty.is_linear() && !entry.used {
                return Err(TypeError::LinearVariableNotConsumed(name.clone()));
            }
        }

        Ok(body_ty)
    }

    fn check_lambda(&mut self, param: &Var, param_ty: &Ty, body: &Expr) -> Result<Ty, TypeError> {
        self.ctx.extend(param.clone(), param_ty.clone());
        let body_ty = self.check(body)?;

        // Check linear param was consumed
        if let Some(entry) = self.ctx.vars.get(param) {
            if entry.ty.is_linear() && !entry.used {
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
        _ty: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, TypeError> {
        // Same as let, but explicitly marked linear
        let value_ty = self.check(value)?;
        self.ctx.extend(name.clone(), value_ty);
        let body_ty = self.check(body)?;

        // Ensure linear variable was consumed
        if let Some(entry) = self.ctx.vars.get(name) {
            if entry.ty.is_linear() && !entry.used {
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

                // Check left branch
                self.ctx.extend(left_var.clone(), *left.clone());
                let left_result_ty = self.check(left_body)?;

                // Check linear branch variable was consumed
                if let Some(entry) = self.ctx.vars.get(left_var) {
                    if entry.ty.is_linear() && !entry.used {
                        return Err(TypeError::LinearVariableNotConsumed(left_var.clone()));
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

                // Check linear branch variable was consumed
                if let Some(entry) = self.ctx.vars.get(right_var) {
                    if entry.ty.is_linear() && !entry.used {
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
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// Type check an entire module
pub fn type_check_module(module: &Module) -> Result<(), TypeError> {
    let mut tc = TypeChecker::new();

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
            Decl::Fn { name, params, ret_ty, body } => {
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

                // Check all linear params were consumed
                for (param_name, param_ty) in params {
                    if param_ty.is_linear() {
                        if let Some(entry) = tc.ctx.vars.get(param_name) {
                            if !entry.used {
                                return Err(TypeError::LinearVariableNotConsumed(param_name.clone()));
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

/// Type check a single expression (convenience function)
pub fn type_check_expr(expr: &Expr) -> Result<Ty, TypeError> {
    let mut tc = TypeChecker::new();
    tc.check(expr)
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
}
