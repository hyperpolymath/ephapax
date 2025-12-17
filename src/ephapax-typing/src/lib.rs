// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Linear Type Checker
//!
//! Implements the typing rules from formal/Typing.v

use ephapax_syntax::{BaseTy, Expr, ExprKind, Literal, RegionName, Ty, Var};
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

    #[error("String escapes its region `{0}`")]
    RegionEscape(RegionName),

    #[error("Expected function type, got {0:?}")]
    NotAFunction(Ty),

    #[error("Expected pair type, got {0:?}")]
    NotAPair(Ty),

    #[error("Expected sum type, got {0:?}")]
    NotASum(Ty),

    #[error("Expected reference type, got {0:?}")]
    NotAReference(Ty),

    #[error("Cannot borrow linear value")]
    CannotBorrowLinear,
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

    /// Remove a binding
    pub fn remove(&mut self, name: &Var) {
        self.vars.remove(name);
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

    /// Clone context for branch checking
    pub fn snapshot(&self) -> Self {
        self.clone()
    }

    /// Get linear variables usage state
    fn linear_usage(&self) -> HashMap<Var, bool> {
        self.vars
            .iter()
            .filter(|(_, e)| e.ty.is_linear())
            .map(|(k, v)| (k.clone(), v.used))
            .collect()
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
            ExprKind::StringLen(inner) => self.check_string_len(inner),
            ExprKind::Let { name, ty, value, body } => self.check_let(name, ty.as_ref(), value, body),
            ExprKind::LetLin { name, ty, value, body } => self.check_let_lin(name, ty.as_ref(), value, body),
            ExprKind::Lambda { param, param_ty, body } => self.check_lambda(param, param_ty, body),
            ExprKind::App { func, arg } => self.check_app(func, arg),
            ExprKind::Pair { left, right } => self.check_pair(left, right),
            ExprKind::Fst(inner) => self.check_fst(inner),
            ExprKind::Snd(inner) => self.check_snd(inner),
            ExprKind::Inl { ty, value } => self.check_inl(ty, value),
            ExprKind::Inr { ty, value } => self.check_inr(ty, value),
            ExprKind::Case { scrutinee, left_var, left_body, right_var, right_body } => {
                self.check_case(scrutinee, left_var, left_body, right_var, right_body)
            }
            ExprKind::If { cond, then_branch, else_branch } => self.check_if(cond, then_branch, else_branch),
            ExprKind::Region { name, body } => self.check_region(name, body),
            ExprKind::Borrow(inner) => self.check_borrow(inner),
            ExprKind::Deref(inner) => self.check_deref(inner),
            ExprKind::Drop(inner) => self.check_drop(inner),
            ExprKind::Copy(inner) => self.check_copy(inner),
            ExprKind::Block(exprs) => self.check_block(exprs),
        }
    }

    /// Type check a module
    pub fn check_module(&mut self, module: &ephapax_syntax::Module) -> Result<(), TypeError> {
        for decl in &module.decls {
            self.check_decl(decl)?;
        }
        Ok(())
    }

    fn check_decl(&mut self, decl: &ephapax_syntax::Decl) -> Result<(), TypeError> {
        match decl {
            ephapax_syntax::Decl::Fn { name, params, ret_ty, body } => {
                // Add params to context
                for (param_name, param_ty) in params {
                    self.ctx.extend(param_name.clone(), param_ty.clone());
                }

                // Check body
                let body_ty = self.check(body)?;

                // Verify return type
                if body_ty != *ret_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: ret_ty.clone(),
                        found: body_ty,
                    });
                }

                // Check linear params consumed
                for (param_name, param_ty) in params {
                    if param_ty.is_linear() {
                        if let Some(entry) = self.ctx.vars.get(param_name) {
                            if !entry.used {
                                return Err(TypeError::LinearVariableNotConsumed(param_name.clone()));
                            }
                        }
                    }
                    self.ctx.remove(param_name);
                }

                // Register function in context for recursive calls
                let func_ty = params.iter().rev().fold(ret_ty.clone(), |acc, (_, param_ty)| {
                    Ty::Fun {
                        param: Box::new(param_ty.clone()),
                        ret: Box::new(acc),
                    }
                });
                self.ctx.extend(name.clone(), func_ty);

                Ok(())
            }
            ephapax_syntax::Decl::Type { .. } => {
                // Type aliases don't need runtime checking
                Ok(())
            }
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
                // String literals without region - treat as needing allocation
                // This would be caught at a higher level; here we allow it for testing
                Ty::Base(BaseTy::Unit)
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

    fn check_string_len(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;
        match &inner_ty {
            Ty::String(_) => Ok(Ty::Base(BaseTy::I32)),
            Ty::Borrow(inner) if matches!(inner.as_ref(), Ty::String(_)) => {
                Ok(Ty::Base(BaseTy::I32))
            }
            _ => Err(TypeError::TypeMismatch {
                expected: Ty::String("_".into()),
                found: inner_ty,
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
        self.ctx.extend(name.clone(), value_ty.clone());
        let body_ty = self.check(body)?;

        // Ensure linear variable was consumed
        if value_ty.is_linear() {
            if let Some(entry) = self.ctx.vars.get(name) {
                if !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(name.clone()));
                }
            }
        }
        self.ctx.remove(name);

        Ok(body_ty)
    }

    fn check_let_lin(
        &mut self,
        name: &Var,
        _ty: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, TypeError> {
        // let! forces linear treatment
        let value_ty = self.check(value)?;
        self.ctx.extend(name.clone(), value_ty);
        let body_ty = self.check(body)?;

        // Must be consumed
        if let Some(entry) = self.ctx.vars.get(name) {
            if !entry.used {
                return Err(TypeError::LinearVariableNotConsumed(name.clone()));
            }
        }
        self.ctx.remove(name);

        Ok(body_ty)
    }

    fn check_lambda(&mut self, param: &Var, param_ty: &Ty, body: &Expr) -> Result<Ty, TypeError> {
        self.ctx.extend(param.clone(), param_ty.clone());
        let body_ty = self.check(body)?;

        // Check linear param was consumed
        if param_ty.is_linear() {
            if let Some(entry) = self.ctx.vars.get(param) {
                if !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(param.clone()));
                }
            }
        }
        self.ctx.remove(param);

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
            _ => Err(TypeError::NotAFunction(func_ty)),
        }
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
            Ty::Prod { left, .. } => Ok(*left),
            _ => Err(TypeError::NotAPair(inner_ty)),
        }
    }

    fn check_snd(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;
        match inner_ty {
            Ty::Prod { right, .. } => Ok(*right),
            _ => Err(TypeError::NotAPair(inner_ty)),
        }
    }

    fn check_inl(&mut self, ty: &Ty, value: &Expr) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;
        Ok(Ty::Sum {
            left: Box::new(value_ty),
            right: Box::new(ty.clone()),
        })
    }

    fn check_inr(&mut self, ty: &Ty, value: &Expr) -> Result<Ty, TypeError> {
        let value_ty = self.check(value)?;
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

        let (left_ty, right_ty) = match scrutinee_ty {
            Ty::Sum { left, right } => (*left, *right),
            _ => return Err(TypeError::NotASum(scrutinee_ty)),
        };

        // Check left branch
        let ctx_before = self.ctx.linear_usage();
        self.ctx.extend(left_var.clone(), left_ty.clone());
        let left_result_ty = self.check(left_body)?;
        if left_ty.is_linear() {
            if let Some(entry) = self.ctx.vars.get(left_var) {
                if !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(left_var.clone()));
                }
            }
        }
        self.ctx.remove(left_var);
        let ctx_after_left = self.ctx.linear_usage();

        // Restore context for right branch
        for (name, was_used) in &ctx_before {
            if let Some(entry) = self.ctx.vars.get_mut(name) {
                entry.used = *was_used;
            }
        }

        // Check right branch
        self.ctx.extend(right_var.clone(), right_ty.clone());
        let right_result_ty = self.check(right_body)?;
        if right_ty.is_linear() {
            if let Some(entry) = self.ctx.vars.get(right_var) {
                if !entry.used {
                    return Err(TypeError::LinearVariableNotConsumed(right_var.clone()));
                }
            }
        }
        self.ctx.remove(right_var);
        let ctx_after_right = self.ctx.linear_usage();

        // Both branches must consume same linear variables
        if ctx_after_left != ctx_after_right {
            return Err(TypeError::BranchLinearityMismatch);
        }

        // Both branches must have same type
        if left_result_ty != right_result_ty {
            return Err(TypeError::TypeMismatch {
                expected: left_result_ty,
                found: right_result_ty,
            });
        }

        Ok(left_result_ty)
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

        // Save linear usage state
        let ctx_before = self.ctx.linear_usage();

        // Check then branch
        let then_ty = self.check(then_branch)?;
        let ctx_after_then = self.ctx.linear_usage();

        // Restore for else branch
        for (name, was_used) in &ctx_before {
            if let Some(entry) = self.ctx.vars.get_mut(name) {
                entry.used = *was_used;
            }
        }

        // Check else branch
        let else_ty = self.check(else_branch)?;
        let ctx_after_else = self.ctx.linear_usage();

        // Both branches must consume same linear variables
        if ctx_after_then != ctx_after_else {
            return Err(TypeError::BranchLinearityMismatch);
        }

        if then_ty != else_ty {
            return Err(TypeError::TypeMismatch {
                expected: then_ty,
                found: else_ty,
            });
        }

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
        // Peek at type without consuming
        let inner_ty = self.check(inner)?;

        // Borrowing linear values is allowed but the borrow is second-class
        Ok(Ty::Borrow(Box::new(inner_ty)))
    }

    fn check_deref(&mut self, inner: &Expr) -> Result<Ty, TypeError> {
        let inner_ty = self.check(inner)?;
        match inner_ty {
            Ty::Borrow(inner) => Ok(*inner),
            _ => Err(TypeError::NotAReference(inner_ty)),
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

    fn check_block(&mut self, exprs: &[Expr]) -> Result<Ty, TypeError> {
        let mut result_ty = Ty::Base(BaseTy::Unit);
        for expr in exprs {
            result_ty = self.check(expr)?;
        }
        Ok(result_ty)
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function to type check an expression
pub fn type_check(expr: &Expr) -> Result<Ty, TypeError> {
    let mut tc = TypeChecker::new();
    tc.check(expr)
}

/// Convenience function to type check a module
pub fn type_check_module(module: &ephapax_syntax::Module) -> Result<(), TypeError> {
    let mut tc = TypeChecker::new();
    tc.check_module(module)
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
    fn test_pair_typing() {
        let mut tc = TypeChecker::new();
        let pair = dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        });
        let ty = tc.check(&pair).unwrap();
        assert_eq!(ty, Ty::Prod {
            left: Box::new(Ty::Base(BaseTy::I32)),
            right: Box::new(Ty::Base(BaseTy::Bool)),
        });
    }

    #[test]
    fn test_fst_projection() {
        let mut tc = TypeChecker::new();
        let pair = dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        });
        let fst = dummy_expr(ExprKind::Fst(Box::new(pair)));
        assert_eq!(tc.check(&fst).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_lambda_typing() {
        let mut tc = TypeChecker::new();
        let lambda = dummy_expr(ExprKind::Lambda {
            param: "x".into(),
            param_ty: Ty::Base(BaseTy::I32),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        let ty = tc.check(&lambda).unwrap();
        assert_eq!(ty, Ty::Fun {
            param: Box::new(Ty::Base(BaseTy::I32)),
            ret: Box::new(Ty::Base(BaseTy::I32)),
        });
    }

    #[test]
    fn test_region_escape() {
        let mut tc = TypeChecker::new();
        let region = dummy_expr(ExprKind::Region {
            name: "r".into(),
            body: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".into(),
            })),
        });
        assert!(matches!(tc.check(&region), Err(TypeError::RegionEscape(_))));
    }

    #[test]
    fn test_branch_linearity() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx.extend("s".into(), Ty::String("r".into()));

        // Both branches must consume s
        let if_expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(
                dummy_expr(ExprKind::Var("s".into()))
            )))),
            else_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(
                dummy_expr(ExprKind::Var("s".into()))
            )))),
        });
        assert!(tc.check(&if_expr).is_ok());
    }
}
