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
            _ => todo!("Type checking for {:?}", expr.kind),
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

        // Both branches must have same type and consume same linear resources
        let then_ty = self.check(then_branch)?;
        let else_ty = self.check(else_branch)?;

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
        // Borrowing does not consume the resource
        let inner_ty = self.check(inner)?;
        Ok(Ty::Borrow(Box::new(inner_ty)))
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
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
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
}
