// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Tree-Walking Interpreter
//!
//! A simple interpreter for debugging and rapid development.
//! Useful for testing before compiling to WASM.

use ephapax_syntax::{BaseTy, Decl, Expr, ExprKind, Literal, Module, RegionName, Ty, Var};
use smol_str::SmolStr;
use std::collections::HashMap;
use thiserror::Error;

/// Runtime errors during interpretation
#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    #[error("Unbound variable: {0}")]
    UnboundVariable(Var),

    #[error("Type error: expected {expected}, got {found}")]
    TypeError { expected: String, found: String },

    #[error("Division by zero")]
    DivisionByZero,

    #[error("Region `{0}` not active")]
    InactiveRegion(RegionName),

    #[error("String `{0}` escaped its region")]
    StringEscaped(String),

    #[error("Linear value used after consumption")]
    LinearValueConsumed,

    #[error("Pattern match failed")]
    PatternMatchFailed,

    #[error("Not a function")]
    NotAFunction,

    #[error("Not a pair")]
    NotAPair,

    #[error("Not a sum type")]
    NotASum,
}

/// Runtime values
#[derive(Debug, Clone)]
pub enum Value {
    Unit,
    Bool(bool),
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    String { data: String, region: RegionName },
    Pair(Box<Value>, Box<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
    Closure {
        param: Var,
        param_ty: Ty,
        body: Expr,
        env: Environment,
    },
    Borrow(Box<Value>),
}

impl Value {
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Unit => "Unit",
            Value::Bool(_) => "Bool",
            Value::I32(_) => "I32",
            Value::I64(_) => "I64",
            Value::F32(_) => "F32",
            Value::F64(_) => "F64",
            Value::String { .. } => "String",
            Value::Pair(_, _) => "Pair",
            Value::Left(_) => "Left",
            Value::Right(_) => "Right",
            Value::Closure { .. } => "Function",
            Value::Borrow(_) => "Borrow",
        }
    }

    /// Get the inferred type of this value
    pub fn to_type(&self) -> Ty {
        match self {
            Value::Unit => Ty::Base(BaseTy::Unit),
            Value::Bool(_) => Ty::Base(BaseTy::Bool),
            Value::I32(_) => Ty::Base(BaseTy::I32),
            Value::I64(_) => Ty::Base(BaseTy::I64),
            Value::F32(_) => Ty::Base(BaseTy::F32),
            Value::F64(_) => Ty::Base(BaseTy::F64),
            Value::String { region, .. } => Ty::String(region.clone()),
            Value::Pair(l, r) => Ty::Prod {
                left: Box::new(l.to_type()),
                right: Box::new(r.to_type()),
            },
            Value::Left(v) => Ty::Sum {
                left: Box::new(v.to_type()),
                right: Box::new(Ty::Base(BaseTy::Unit)),
            },
            Value::Right(v) => Ty::Sum {
                left: Box::new(Ty::Base(BaseTy::Unit)),
                right: Box::new(v.to_type()),
            },
            Value::Closure { param_ty, .. } => Ty::Fun {
                param: Box::new(param_ty.clone()),
                ret: Box::new(Ty::Base(BaseTy::Unit)), // Unknown without evaluation
            },
            Value::Borrow(inner) => Ty::Borrow(Box::new(inner.to_type())),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::I32(n) => write!(f, "{}", n),
            Value::I64(n) => write!(f, "{}i64", n),
            Value::F32(n) => write!(f, "{}f32", n),
            Value::F64(n) => write!(f, "{}", n),
            Value::String { data, region } => write!(f, "\"{}\"@{}", data, region),
            Value::Pair(l, r) => write!(f, "({}, {})", l, r),
            Value::Left(v) => write!(f, "inl({})", v),
            Value::Right(v) => write!(f, "inr({})", v),
            Value::Closure { param, .. } => write!(f, "<fn({})>", param),
            Value::Borrow(v) => write!(f, "&{}", v),
        }
    }
}

/// Environment for variable bindings
#[derive(Debug, Clone, Default)]
pub struct Environment {
    bindings: HashMap<Var, Value>,
    /// Track which linear values have been consumed
    consumed: HashMap<Var, bool>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extend(&mut self, name: Var, value: Value) {
        self.bindings.insert(name.clone(), value);
        self.consumed.insert(name, false);
    }

    pub fn get(&self, name: &Var) -> Option<&Value> {
        self.bindings.get(name)
    }

    pub fn get_mut(&mut self, name: &Var) -> Option<&mut Value> {
        self.bindings.get_mut(name)
    }

    pub fn remove(&mut self, name: &Var) {
        self.bindings.remove(name);
        self.consumed.remove(name);
    }

    pub fn mark_consumed(&mut self, name: &Var) {
        if let Some(consumed) = self.consumed.get_mut(name) {
            *consumed = true;
        }
    }

    pub fn is_consumed(&self, name: &Var) -> bool {
        self.consumed.get(name).copied().unwrap_or(false)
    }
}

/// Interpreter state
pub struct Interpreter {
    env: Environment,
    /// Active regions stack
    regions: Vec<RegionName>,
    /// Function definitions
    functions: HashMap<Var, (Vec<(Var, Ty)>, Ty, Expr)>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Environment::new(),
            regions: Vec::new(),
            functions: HashMap::new(),
        }
    }

    /// Load a module (register all function definitions)
    pub fn load_module(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::Fn { name, params, ret_ty, body } = decl {
                self.functions.insert(
                    name.clone(),
                    (params.clone(), ret_ty.clone(), body.clone()),
                );
            }
        }
    }

    /// Evaluate an expression
    pub fn eval(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match &expr.kind {
            ExprKind::Lit(lit) => self.eval_lit(lit),
            ExprKind::Var(name) => self.eval_var(name),
            ExprKind::StringNew { region, value } => self.eval_string_new(region, value),
            ExprKind::StringConcat { left, right } => self.eval_string_concat(left, right),
            ExprKind::StringLen(inner) => self.eval_string_len(inner),
            ExprKind::Let { name, value, body, .. } => self.eval_let(name, value, body),
            ExprKind::LetLin { name, value, body, .. } => self.eval_let(name, value, body),
            ExprKind::Lambda { param, param_ty, body } => self.eval_lambda(param, param_ty, body),
            ExprKind::App { func, arg } => self.eval_app(func, arg),
            ExprKind::Pair { left, right } => self.eval_pair(left, right),
            ExprKind::Fst(inner) => self.eval_fst(inner),
            ExprKind::Snd(inner) => self.eval_snd(inner),
            ExprKind::Inl { value, .. } => self.eval_inl(value),
            ExprKind::Inr { value, .. } => self.eval_inr(value),
            ExprKind::Case { scrutinee, left_var, left_body, right_var, right_body } => {
                self.eval_case(scrutinee, left_var, left_body, right_var, right_body)
            }
            ExprKind::If { cond, then_branch, else_branch } => {
                self.eval_if(cond, then_branch, else_branch)
            }
            ExprKind::Region { name, body } => self.eval_region(name, body),
            ExprKind::Borrow(inner) => self.eval_borrow(inner),
            ExprKind::Deref(inner) => self.eval_deref(inner),
            ExprKind::Drop(inner) => self.eval_drop(inner),
            ExprKind::Copy(inner) => self.eval_copy(inner),
            ExprKind::Block(exprs) => self.eval_block(exprs),
        }
    }

    fn eval_lit(&self, lit: &Literal) -> Result<Value, RuntimeError> {
        Ok(match lit {
            Literal::Unit => Value::Unit,
            Literal::Bool(b) => Value::Bool(*b),
            Literal::I32(n) => Value::I32(*n),
            Literal::I64(n) => Value::I64(*n),
            Literal::F32(n) => Value::F32(*n),
            Literal::F64(n) => Value::F64(*n),
            Literal::String(s) => {
                // Unallocated string literal - use default region
                Value::String {
                    data: s.clone(),
                    region: "_".into(),
                }
            }
        })
    }

    fn eval_var(&mut self, name: &Var) -> Result<Value, RuntimeError> {
        // Check if it's a function
        if let Some((params, _ret_ty, body)) = self.functions.get(name).cloned() {
            if params.is_empty() {
                // Nullary function - evaluate body
                return self.eval(&body);
            } else {
                // Create closure for first parameter
                let (first_param, first_ty) = params[0].clone();
                return Ok(Value::Closure {
                    param: first_param,
                    param_ty: first_ty,
                    body: body.clone(),
                    env: self.env.clone(),
                });
            }
        }

        // Check if consumed (for linear values)
        if self.env.is_consumed(name) {
            return Err(RuntimeError::LinearValueConsumed);
        }

        let value = self
            .env
            .get(name)
            .ok_or_else(|| RuntimeError::UnboundVariable(name.clone()))?
            .clone();

        // Mark as consumed for linear types
        if matches!(value, Value::String { .. }) {
            self.env.mark_consumed(name);
        }

        Ok(value)
    }

    fn eval_string_new(&self, region: &RegionName, value: &str) -> Result<Value, RuntimeError> {
        if !self.regions.contains(region) && region != "_" {
            return Err(RuntimeError::InactiveRegion(region.clone()));
        }
        Ok(Value::String {
            data: value.to_string(),
            region: region.clone(),
        })
    }

    fn eval_string_concat(&mut self, left: &Expr, right: &Expr) -> Result<Value, RuntimeError> {
        let left_val = self.eval(left)?;
        let right_val = self.eval(right)?;

        match (left_val, right_val) {
            (
                Value::String { data: d1, region: r1 },
                Value::String { data: d2, region: r2 },
            ) => {
                if r1 != r2 {
                    return Err(RuntimeError::TypeError {
                        expected: format!("String@{}", r1),
                        found: format!("String@{}", r2),
                    });
                }
                Ok(Value::String {
                    data: d1 + &d2,
                    region: r1,
                })
            }
            (l, r) => Err(RuntimeError::TypeError {
                expected: "String".to_string(),
                found: format!("{}, {}", l.type_name(), r.type_name()),
            }),
        }
    }

    fn eval_string_len(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        match &val {
            Value::String { data, .. } => Ok(Value::I32(data.len() as i32)),
            Value::Borrow(inner) => match inner.as_ref() {
                Value::String { data, .. } => Ok(Value::I32(data.len() as i32)),
                _ => Err(RuntimeError::TypeError {
                    expected: "String".to_string(),
                    found: val.type_name().to_string(),
                }),
            },
            _ => Err(RuntimeError::TypeError {
                expected: "String".to_string(),
                found: val.type_name().to_string(),
            }),
        }
    }

    fn eval_let(&mut self, name: &Var, value: &Expr, body: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(value)?;
        self.env.extend(name.clone(), val);
        let result = self.eval(body)?;
        self.env.remove(name);
        Ok(result)
    }

    fn eval_lambda(&self, param: &Var, param_ty: &Ty, body: &Expr) -> Result<Value, RuntimeError> {
        Ok(Value::Closure {
            param: param.clone(),
            param_ty: param_ty.clone(),
            body: body.clone(),
            env: self.env.clone(),
        })
    }

    fn eval_app(&mut self, func: &Expr, arg: &Expr) -> Result<Value, RuntimeError> {
        let func_val = self.eval(func)?;
        let arg_val = self.eval(arg)?;

        match func_val {
            Value::Closure { param, body, env, .. } => {
                let mut new_env = env;
                new_env.extend(param, arg_val);
                let old_env = std::mem::replace(&mut self.env, new_env);
                let result = self.eval(&body)?;
                self.env = old_env;
                Ok(result)
            }
            _ => Err(RuntimeError::NotAFunction),
        }
    }

    fn eval_pair(&mut self, left: &Expr, right: &Expr) -> Result<Value, RuntimeError> {
        let left_val = self.eval(left)?;
        let right_val = self.eval(right)?;
        Ok(Value::Pair(Box::new(left_val), Box::new(right_val)))
    }

    fn eval_fst(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        match val {
            Value::Pair(left, _) => Ok(*left),
            _ => Err(RuntimeError::NotAPair),
        }
    }

    fn eval_snd(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        match val {
            Value::Pair(_, right) => Ok(*right),
            _ => Err(RuntimeError::NotAPair),
        }
    }

    fn eval_inl(&mut self, value: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(value)?;
        Ok(Value::Left(Box::new(val)))
    }

    fn eval_inr(&mut self, value: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(value)?;
        Ok(Value::Right(Box::new(val)))
    }

    fn eval_case(
        &mut self,
        scrutinee: &Expr,
        left_var: &Var,
        left_body: &Expr,
        right_var: &Var,
        right_body: &Expr,
    ) -> Result<Value, RuntimeError> {
        let scrutinee_val = self.eval(scrutinee)?;

        match scrutinee_val {
            Value::Left(inner) => {
                self.env.extend(left_var.clone(), *inner);
                let result = self.eval(left_body)?;
                self.env.remove(left_var);
                Ok(result)
            }
            Value::Right(inner) => {
                self.env.extend(right_var.clone(), *inner);
                let result = self.eval(right_body)?;
                self.env.remove(right_var);
                Ok(result)
            }
            _ => Err(RuntimeError::NotASum),
        }
    }

    fn eval_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Value, RuntimeError> {
        let cond_val = self.eval(cond)?;

        match cond_val {
            Value::Bool(true) => self.eval(then_branch),
            Value::Bool(false) => self.eval(else_branch),
            _ => Err(RuntimeError::TypeError {
                expected: "Bool".to_string(),
                found: cond_val.type_name().to_string(),
            }),
        }
    }

    fn eval_region(&mut self, name: &RegionName, body: &Expr) -> Result<Value, RuntimeError> {
        self.regions.push(name.clone());
        let result = self.eval(body)?;
        self.regions.pop();

        // Check for region escape
        if let Value::String { region, data } = &result {
            if region == name {
                return Err(RuntimeError::StringEscaped(data.clone()));
            }
        }

        Ok(result)
    }

    fn eval_borrow(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        Ok(Value::Borrow(Box::new(val)))
    }

    fn eval_deref(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        match val {
            Value::Borrow(inner) => Ok(*inner),
            _ => Err(RuntimeError::TypeError {
                expected: "Borrow".to_string(),
                found: val.type_name().to_string(),
            }),
        }
    }

    fn eval_drop(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        // Evaluate and discard
        let _ = self.eval(inner)?;
        Ok(Value::Unit)
    }

    fn eval_copy(&mut self, inner: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval(inner)?;
        // For unrestricted types, return a pair of copies
        Ok(Value::Pair(Box::new(val.clone()), Box::new(val)))
    }

    fn eval_block(&mut self, exprs: &[Expr]) -> Result<Value, RuntimeError> {
        let mut result = Value::Unit;
        for expr in exprs {
            result = self.eval(expr)?;
        }
        Ok(result)
    }

    /// Get a binding from the environment
    pub fn get_binding(&self, name: &str) -> Option<&Value> {
        let name: SmolStr = name.into();
        self.env.get(&name)
    }

    /// Call the main function (no arguments)
    pub fn call_main(&mut self) -> Result<Value, RuntimeError> {
        let name: SmolStr = "main".into();

        let (params, _ret_ty, body) = self
            .functions
            .get(&name)
            .ok_or_else(|| RuntimeError::UnboundVariable(name.clone()))?
            .clone();

        // Main should have no parameters
        if !params.is_empty() {
            return Err(RuntimeError::TypeError {
                expected: "main with no parameters".to_string(),
                found: format!("main with {} parameters", params.len()),
            });
        }

        self.eval(&body)
    }

    /// Call a named function with arguments
    pub fn call(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let name: SmolStr = name.into();

        let (params, _ret_ty, body) = self
            .functions
            .get(&name)
            .ok_or_else(|| RuntimeError::UnboundVariable(name.clone()))?
            .clone();

        if args.len() != params.len() {
            return Err(RuntimeError::TypeError {
                expected: format!("{} arguments", params.len()),
                found: format!("{} arguments", args.len()),
            });
        }

        // Bind parameters
        for ((param_name, _), arg) in params.iter().zip(args) {
            self.env.extend(param_name.clone(), arg);
        }

        // Evaluate body
        let result = self.eval(&body)?;

        // Remove parameters
        for (param_name, _) in &params {
            self.env.remove(param_name);
        }

        Ok(result)
    }
}

impl Default for Interpreter {
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
    fn test_eval_literal() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::Lit(Literal::I32(42)));
        let result = interp.eval(&expr).unwrap();
        assert!(matches!(result, Value::I32(42)));
    }

    #[test]
    fn test_eval_if() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });
        let result = interp.eval(&expr).unwrap();
        assert!(matches!(result, Value::I32(1)));
    }

    #[test]
    fn test_eval_let() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::Let {
            name: "x".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        let result = interp.eval(&expr).unwrap();
        assert!(matches!(result, Value::I32(42)));
    }

    #[test]
    fn test_eval_lambda_app() {
        let mut interp = Interpreter::new();
        let lambda = dummy_expr(ExprKind::Lambda {
            param: "x".into(),
            param_ty: Ty::Base(BaseTy::I32),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        let app = dummy_expr(ExprKind::App {
            func: Box::new(lambda),
            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
        });
        let result = interp.eval(&app).unwrap();
        assert!(matches!(result, Value::I32(42)));
    }

    #[test]
    fn test_eval_pair() {
        let mut interp = Interpreter::new();
        let pair = dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });
        let fst = dummy_expr(ExprKind::Fst(Box::new(pair)));
        let result = interp.eval(&fst).unwrap();
        assert!(matches!(result, Value::I32(1)));
    }

    #[test]
    fn test_eval_region() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::Region {
            name: "r".into(),
            body: Box::new(dummy_expr(ExprKind::Let {
                name: "s".into(),
                ty: None,
                value: Box::new(dummy_expr(ExprKind::StringNew {
                    region: "r".into(),
                    value: "hello".into(),
                })),
                body: Box::new(dummy_expr(ExprKind::Drop(Box::new(
                    dummy_expr(ExprKind::Var("s".into()))
                )))),
            })),
        });
        let result = interp.eval(&expr).unwrap();
        assert!(matches!(result, Value::Unit));
    }
}
