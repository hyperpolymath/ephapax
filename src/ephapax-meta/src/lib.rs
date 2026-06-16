// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Metainterpreter + metacompiler foundation for ephapax.
//!
//! # What this is
//!
//! Two reflective capabilities, each a thin wrapper over machinery that
//! already exists — no second AST encoding, no second evaluator, no
//! second codegen:
//!
//! - **Metainterpreter** ([`ReflectiveInterp`]): ephapax syntax can be
//!   treated as *data* ([`quote`]), evaluated back to a value
//!   ([`ReflectiveInterp::eval_quoted`]), and — for non-linear results —
//!   lifted from a value back into syntax ([`reify_value`]). The
//!   canonical "AST as data" representation is the existing
//!   [`ephapax_ir::SExpr`] codec; quoting is `expr_to_sexpr`, unquoting is
//!   `decode_expr`.
//!
//! - **Metacompiler** ([`WasmStager`]): an ephapax expression can be
//!   compiled to wasm at "compile time" and executed, reusing the real
//!   [`ephapax_wasm::Codegen`] and wasmtime. This is the staging hook:
//!   `compile_stage` turns a (closed) expression into a validated module;
//!   `run_stage` runs it.
//!
//! # Substructural discipline
//!
//! Quoting copies *syntax*, never a runtime value, so it cannot duplicate
//! a linear resource. The only value-to-syntax crossing is
//! [`reify_value`], which **hard-refuses** any `is_linear` value (a String
//! or a compound containing one) and any closure — there is no sound way
//! to splice a linear resource into syntax that may be evaluated more than
//! once. Stages are closed terms.
//!
//! # What this is NOT (yet)
//!
//! A *foundation*, honestly labelled. Surface syntax (`quote`/`eval`/
//! `stage` keywords in `.eph`) is deliberately NOT added here — that would
//! ripple new `ExprKind` variants through the parser, desugarer, type
//! checker, interpreter, and codegen. The reflection surface is exposed at
//! the Rust API level first (against the existing SExpr codec), and the
//! surface-syntax wiring is a documented follow-up. `run_stage` today
//! proves the staged module *compiles and runs without trapping*; reading
//! a typed return value back out of the module is a documented next step —
//! the value-producing half of staging is already covered by the
//! metainterpreter (`eval_quoted`).

use ephapax_interp::{Interpreter, Value};
use ephapax_ir::{decode_expr, expr_to_sexpr, SExpr, SExprError};
use ephapax_syntax::{Expr, ExprKind, Literal};
use ephapax_wasm::Codegen;

/// Errors from reflection / staging.
#[derive(Debug)]
pub enum MetaError {
    /// A runtime value has no syntactic literal form (closure, compound).
    CannotReify(&'static str),
    /// Refused to reify/splice a linear value — would duplicate a resource.
    LinearSplice(&'static str),
    /// Decoding quoted syntax back into an AST failed.
    Decode(SExprError),
    /// Evaluating quoted syntax failed at runtime.
    Eval(String),
    /// The staged module failed structural validation.
    InvalidModule(String),
    /// Instantiating or running the staged module failed/trapped.
    Run(String),
}

impl std::fmt::Display for MetaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetaError::CannotReify(t) => write!(f, "cannot reify a {t} value into syntax"),
            MetaError::LinearSplice(t) => {
                write!(f, "refused to reify linear {t} value (would duplicate a resource)")
            }
            MetaError::Decode(e) => write!(f, "decode error: {e}"),
            MetaError::Eval(e) => write!(f, "eval error: {e}"),
            MetaError::InvalidModule(e) => write!(f, "staged module invalid: {e}"),
            MetaError::Run(e) => write!(f, "staged run failed: {e}"),
        }
    }
}

impl std::error::Error for MetaError {}

// ---------------------------------------------------------------------------
// Reflection surface (free functions; the canonical codec is ephapax-ir's)
// ---------------------------------------------------------------------------

/// Quote: lift an AST to data. Reuses `ephapax_ir::expr_to_sexpr`.
pub fn quote(expr: &Expr) -> SExpr {
    expr_to_sexpr(expr)
}

/// Unquote: lower quoted data back to an AST. Reuses `decode_expr`.
pub fn unquote(sexpr: &SExpr) -> Result<Expr, MetaError> {
    decode_expr(sexpr).map_err(MetaError::Decode)
}

/// Reify a runtime value into quoted syntax. Refuses linear values (would
/// duplicate a resource) and values with no literal form (closures,
/// compounds). Only the unrestricted base values have a syntactic literal.
pub fn reify_value(value: &Value) -> Result<SExpr, MetaError> {
    if value.is_linear() {
        return Err(MetaError::LinearSplice(value.type_name()));
    }
    let lit = match value {
        Value::Unit => Literal::Unit,
        Value::Bool(b) => Literal::Bool(*b),
        Value::I32(n) => Literal::I32(*n),
        Value::I64(n) => Literal::I64(*n),
        Value::F32(x) => Literal::F32(*x),
        Value::F64(x) => Literal::F64(*x),
        _ => return Err(MetaError::CannotReify(value.type_name())),
    };
    Ok(quote(&Expr::dummy(ExprKind::Lit(lit))))
}

// ---------------------------------------------------------------------------
// Metainterpreter
// ---------------------------------------------------------------------------

/// A reflective interpreter: treat ephapax syntax as data, evaluate it, and
/// (for non-linear results) lift values back to syntax.
pub struct ReflectiveInterp {
    inner: Interpreter,
}

impl ReflectiveInterp {
    /// A fresh reflective interpreter.
    pub fn new() -> Self {
        Self { inner: Interpreter::new() }
    }

    /// Quote an expression to data.
    pub fn quote(&self, expr: &Expr) -> SExpr {
        quote(expr)
    }

    /// Evaluate quoted data: decode it, then run it through the real
    /// interpreter.
    pub fn eval_quoted(&mut self, sexpr: &SExpr) -> Result<Value, MetaError> {
        let expr = unquote(sexpr)?;
        self.inner
            .eval(&expr)
            .map_err(|e| MetaError::Eval(e.to_string()))
    }

    /// Splice a value into quoted syntax (refuses linear / non-base values).
    pub fn splice(&self, value: &Value) -> Result<SExpr, MetaError> {
        reify_value(value)
    }

    /// Access the underlying interpreter (e.g. to load a module first).
    pub fn interpreter(&mut self) -> &mut Interpreter {
        &mut self.inner
    }
}

impl Default for ReflectiveInterp {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Metacompiler (staging)
// ---------------------------------------------------------------------------

/// A staging compiler: compile an ephapax expression to wasm at compile
/// time and run it, reusing the real `Codegen` + wasmtime.
pub struct WasmStager;

impl WasmStager {
    /// A new stager.
    pub fn new() -> Self {
        WasmStager
    }

    /// Compile a (closed) expression to a wasm module, asserting structural
    /// validity (the same floor the CLI enforces).
    pub fn compile_stage(&self, expr: &Expr) -> Result<Vec<u8>, MetaError> {
        let mut cg = Codegen::new();
        let wasm = cg.compile_program(expr);
        wasmparser::validate(&wasm).map_err(|e| MetaError::InvalidModule(e.to_string()))?;
        Ok(wasm)
    }

    /// Compile and execute a staged expression's `main`, returning `Ok` on a
    /// clean (non-trapping) run.
    pub fn run_stage(&self, expr: &Expr) -> Result<(), MetaError> {
        let wasm = self.compile_stage(expr)?;
        run_main(&wasm).map_err(MetaError::Run)
    }
}

impl Default for WasmStager {
    fn default() -> Self {
        Self::new()
    }
}

/// Instantiate a module and run its `main` (`() -> ()`), providing the same
/// `env` import stubs the e2e harness uses. Returns `Err` on a trap or any
/// instantiation failure.
fn run_main(wasm: &[u8]) -> Result<(), String> {
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, wasm).map_err(|e| e.to_string())?;
    let mut store = wasmtime::Store::new(&engine, ());
    let mut linker = wasmtime::Linker::new(&engine);
    linker
        .func_wrap("env", "print_i32", |_: i32| {})
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap("env", "print_string", |_: i32, _: i32| {})
        .map_err(|e| e.to_string())?;
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| e.to_string())?;
    let main = instance
        .get_typed_func::<(), ()>(&mut store, "main")
        .map_err(|e| e.to_string())?;
    main.call(&mut store, ()).map_err(|e| e.to_string())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::{BinOp, Expr, ExprKind, Literal};

    /// `a * b` as an AST.
    fn mul(a: i32, b: i32) -> Expr {
        Expr::dummy(ExprKind::BinOp {
            op: BinOp::Mul,
            left: Box::new(Expr::dummy(ExprKind::Lit(Literal::I32(a)))),
            right: Box::new(Expr::dummy(ExprKind::Lit(Literal::I32(b)))),
        })
    }

    fn as_i32(v: &Value) -> Option<i32> {
        match v {
            Value::I32(n) => Some(*n),
            _ => None,
        }
    }

    #[test]
    fn quote_unquote_roundtrip() {
        let e = mul(6, 7);
        let q = quote(&e);
        let back = unquote(&q).expect("decode quoted AST");
        assert_eq!(back, e); // Expr derives PartialEq
    }

    #[test]
    fn metainterpreter_evaluates_quoted() {
        let mut ri = ReflectiveInterp::new();
        let q = ri.quote(&mul(6, 7));
        let v = ri.eval_quoted(&q).expect("eval quoted");
        assert_eq!(as_i32(&v), Some(42));
    }

    #[test]
    fn metacompiler_stages_and_runs() {
        let stager = WasmStager::new();
        let wasm = stager.compile_stage(&mul(6, 7)).expect("compile stage");
        assert!(wasm.starts_with(b"\0asm"), "valid wasm magic");
        stager.run_stage(&mul(6, 7)).expect("staged run must not trap");
    }

    #[test]
    fn reify_lifts_base_value_and_roundtrips() {
        let s = reify_value(&Value::I32(42)).expect("reify i32");
        let mut ri = ReflectiveInterp::new();
        assert_eq!(as_i32(&ri.eval_quoted(&s).unwrap()), Some(42));
    }

    #[test]
    fn reify_refuses_linear() {
        // A String value is linear; reifying it must be refused, not
        // silently duplicated.
        let linear = Value::String {
            data: "x".to_string(),
            region: "r".into(),
        };
        assert!(matches!(
            reify_value(&linear),
            Err(MetaError::LinearSplice(_))
        ));
    }

    #[test]
    fn reify_refuses_closure() {
        // Build a closure value by evaluating a lambda, then try to reify.
        let mut ri = ReflectiveInterp::new();
        let lam = Expr::dummy(ExprKind::Lambda {
            param: "x".into(),
            param_ty: ephapax_syntax::Ty::Base(ephapax_syntax::BaseTy::I32),
            body: Box::new(Expr::dummy(ExprKind::Var("x".into()))),
        });
        let v = ri.interpreter().eval(&lam).expect("eval lambda");
        assert!(matches!(reify_value(&v), Err(MetaError::CannotReify(_))));
    }
}
