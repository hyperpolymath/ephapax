// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Tree-Walking Interpreter
//!
//! A simple interpreter for debugging and rapid development.
//! Useful for testing before compiling to WASM.
//!
//! The evaluator is a loop with its own stack of frames on the heap
//! ([`Interpreter::eval`]). A call in the program uses no native stack,
//! so deep calls end with a value or with the runtime error
//! [`RuntimeError::StackOverflow`]. A [`Value`] shares its parts, and
//! its copy, its print and its free use a loop, so a long list does not
//! exhaust the native stack.

use ephapax_syntax::{
    BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, Pattern, RegionName, Ty, UnaryOp, Var,
};
use smol_str::SmolStr;
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

/// Runtime info for a single constructor: (position, total, arity).
///
/// - **position**: 0-based index in the parent data type's constructor list,
///   defining the inl/inr depth in the runtime `Value::Left`/`Value::Right`
///   chain.
/// - **total**: total number of constructors in the parent data type.
///   When `position == total - 1` ("last"), the value path skips the
///   trailing `Left` (the rightmost summand is bare, not wrapped) —
///   mirrors `ephapax_desugar::wrap_injection`.
/// - **arity**: number of payload fields, used to destructure the payload
///   into `Value::Pair` chains (0 → Unit, 1 → bare, N → right-nested).
#[derive(Debug, Clone, Copy)]
struct InterpCtor {
    position: usize,
    total: usize,
    arity: usize,
}

/// Runtime constructor registry, populated from `Decl::Data` at load time.
/// Used by `eval_match` to resolve `Pattern::Constructor` against the
/// binary-sum value encoding without typing-level info.
#[derive(Debug, Clone, Default)]
struct InterpDataRegistry {
    ctors: HashMap<SmolStr, InterpCtor>,
}

impl InterpDataRegistry {
    fn populate_from_module(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::Data { constructors, .. } = decl {
                let total = constructors.len();
                for (position, ctor) in constructors.iter().enumerate() {
                    self.ctors.insert(
                        ctor.name.as_str().into(),
                        InterpCtor {
                            position,
                            total,
                            arity: ctor.fields.len(),
                        },
                    );
                }
            }
        }
    }

    fn get(&self, name: &str) -> Option<InterpCtor> {
        self.ctors.get(name).copied()
    }
}

/// Runtime errors during interpretation
#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    #[error("Unbound variable: {0}")]
    UnboundVariable(Var),

    #[error("Type error: expected {expected}, got {found}")]
    TypeError { expected: String, found: String },

    #[error("Division by zero")]
    DivisionByZero,

    /// `MIN / -1`: the quotient does not fit. Wasm traps here too.
    #[error("Integer overflow")]
    IntegerOverflow,

    #[error("Unimplemented: {0}")]
    Unimplemented(String),

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

    #[error("Index {index} out of bounds (length {length})")]
    IndexOutOfBounds { index: usize, length: usize },

    /// The calls of the program are too deep: the evaluator has its
    /// greatest number of frames. Wasm traps with this text too.
    #[error("call stack exhausted")]
    StackOverflow,
}

/// Runtime values
///
/// A value shares its parts (`Arc`), so a copy of a value is 1 step for
/// each size of value. A long list is a deep chain of parts: the copy,
/// the print and the free of a value use no native recursion, so the
/// length of a list has no limit from the native stack.
#[derive(Clone)]
pub enum Value {
    Unit,
    Bool(bool),
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    String { data: String, region: RegionName },
    Pair(Arc<Value>, Arc<Value>),
    Tuple(Arc<[Value]>),
    List(Arc<[Value]>),
    Left(Arc<Value>),
    Right(Arc<Value>),
    Closure(Arc<Closure>),
    Borrow(Arc<Value>),
}

/// A function value: its parameter, its body, and the environment of
/// the place that made it.
#[derive(Debug)]
pub struct Closure {
    pub param: Var,
    pub param_ty: Ty,
    pub body: Code,
    pub env: Environment,
}

/// The value of a part: the part itself when no other value shares it,
/// else a copy (which shares the parts of the part).
fn take(part: &mut Arc<Value>) -> Value {
    match Arc::get_mut(part) {
        Some(value) => std::mem::replace(value, Value::Unit),
        None => Value::clone(part),
    }
}

impl Value {
    /// The pair of `left` and `right`.
    pub fn pair(left: Value, right: Value) -> Value {
        Value::Pair(Arc::new(left), Arc::new(right))
    }

    /// The left injection of `value`.
    pub fn left(value: Value) -> Value {
        Value::Left(Arc::new(value))
    }

    /// The right injection of `value`.
    pub fn right(value: Value) -> Value {
        Value::Right(Arc::new(value))
    }

    /// A borrow of `value`.
    pub fn borrow(value: Value) -> Value {
        Value::Borrow(Arc::new(value))
    }

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
            Value::Tuple(_) => "Tuple",
            Value::List(_) => "List",
            Value::Left(_) => "Left",
            Value::Right(_) => "Right",
            Value::Closure(_) => "Function",
            Value::Borrow(_) => "Borrow",
        }
    }

    /// Check if this value is linear (must be used exactly once)
    pub fn is_linear(&self) -> bool {
        let mut work = vec![self];
        while let Some(value) = work.pop() {
            match value {
                // Strings are linear resources
                Value::String { .. } => return true,
                // Pairs are linear if either component is linear
                Value::Pair(l, r) => work.extend([&**l, &**r]),
                // Tuples and lists are linear if any element is linear
                Value::Tuple(elements) | Value::List(elements) => work.extend(elements.iter()),
                // Sum types are linear if either variant type is linear
                Value::Left(v) | Value::Right(v) => work.push(v),
                // Closures that capture linear values are linear
                // (Conservative: treat all closures as potentially linear)
                // Could be refined with capture analysis.
                // Borrows are second-class (not linear in the sense of consumption).
                // Base types are unrestricted.
                _ => {}
            }
        }
        false
    }

    /// Get the inferred type of this value
    pub fn to_type(&self) -> Ty {
        self.type_to_depth(TYPE_DEPTH)
    }

    /// The type of this value, to `depth` levels of parts. A part below
    /// that has the placeholder type `()`, which this function also uses
    /// for the side of a sum that the value does not have.
    // snip: a depth limit, because `Ty` is a boxed tree and a long list
    // gives a type as deep as the list; upgrade to the declared type of
    // the value when the interpreter has types.
    fn type_to_depth(&self, depth: usize) -> Ty {
        let unit = || Ty::Base(BaseTy::Unit);
        let Some(depth) = depth.checked_sub(1) else {
            return unit();
        };
        let part = |value: &Value| Box::new(value.type_to_depth(depth));
        match self {
            Value::Unit => unit(),
            Value::Bool(_) => Ty::Base(BaseTy::Bool),
            Value::I32(_) => Ty::Base(BaseTy::I32),
            Value::I64(_) => Ty::Base(BaseTy::I64),
            Value::F32(_) => Ty::Base(BaseTy::F32),
            Value::F64(_) => Ty::Base(BaseTy::F64),
            Value::String { region, .. } => Ty::String(region.clone()),
            Value::Pair(l, r) => Ty::Prod {
                left: part(l),
                right: part(r),
            },
            Value::Tuple(elements) => Ty::Tuple(elements.iter().map(|v| *part(v)).collect()),
            Value::List(elements) => Ty::List(elements.first().map_or(Box::new(unit()), part)),
            Value::Left(v) => Ty::Sum {
                left: part(v),
                right: Box::new(unit()),
            },
            Value::Right(v) => Ty::Sum {
                left: Box::new(unit()),
                right: part(v),
            },
            Value::Closure(closure) => Ty::Fun {
                param: Box::new(closure.param_ty.clone()),
                ret: Box::new(unit()), // Unknown without evaluation
            },
            Value::Borrow(inner) => Ty::Borrow {
                inner: part(inner),
                mutable: false,
            },
        }
    }

    /// Move each part of this value that has parts of its own, and that
    /// no other value shares, into `out`.
    fn take_parts(&mut self, out: &mut Vec<Value>) {
        let mut take = |part: &mut Value| {
            if !matches!(
                part,
                Value::Unit
                    | Value::Bool(_)
                    | Value::I32(_)
                    | Value::I64(_)
                    | Value::F32(_)
                    | Value::F64(_)
                    | Value::String { .. }
            ) {
                out.push(std::mem::replace(part, Value::Unit));
            }
        };
        match self {
            Value::Pair(left, right) => {
                Arc::get_mut(left).map(&mut take);
                Arc::get_mut(right).map(&mut take);
            }
            Value::Left(part) | Value::Right(part) | Value::Borrow(part) => {
                Arc::get_mut(part).map(&mut take);
            }
            Value::Tuple(parts) | Value::List(parts) => {
                if let Some(parts) = Arc::get_mut(parts) {
                    parts.iter_mut().for_each(&mut take);
                }
            }
            Value::Closure(closure) => {
                if let Some(closure) = Arc::get_mut(closure) {
                    closure.env.bindings.values_mut().for_each(&mut take);
                }
            }
            _ => {}
        }
    }
}

/// The depth of parts to which [`Value::to_type`] gives a type.
const TYPE_DEPTH: usize = 64;

impl Drop for Value {
    /// Free the parts with a loop. The default drop goes 1 native call
    /// deeper for each part of a chain, and a long list is a long chain.
    fn drop(&mut self) {
        let mut parts = Vec::new();
        self.take_parts(&mut parts);
        while let Some(mut part) = parts.pop() {
            part.take_parts(&mut parts);
            // `part` has no part with parts now: its drop is 1 step.
        }
    }
}

impl std::fmt::Display for Value {
    /// Print with a loop: the work list has the values and the texts
    /// that are still to print, the next one last.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Item<'a> {
            Value(&'a Value),
            Text(&'static str),
        }
        // The parts of a sequence, with ", " between them.
        fn sequence<'a>(work: &mut Vec<Item<'a>>, open: &'static str, parts: &'a [Value]) {
            for (i, part) in parts.iter().enumerate().rev() {
                work.push(Item::Value(part));
                if i > 0 {
                    work.push(Item::Text(", "));
                }
            }
            work.push(Item::Text(open));
        }
        let mut work = vec![Item::Value(self)];
        while let Some(item) = work.pop() {
            let value = match item {
                Item::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                Item::Value(value) => value,
            };
            match value {
                Value::Unit => write!(f, "()")?,
                Value::Bool(b) => write!(f, "{}", b)?,
                Value::I32(n) => write!(f, "{}", n)?,
                Value::I64(n) => write!(f, "{}i64", n)?,
                Value::F32(n) => write!(f, "{}f32", n)?,
                Value::F64(n) => write!(f, "{}", n)?,
                Value::String { data, region } => write!(f, "\"{}\"@{}", data, region)?,
                Value::Pair(l, r) => {
                    work.push(Item::Text(")"));
                    work.push(Item::Value(r));
                    work.push(Item::Text(", "));
                    work.push(Item::Value(l));
                    work.push(Item::Text("("));
                }
                Value::Tuple(elements) => {
                    work.push(Item::Text(")"));
                    sequence(&mut work, "(", elements);
                }
                Value::List(elements) => {
                    work.push(Item::Text("]"));
                    sequence(&mut work, "[", elements);
                }
                Value::Left(v) => {
                    work.push(Item::Text(")"));
                    work.push(Item::Value(v));
                    work.push(Item::Text("inl("));
                }
                Value::Right(v) => {
                    work.push(Item::Text(")"));
                    work.push(Item::Value(v));
                    work.push(Item::Text("inr("));
                }
                Value::Closure(closure) => write!(f, "<fn({})>", closure.param)?,
                Value::Borrow(v) => {
                    work.push(Item::Value(v));
                    work.push(Item::Text("&"));
                }
            }
        }
        Ok(())
    }
}

/// The debug form is the printed form: a derived form goes 1 native call
/// deeper for each part.
impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

/// Environment for variable bindings
#[derive(Debug, Clone, Default)]
pub struct Environment {
    /// Variable bindings (pub for save-restore in eval_let/eval_case)
    pub bindings: HashMap<Var, Value>,
    /// Track which linear values have been consumed
    pub consumed: HashMap<Var, bool>,
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

/// A top-level function, in the form that the evaluator runs.
struct Function {
    params: Vec<(Var, Ty)>,
    body: Arc<Node>,
    /// The function as a value ([`function_value`]).
    value: Value,
}

/// Interpreter state
pub struct Interpreter {
    env: Environment,
    /// Active regions stack
    regions: Vec<RegionName>,
    /// Function definitions
    functions: HashMap<Var, Function>,
    /// The value expression of each top-level constant.
    constants: HashMap<Var, Arc<Node>>,
    /// Data declarations from loaded modules, used by `eval_match` to
    /// resolve `Pattern::Constructor` against the runtime binary-sum
    /// encoding.
    data_registry: InterpDataRegistry,
    /// Loaded native libraries for FFI (dlopen handles).
    /// Libraries are kept alive for the lifetime of the interpreter.
    ffi_libraries: Vec<libloading::Library>,
}

/// Compare a runtime `Value` against a `Literal` for pattern matching.
/// Type mismatches (e.g. comparing a `Value::String` against `Literal::I32`)
/// fail silently — they're already rejected by the typechecker, and at
/// match time we just want a boolean "is this the same constant value?".
fn value_matches_literal(val: &Value, lit: &Literal) -> bool {
    match (val, lit) {
        (Value::Unit, Literal::Unit) => true,
        (Value::Bool(a), Literal::Bool(b)) => a == b,
        (Value::I32(a), Literal::I32(b)) => a == b,
        (Value::I64(a), Literal::I64(b)) => a == b,
        (Value::F32(a), Literal::F32(b)) => a == b,
        (Value::F64(a), Literal::F64(b)) => a == b,
        (Value::String { data, .. }, Literal::String(s)) => data == s,
        _ => false,
    }
}

/// The greatest number of frames of the evaluator. A frame holds the work
/// that waits for a value, so this is the limit of the depth of the calls
/// of a program. More frames give [`RuntimeError::StackOverflow`].
const MAX_FRAMES: usize = 1_000_000;

/// The code of a closure, in the form that the evaluator runs.
#[derive(Clone)]
pub struct Code(Arc<Node>);

impl std::fmt::Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<code>")
    }
}

/// An expression in the form that the evaluator runs. Each part is
/// shared, so a frame of the evaluator can hold the part that runs next.
#[derive(Debug)]
enum Node {
    Lit(Literal),
    Var(Var),
    StringNew {
        region: RegionName,
        value: String,
    },
    Lambda {
        param: Var,
        param_ty: Ty,
        body: Arc<Node>,
    },
    Unary(Unary, Arc<Node>),
    Binary(Binary, Arc<Node>, Arc<Node>),
    Let {
        name: Var,
        value: Arc<Node>,
        body: Arc<Node>,
    },
    If {
        cond: Arc<Node>,
        then_branch: Arc<Node>,
        else_branch: Arc<Node>,
    },
    /// `left` and `right`: the name and the body of each branch.
    Case {
        scrutinee: Arc<Node>,
        left: (Var, Arc<Node>),
        right: (Var, Arc<Node>),
    },
    Match {
        scrutinee: Arc<Node>,
        arms: Arc<[Arm]>,
    },
    Region {
        name: RegionName,
        body: Arc<Node>,
    },
    Seq(Seq, Arc<[Arc<Node>]>),
    /// A form with no implementation in the interpreter: the text of the
    /// error.
    Unimplemented(&'static str),
}

/// An arm of a [`Node::Match`].
#[derive(Debug)]
struct Arm {
    pattern: Pattern,
    guard: Option<Arc<Node>>,
    body: Arc<Node>,
}

/// An operation on the value of 1 operand.
#[derive(Debug, Clone, Copy)]
enum Unary {
    Op(UnaryOp),
    StringLen,
    Fst,
    Snd,
    Inl,
    Inr,
    Borrow,
    Deref,
    Drop,
    Copy,
    TupleIndex(usize),
}

/// An operation on the values of 2 operands, the left one first.
#[derive(Debug, Clone, Copy)]
enum Binary {
    Op(BinOp),
    Concat,
    Pair,
    ListIndex,
    /// The function, then its argument.
    App,
}

/// The forms with a sequence of parts, each evaluated in order.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Seq {
    Block,
    List,
    Tuple,
}

impl Seq {
    /// The value of the form from the values of its parts. For a block,
    /// `values` has the value of the last part only.
    fn value(self, mut values: Vec<Value>) -> Value {
        match self {
            Seq::Block => values.pop().unwrap_or(Value::Unit),
            Seq::List => Value::List(values.into()),
            Seq::Tuple => Value::Tuple(values.into()),
        }
    }
}

/// The form of `expr` that the evaluator runs.
fn lower(expr: &Expr) -> Arc<Node> {
    let unary = |op, inner: &Expr| Node::Unary(op, lower(inner));
    let binary = |op, left: &Expr, right: &Expr| Node::Binary(op, lower(left), lower(right));
    let seq = |kind, parts: &[Expr]| Node::Seq(kind, parts.iter().map(lower).collect());
    Arc::new(match &expr.kind {
        ExprKind::Lit(lit) => Node::Lit(lit.clone()),
        // The interpreter runs a generic function as it is: the type
        // arguments select no code.
        ExprKind::Var(name) | ExprKind::TypeApp { name, .. } => Node::Var(name.clone()),
        ExprKind::StringNew { region, value } => Node::StringNew {
            region: region.clone(),
            value: value.clone(),
        },
        ExprKind::StringConcat { left, right } => binary(Binary::Concat, left, right),
        ExprKind::StringLen(inner) => unary(Unary::StringLen, inner),
        ExprKind::Let {
            name, value, body, ..
        }
        | ExprKind::LetLin {
            name, value, body, ..
        } => Node::Let {
            name: name.clone(),
            value: lower(value),
            body: lower(body),
        },
        ExprKind::Lambda {
            param,
            param_ty,
            body,
        } => Node::Lambda {
            param: param.clone(),
            param_ty: param_ty.clone(),
            body: lower(body),
        },
        ExprKind::App { func, arg } => binary(Binary::App, func, arg),
        ExprKind::Pair { left, right } => binary(Binary::Pair, left, right),
        ExprKind::Fst(inner) => unary(Unary::Fst, inner),
        ExprKind::Snd(inner) => unary(Unary::Snd, inner),
        ExprKind::Inl { value, .. } => unary(Unary::Inl, value),
        ExprKind::Inr { value, .. } => unary(Unary::Inr, value),
        // A value of a recursive type is the value of its unfolding:
        // `fold` and `unfold` change the type only.
        ExprKind::Fold { value, .. } | ExprKind::Unfold(value) => return lower(value),
        ExprKind::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => Node::Case {
            scrutinee: lower(scrutinee),
            left: (left_var.clone(), lower(left_body)),
            right: (right_var.clone(), lower(right_body)),
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => Node::If {
            cond: lower(cond),
            then_branch: lower(then_branch),
            else_branch: lower(else_branch),
        },
        ExprKind::Region { name, body } => Node::Region {
            name: name.clone(),
            body: lower(body),
        },
        ExprKind::Borrow { inner, .. } => unary(Unary::Borrow, inner),
        ExprKind::Deref(inner) => unary(Unary::Deref, inner),
        ExprKind::Drop(inner) => unary(Unary::Drop, inner),
        ExprKind::Copy(inner) => unary(Unary::Copy, inner),
        ExprKind::Block(exprs) => seq(Seq::Block, exprs),
        ExprKind::BinOp { op, left, right } => binary(Binary::Op(*op), left, right),
        ExprKind::UnaryOp { op, operand } => unary(Unary::Op(*op), operand),
        ExprKind::ListLit(elements) => seq(Seq::List, elements),
        ExprKind::ListIndex { list, index } => binary(Binary::ListIndex, list, index),
        ExprKind::TupleLit(exprs) => seq(Seq::Tuple, exprs),
        ExprKind::TupleIndex { tuple, index } => unary(Unary::TupleIndex(*index), tuple),
        ExprKind::FFI { .. } => {
            Node::Unimplemented("raw __ffi is not supported; use typed extern declarations")
        }
        ExprKind::Perform { .. } => {
            Node::Unimplemented("effect perform not yet implemented in interpreter")
        }
        ExprKind::Handle { .. } => {
            Node::Unimplemented("effect handle not yet implemented in interpreter")
        }
        ExprKind::Match { scrutinee, arms } => Node::Match {
            scrutinee: lower(scrutinee),
            arms: arms
                .iter()
                .map(|arm| Arm {
                    pattern: arm.pattern.clone(),
                    guard: arm.guard.as_deref().map(lower),
                    body: lower(&arm.body),
                })
                .collect(),
        },
    })
}

/// The evaluator either evaluates code or has a value for the top frame.
enum State {
    Eval(Arc<Node>),
    Value(Value),
}

/// What a name had before a binding: its value and its consumed mark.
type Saved = (Var, Option<Value>, Option<bool>);

/// Work that waits for a value. The frames are on the heap: they take the
/// place of the native stack frames of a recursive evaluator.
enum Frame {
    /// The operand of a unary operation.
    Unary(Unary),
    /// The left operand of a binary operation; the code of the right one.
    Left(Binary, Arc<Node>),
    /// The right operand of a binary operation; the value of the left one.
    Right(Binary, Value),
    /// The value of a `let`; its name and its body.
    Let(Var, Arc<Node>),
    /// The condition of an `if`; its 2 branches.
    If(Arc<Node>, Arc<Node>),
    /// The scrutinee of a `case`; the name and the body of each branch.
    Case((Var, Arc<Node>), (Var, Arc<Node>)),
    /// The scrutinee of a `match`.
    Match(Arc<[Arm]>),
    /// The guard of arm `arm`, with the names of the arm bound.
    Guard {
        arms: Arc<[Arm]>,
        arm: usize,
        scrutinee: Value,
        saved: Vec<Saved>,
    },
    /// Part `next - 1` of a sequence; the values of the parts before it.
    Seq {
        kind: Seq,
        parts: Arc<[Arc<Node>]>,
        next: usize,
        values: Vec<Value>,
    },
    /// The body of a `let`, of a `case` branch or of a match arm: its
    /// names go out of scope.
    Unbind(Vec<Saved>),
    /// The body of a closure or the value of a constant: the evaluation
    /// goes back to this environment.
    Env(Environment),
    /// The body of a region: the region ends.
    Region(RegionName),
}

/// A top-level function as a value: a closure for its first
/// parameter, with a lambda in its body for each next parameter. So
/// `f(a, b)`, which is `(f a) b`, gives each parameter its argument.
/// A function with no parameter takes the unit argument of `f()`.
/// The closure starts from an empty environment: the body of a
/// top-level function sees its parameters and the top-level
/// functions, and no local name of the caller.
fn function_value(params: &[(Var, Ty)], body: &Arc<Node>) -> Value {
    let mut params = params.iter().cloned();
    let (param, param_ty) = params
        .next()
        .unwrap_or_else(|| ("_".into(), Ty::Base(BaseTy::Unit)));
    let body = params.rev().fold(body.clone(), |body, (param, param_ty)| {
        Arc::new(Node::Lambda {
            param,
            param_ty,
            body,
        })
    });
    Value::Closure(Arc::new(Closure {
        param,
        param_ty,
        body: Code(body),
        env: Environment::new(),
    }))
}

/// The element `index` of a list value.
fn list_element(elements: &[Value], index: usize) -> Result<Value, RuntimeError> {
    elements
        .get(index)
        .cloned()
        .ok_or(RuntimeError::IndexOutOfBounds {
            index,
            length: elements.len(),
        })
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Environment::new(),
            regions: Vec::new(),
            functions: HashMap::new(),
            constants: HashMap::new(),
            data_registry: InterpDataRegistry::default(),
            ffi_libraries: Vec::new(),
        }
    }

    /// Load a native shared library for FFI calls.
    ///
    /// Symbols from the library become available to `__ffi("symbol", ...)`.
    /// The library handle is kept alive until the interpreter is dropped.
    ///
    /// # Safety
    /// Loading shared libraries is inherently unsafe. The caller must
    /// ensure the library is trustworthy.
    pub fn load_ffi_library(&mut self, path: &str) -> Result<(), RuntimeError> {
        // SAFETY: Loading a shared library is unsafe because the loaded code
        // is unverified; caller trust is documented in this fn's `# Safety`
        // section. The handle is stored in `self.ffi_libraries` and kept alive
        // until the interpreter is dropped, so no symbol outlives its library.
        let lib = unsafe {
            libloading::Library::new(path).map_err(|e| {
                RuntimeError::Unimplemented(format!("Failed to load FFI library '{}': {}", path, e))
            })?
        };
        self.ffi_libraries.push(lib);
        Ok(())
    }

    /// Load a module (register all function definitions and data decls).
    pub fn load_module(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::Fn {
                name, params, body, ..
            } = decl
            {
                let body = lower(body);
                let function = Function {
                    value: function_value(params, &body),
                    params: params.clone(),
                    body,
                };
                self.functions.insert(name.clone(), function);
            }
            if let Decl::Const { name, value, .. } = decl {
                self.constants.insert(name.clone(), lower(value));
            }
        }
        self.data_registry.populate_from_module(module);
    }

    /// Evaluate an expression
    pub fn eval(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        self.run(lower(expr))
    }

    /// Run `code` to a value. The work that waits for a value is in
    /// `stack`, on the heap, so a call in the program uses no native
    /// stack: the limit of the depth is [`MAX_FRAMES`], not the size of
    /// the native stack.
    fn run(&mut self, code: Arc<Node>) -> Result<Value, RuntimeError> {
        let mut stack: Vec<Frame> = Vec::new();
        let mut state = State::Eval(code);
        loop {
            let step = match state {
                State::Eval(code) => self.enter(&code, &mut stack),
                State::Value(value) => match stack.pop() {
                    Some(frame) => self.resume(frame, value, &mut stack),
                    None => return Ok(value),
                },
            };
            state = match step {
                Ok(state) if stack.len() <= MAX_FRAMES => state,
                step => {
                    // An error ends each frame, the top one first: the
                    // names, the environment and the regions are as they
                    // were before the evaluation. So a caller that keeps
                    // the interpreter after an error (the REPL) does not
                    // see the names of the call that failed.
                    for frame in stack.into_iter().rev() {
                        match frame {
                            Frame::Env(saved) => self.env = saved,
                            Frame::Unbind(saved) | Frame::Guard { saved, .. } => self.unbind(saved),
                            Frame::Region(_) => {
                                self.regions.pop();
                            }
                            _ => {}
                        }
                    }
                    return Err(step.err().unwrap_or(RuntimeError::StackOverflow));
                }
            };
        }
    }

    /// Start the evaluation of `code`: give its value, or push a frame for
    /// the rest of its work and give the part to evaluate first.
    fn enter(&mut self, code: &Arc<Node>, stack: &mut Vec<Frame>) -> Result<State, RuntimeError> {
        let first = match &**code {
            Node::Lit(lit) => return Ok(State::Value(self.eval_lit(lit)?)),
            Node::Var(name) => return self.enter_var(name, stack),
            Node::StringNew { region, value } => {
                return Ok(State::Value(self.eval_string_new(region, value)?));
            }
            Node::Lambda {
                param,
                param_ty,
                body,
            } => {
                return Ok(State::Value(Value::Closure(Arc::new(Closure {
                    param: param.clone(),
                    param_ty: param_ty.clone(),
                    body: Code(body.clone()),
                    env: self.env.clone(),
                }))));
            }
            Node::Unimplemented(what) => {
                return Err(RuntimeError::Unimplemented((*what).into()));
            }
            Node::Unary(op, inner) => {
                // A borrow of a variable reads the value and leaves it in
                // place: `&s` is not a use of `s`.
                if let (Unary::Borrow, Node::Var(name)) = (op, &**inner) {
                    if self.env.is_consumed(name) {
                        return Err(RuntimeError::LinearValueConsumed);
                    }
                    if let Some(value) = self.env.get(name) {
                        return Ok(State::Value(Value::borrow(value.clone())));
                    }
                }
                stack.push(Frame::Unary(*op));
                inner
            }
            Node::Binary(op, left, right) => {
                stack.push(Frame::Left(*op, right.clone()));
                left
            }
            Node::Let { name, value, body } => {
                stack.push(Frame::Let(name.clone(), body.clone()));
                value
            }
            Node::If {
                cond,
                then_branch,
                else_branch,
            } => {
                stack.push(Frame::If(then_branch.clone(), else_branch.clone()));
                cond
            }
            Node::Case {
                scrutinee,
                left,
                right,
            } => {
                stack.push(Frame::Case(left.clone(), right.clone()));
                scrutinee
            }
            Node::Match { scrutinee, arms } => {
                stack.push(Frame::Match(arms.clone()));
                scrutinee
            }
            Node::Region { name, body } => {
                self.regions.push(name.clone());
                stack.push(Frame::Region(name.clone()));
                body
            }
            Node::Seq(kind, parts) => match parts.first() {
                Some(first) => {
                    stack.push(Frame::Seq {
                        kind: *kind,
                        parts: parts.clone(),
                        next: 1,
                        values: Vec::new(),
                    });
                    first
                }
                None => return Ok(State::Value(kind.value(Vec::new()))),
            },
        };
        Ok(State::Eval(first.clone()))
    }

    /// Continue the work of `frame` with the `value` that it waits for.
    fn resume(
        &mut self,
        frame: Frame,
        mut value: Value,
        stack: &mut Vec<Frame>,
    ) -> Result<State, RuntimeError> {
        let next = match frame {
            Frame::Unary(op) => return Ok(State::Value(self.unary(op, value)?)),
            Frame::Left(op, right) => {
                stack.push(Frame::Right(op, value));
                right
            }
            Frame::Right(op, left) => return self.binary(op, left, value, stack),
            Frame::Let(name, body) => {
                let saved = self.bind(vec![(name, value)]);
                stack.push(Frame::Unbind(saved));
                body
            }
            Frame::If(then_branch, else_branch) => match value {
                Value::Bool(true) => then_branch,
                Value::Bool(false) => else_branch,
                other => {
                    return Err(RuntimeError::TypeError {
                        expected: "Bool".to_string(),
                        found: other.type_name().to_string(),
                    });
                }
            },
            Frame::Case(left, right) => {
                let ((name, body), inner) = match &mut value {
                    Value::Left(inner) => (left, take(inner)),
                    Value::Right(inner) => (right, take(inner)),
                    _ => return Err(RuntimeError::NotASum),
                };
                let saved = self.bind(vec![(name, inner)]);
                stack.push(Frame::Unbind(saved));
                body
            }
            Frame::Match(arms) => return self.match_arms(arms, value, 0, stack),
            Frame::Guard {
                arms,
                arm,
                scrutinee,
                saved,
            } => match value {
                Value::Bool(true) => {
                    stack.push(Frame::Unbind(saved));
                    arms[arm].body.clone()
                }
                // The guard is false: the names of the arm go out of
                // scope, and the next arms get the value.
                Value::Bool(false) => {
                    self.unbind(saved);
                    return self.match_arms(arms, scrutinee, arm + 1, stack);
                }
                other => {
                    return Err(RuntimeError::TypeError {
                        expected: "Bool".into(),
                        found: other.type_name().into(),
                    });
                }
            },
            Frame::Seq {
                kind,
                parts,
                next,
                mut values,
            } => {
                if kind == Seq::Block {
                    values.clear();
                }
                values.push(value);
                match parts.get(next).cloned() {
                    Some(part) => {
                        stack.push(Frame::Seq {
                            kind,
                            parts,
                            next: next + 1,
                            values,
                        });
                        part
                    }
                    None => return Ok(State::Value(kind.value(values))),
                }
            }
            Frame::Unbind(saved) => {
                self.unbind(saved);
                return Ok(State::Value(value));
            }
            Frame::Env(saved) => {
                self.env = saved;
                return Ok(State::Value(value));
            }
            Frame::Region(name) => {
                self.regions.pop();
                // Check for region escape
                if let Value::String { region, data } = &value {
                    if *region == name {
                        return Err(RuntimeError::StringEscaped(data.clone()));
                    }
                }
                return Ok(State::Value(value));
            }
        };
        Ok(State::Eval(next))
    }

    /// Bind each name of `bindings` in the environment. The result has
    /// what each name had before, for [`Self::unbind`].
    fn bind(&mut self, bindings: Vec<(Var, Value)>) -> Vec<Saved> {
        // Save-restore: prevents environment leaking between nested let bindings.
        // The old extend/remove pattern clobbered outer bindings on name shadowing
        // and leaked intermediate env state to sibling expressions.
        // See formal/DESIGN-NOTE-2026-03-28.md for the soundness proof.
        let saved = bindings
            .iter()
            .map(|(name, _)| {
                (
                    name.clone(),
                    self.env.bindings.get(name).cloned(),
                    self.env.consumed.get(name).copied(),
                )
            })
            .collect();
        for (name, value) in bindings {
            self.env.extend(name, value);
        }
        saved
    }

    /// Give each name of `saved` what it had before [`Self::bind`], the
    /// last name first.
    fn unbind(&mut self, saved: Vec<Saved>) {
        for (name, value, consumed) in saved.into_iter().rev() {
            match value {
                Some(value) => {
                    self.env.bindings.insert(name.clone(), value);
                    if let Some(consumed) = consumed {
                        self.env.consumed.insert(name, consumed);
                    }
                }
                None => self.env.remove(&name),
            }
        }
    }

    /// The result of `op` on the value of its operand.
    fn unary(&self, op: Unary, mut val: Value) -> Result<Value, RuntimeError> {
        match op {
            Unary::Op(op) => self.eval_unaryop(op, val),
            Unary::StringLen => match &val {
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
            },
            Unary::Fst => match &mut val {
                Value::Pair(left, _) => Ok(take(left)),
                _ => Err(RuntimeError::NotAPair),
            },
            Unary::Snd => match &mut val {
                Value::Pair(_, right) => Ok(take(right)),
                _ => Err(RuntimeError::NotAPair),
            },
            Unary::Inl => Ok(Value::left(val)),
            Unary::Inr => Ok(Value::right(val)),
            Unary::Borrow => Ok(Value::borrow(val)),
            Unary::Deref => match &mut val {
                Value::Borrow(inner) => Ok(take(inner)),
                _ => Err(RuntimeError::TypeError {
                    expected: "Borrow".to_string(),
                    found: val.type_name().to_string(),
                }),
            },
            // Evaluate and discard
            Unary::Drop => Ok(Value::Unit),
            Unary::Copy => {
                // Only unrestricted types can be copied - linear types (String, etc.) cannot
                if val.is_linear() {
                    return Err(RuntimeError::TypeError {
                        expected: "unrestricted (copyable) type".to_string(),
                        found: format!("linear type {}", val.type_name()),
                    });
                }
                // For unrestricted types, return a pair of copies
                Ok(Value::pair(val.clone(), val))
            }
            Unary::TupleIndex(index) => match &mut val {
                Value::Tuple(values) => {
                    if index < values.len() {
                        Ok(values[index].clone())
                    } else {
                        Err(RuntimeError::Unimplemented(format!(
                            "tuple index {} out of bounds",
                            index
                        )))
                    }
                }
                // A 2-tuple is a pair.
                Value::Pair(left, _) if index == 0 => Ok(take(left)),
                Value::Pair(_, right) if index == 1 => Ok(take(right)),
                _ => Err(RuntimeError::Unimplemented(
                    "tuple index on non-tuple".to_string(),
                )),
            },
        }
    }

    /// The result of `op` on the values of its 2 operands. A call gives
    /// the body of the function, to evaluate in the environment of the
    /// closure.
    fn binary(
        &mut self,
        op: Binary,
        left: Value,
        right: Value,
        stack: &mut Vec<Frame>,
    ) -> Result<State, RuntimeError> {
        Ok(State::Value(match op {
            Binary::Op(op) => self.eval_binop(op, left, right)?,
            Binary::Concat => self.eval_string_concat(left, right)?,
            Binary::Pair => Value::pair(left, right),
            Binary::ListIndex => match (&left, &right) {
                (Value::List(elements), Value::I32(i)) => list_element(elements, *i as usize)?,
                (Value::List(elements), Value::I64(i)) => list_element(elements, *i as usize)?,
                _ => {
                    return Err(RuntimeError::TypeError {
                        expected: "list and integer".to_string(),
                        found: "non-list or non-integer".to_string(),
                    });
                }
            },
            Binary::App => match &left {
                Value::Closure(closure) => {
                    let mut callee = closure.env.clone();
                    callee.extend(closure.param.clone(), right);
                    let caller = std::mem::replace(&mut self.env, callee);
                    stack.push(Frame::Env(caller));
                    return Ok(State::Eval(closure.body.0.clone()));
                }
                _ => return Err(RuntimeError::NotAFunction),
            },
        }))
    }

    fn eval_binop(
        &self,
        op: BinOp,
        left_val: Value,
        right_val: Value,
    ) -> Result<Value, RuntimeError> {
        // Integer arithmetic wraps, as the compiled wasm does. `/` and `%`
        // by zero, and `MIN / -1`, are errors (wasm traps); `MIN % -1` is 0.
        match op {
            BinOp::Add => self.numeric_binop(
                left_val,
                right_val,
                |a, b| Ok(a.wrapping_add(b)),
                |a, b| Ok(a.wrapping_add(b)),
                |a, b| a + b,
            ),
            BinOp::Sub => self.numeric_binop(
                left_val,
                right_val,
                |a, b| Ok(a.wrapping_sub(b)),
                |a, b| Ok(a.wrapping_sub(b)),
                |a, b| a - b,
            ),
            BinOp::Mul => self.numeric_binop(
                left_val,
                right_val,
                |a, b| Ok(a.wrapping_mul(b)),
                |a, b| Ok(a.wrapping_mul(b)),
                |a, b| a * b,
            ),
            BinOp::Div => self.numeric_binop(
                left_val,
                right_val,
                |a, b| match b {
                    0 => Err(RuntimeError::DivisionByZero),
                    _ => a.checked_div(b).ok_or(RuntimeError::IntegerOverflow),
                },
                |a, b| match b {
                    0 => Err(RuntimeError::DivisionByZero),
                    _ => a.checked_div(b).ok_or(RuntimeError::IntegerOverflow),
                },
                |a, b| a / b,
            ),
            BinOp::Mod => self.numeric_binop(
                left_val,
                right_val,
                |a, b| match b {
                    0 => Err(RuntimeError::DivisionByZero),
                    _ => Ok(a.wrapping_rem(b)),
                },
                |a, b| match b {
                    0 => Err(RuntimeError::DivisionByZero),
                    _ => Ok(a.wrapping_rem(b)),
                },
                |a, b| a % b,
            ),
            BinOp::Lt => self.compare_op(left_val, right_val, |a, b| a < b, |a, b| a < b),
            BinOp::Le => self.compare_op(left_val, right_val, |a, b| a <= b, |a, b| a <= b),
            BinOp::Gt => self.compare_op(left_val, right_val, |a, b| a > b, |a, b| a > b),
            BinOp::Ge => self.compare_op(left_val, right_val, |a, b| a >= b, |a, b| a >= b),
            BinOp::Eq => Ok(Value::Bool(self.values_equal(&left_val, &right_val))),
            BinOp::Ne => Ok(Value::Bool(!self.values_equal(&left_val, &right_val))),
            BinOp::And => match (left_val, right_val) {
                (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
                (l, r) => Err(RuntimeError::TypeError {
                    expected: "Bool".to_string(),
                    found: format!("{}, {}", l.type_name(), r.type_name()),
                }),
            },
            BinOp::Or => match (left_val, right_val) {
                (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
                (l, r) => Err(RuntimeError::TypeError {
                    expected: "Bool".to_string(),
                    found: format!("{}, {}", l.type_name(), r.type_name()),
                }),
            },
        }
    }

    /// Apply a numeric operator to 2 values of one numeric type, with the
    /// function for that type.
    fn numeric_binop(
        &self,
        left: Value,
        right: Value,
        i32_op: impl Fn(i32, i32) -> Result<i32, RuntimeError>,
        i64_op: impl Fn(i64, i64) -> Result<i64, RuntimeError>,
        float_op: impl Fn(f64, f64) -> f64,
    ) -> Result<Value, RuntimeError> {
        match (left, right) {
            (Value::I32(a), Value::I32(b)) => Ok(Value::I32(i32_op(a, b)?)),
            (Value::I64(a), Value::I64(b)) => Ok(Value::I64(i64_op(a, b)?)),
            // An F32 operation done in F64 and rounded once gives the
            // correctly rounded F32 result.
            (Value::F32(a), Value::F32(b)) => Ok(Value::F32(float_op(a as f64, b as f64) as f32)),
            (Value::F64(a), Value::F64(b)) => Ok(Value::F64(float_op(a, b))),
            (l, r) => Err(RuntimeError::TypeError {
                expected: "numeric type".to_string(),
                found: format!("{}, {}", l.type_name(), r.type_name()),
            }),
        }
    }

    fn compare_op<I, F>(
        &self,
        left: Value,
        right: Value,
        int_op: I,
        float_op: F,
    ) -> Result<Value, RuntimeError>
    where
        I: Fn(i64, i64) -> bool,
        F: Fn(f64, f64) -> bool,
    {
        match (left, right) {
            (Value::I32(a), Value::I32(b)) => Ok(Value::Bool(int_op(a as i64, b as i64))),
            (Value::I64(a), Value::I64(b)) => Ok(Value::Bool(int_op(a, b))),
            (Value::F32(a), Value::F32(b)) => Ok(Value::Bool(float_op(a as f64, b as f64))),
            (Value::F64(a), Value::F64(b)) => Ok(Value::Bool(float_op(a, b))),
            (l, r) => Err(RuntimeError::TypeError {
                expected: "numeric type".to_string(),
                found: format!("{}, {}", l.type_name(), r.type_name()),
            }),
        }
    }

    fn values_equal(&self, left: &Value, right: &Value) -> bool {
        match (left, right) {
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::I32(a), Value::I32(b)) => a == b,
            (Value::I64(a), Value::I64(b)) => a == b,
            (Value::F32(a), Value::F32(b)) => a == b,
            (Value::F64(a), Value::F64(b)) => a == b,
            (Value::String { data: d1, .. }, Value::String { data: d2, .. }) => d1 == d2,
            _ => false,
        }
    }

    fn eval_unaryop(&self, op: UnaryOp, val: Value) -> Result<Value, RuntimeError> {
        match op {
            UnaryOp::Not => match val {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                v => Err(RuntimeError::TypeError {
                    expected: "Bool".to_string(),
                    found: v.type_name().to_string(),
                }),
            },
            UnaryOp::Neg => match val {
                Value::I32(n) => Ok(Value::I32(n.wrapping_neg())),
                Value::I64(n) => Ok(Value::I64(n.wrapping_neg())),
                Value::F32(n) => Ok(Value::F32(-n)),
                Value::F64(n) => Ok(Value::F64(-n)),
                v => Err(RuntimeError::TypeError {
                    expected: "numeric type".to_string(),
                    found: v.type_name().to_string(),
                }),
            },
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

    /// The value of the name `name`. A constant gives its value
    /// expression, to evaluate in an empty environment.
    fn enter_var(&mut self, name: &Var, stack: &mut Vec<Frame>) -> Result<State, RuntimeError> {
        // A parameter or a `let` of this name shadows a top-level
        // function, also after its value was consumed.
        let local = self.env.get(name).is_some() || self.env.is_consumed(name);
        if !local {
            if let Some(function) = self.functions.get(name) {
                return Ok(State::Value(function.value.clone()));
            }
            // A constant: its value, from an empty environment, at each
            // use of the name (as wasm, which calls a function).
            if let Some(value) = self.constants.get(name).cloned() {
                stack.push(Frame::Env(std::mem::take(&mut self.env)));
                return Ok(State::Eval(value));
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

        Ok(State::Value(value))
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

    fn eval_string_concat(&self, left_val: Value, right_val: Value) -> Result<Value, RuntimeError> {
        match (&left_val, &right_val) {
            (
                Value::String {
                    data: d1,
                    region: r1,
                },
                Value::String {
                    data: d2,
                    region: r2,
                },
            ) => {
                if r1 != r2 {
                    return Err(RuntimeError::TypeError {
                        expected: format!("String@{}", r1),
                        found: format!("String@{}", r2),
                    });
                }
                Ok(Value::String {
                    data: format!("{d1}{d2}"),
                    region: r1.clone(),
                })
            }
            (l, r) => Err(RuntimeError::TypeError {
                expected: "String".to_string(),
                found: format!("{}, {}", l.type_name(), r.type_name()),
            }),
        }
    }

    /// Give `scrutinee` to the arms of a match, from arm `start`.
    ///
    /// Tries each arm in order; on the first matching pattern, binds
    /// captured names in the environment and gives the guard of the arm,
    /// or its body, to evaluate. No arms matching is a runtime
    /// error — the typechecker's exhaustiveness pass should prevent
    /// this when the module is well-typed.
    fn match_arms(
        &mut self,
        arms: Arc<[Arm]>,
        scrutinee: Value,
        start: usize,
        stack: &mut Vec<Frame>,
    ) -> Result<State, RuntimeError> {
        for (index, arm) in arms.iter().enumerate().skip(start) {
            let mut bindings: Vec<(Var, Value)> = Vec::new();
            if !self.try_match_pattern(&scrutinee, &arm.pattern, &mut bindings)? {
                continue;
            }
            let saved = self.bind(bindings);
            return Ok(State::Eval(match &arm.guard {
                None => {
                    stack.push(Frame::Unbind(saved));
                    arm.body.clone()
                }
                // The guard runs under the pattern bindings of the arm.
                Some(guard) => {
                    let guard = guard.clone();
                    stack.push(Frame::Guard {
                        arms: arms.clone(),
                        arm: index,
                        scrutinee,
                        saved,
                    });
                    guard
                }
            }));
        }
        Err(RuntimeError::PatternMatchFailed)
    }

    /// Check whether `val` matches `pat`, collecting variable bindings
    /// into `out`. Read-only on the interpreter state — the caller
    /// applies (or discards) the bindings after deciding which arm to
    /// run. A failed match returns `Ok(false)`; structural errors
    /// (unknown constructor, ill-typed value) return `Err`.
    fn try_match_pattern(
        &self,
        val: &Value,
        pat: &Pattern,
        out: &mut Vec<(Var, Value)>,
    ) -> Result<bool, RuntimeError> {
        match pat {
            Pattern::Wildcard => Ok(true),
            Pattern::Var(name) => {
                out.push((name.clone(), val.clone()));
                Ok(true)
            }
            Pattern::Literal(lit) => Ok(value_matches_literal(val, lit)),
            Pattern::Unit => Ok(matches!(val, Value::Unit)),
            Pattern::Pair(lpat, rpat) => match val {
                Value::Pair(lv, rv) => {
                    if !self.try_match_pattern(lv, lpat, out)? {
                        return Ok(false);
                    }
                    self.try_match_pattern(rv, rpat, out)
                }
                _ => Ok(false),
            },
            Pattern::Tuple(parts) => match val {
                Value::Tuple(vals) if vals.len() == parts.len() => {
                    for (p, v) in parts.iter().zip(vals.iter()) {
                        if !self.try_match_pattern(v, p, out)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            },
            Pattern::Constructor { ctor, args } => {
                let info = self.data_registry.get(ctor.as_str()).ok_or_else(|| {
                    RuntimeError::Unimplemented(format!("unknown constructor `{}`", ctor))
                })?;
                if args.len() != info.arity {
                    return Err(RuntimeError::TypeError {
                        expected: format!("{} arg(s) for constructor `{}`", info.arity, ctor),
                        found: format!("{} arg(s)", args.len()),
                    });
                }

                // Walk `position` levels of Right-wrapping. The last
                // constructor (position == total-1) is encoded bare
                // (no trailing Left), all others wrap their payload
                // in Left after the Right-chain.
                let mut current = val;
                for _ in 0..info.position {
                    match current {
                        Value::Right(inner) => current = inner,
                        _ => return Ok(false),
                    }
                }
                let payload: &Value = if info.position + 1 < info.total {
                    match current {
                        Value::Left(inner) => inner,
                        _ => return Ok(false),
                    }
                } else {
                    current
                };

                match info.arity {
                    0 => Ok(matches!(payload, Value::Unit)),
                    1 => self.try_match_pattern(payload, &args[0], out),
                    _ => self.try_match_pair_chain(payload, args, out),
                }
            }
        }
    }

    /// Destructure a right-nested `Value::Pair` chain against a flat
    /// list of patterns. Mirrors `ephapax_desugar::build_payload_expr`:
    /// `(a, b, c)` was constructed as `Pair(a, Pair(b, c))`.
    fn try_match_pair_chain(
        &self,
        val: &Value,
        args: &[Pattern],
        out: &mut Vec<(Var, Value)>,
    ) -> Result<bool, RuntimeError> {
        if args.len() == 1 {
            return self.try_match_pattern(val, &args[0], out);
        }
        match val {
            Value::Pair(lv, rv) => {
                if !self.try_match_pattern(lv, &args[0], out)? {
                    return Ok(false);
                }
                self.try_match_pair_chain(rv, &args[1..], out)
            }
            _ => Ok(false),
        }
    }

    /// Get a binding from the environment
    pub fn get_binding(&self, name: &str) -> Option<&Value> {
        let name: SmolStr = name.into();
        self.env.get(&name)
    }

    /// Check if a function is defined.
    pub fn has_function(&self, name: &str) -> bool {
        let name: SmolStr = name.into();
        self.functions.contains_key(&name)
    }

    /// Call the main function (no arguments)
    pub fn call_main(&mut self) -> Result<Value, RuntimeError> {
        let name: SmolStr = "main".into();

        let main = self
            .functions
            .get(&name)
            .ok_or_else(|| RuntimeError::UnboundVariable(name.clone()))?;

        // Main should have no parameters
        if !main.params.is_empty() {
            return Err(RuntimeError::TypeError {
                expected: "main with no parameters".to_string(),
                found: format!("main with {} parameters", main.params.len()),
            });
        }

        self.run(main.body.clone())
    }

    /// Call a named function with arguments
    pub fn call(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let name: SmolStr = name.into();

        let function = self
            .functions
            .get(&name)
            .ok_or_else(|| RuntimeError::UnboundVariable(name.clone()))?;
        let (params, body) = (function.params.clone(), function.body.clone());

        if args.len() != params.len() {
            return Err(RuntimeError::TypeError {
                expected: format!("{} arguments", params.len()),
                found: format!("{} arguments", args.len()),
            });
        }

        // Save-restore: snapshot env before binding params, restore after.
        // Matches the substitution-based semantics proven in formal/Semantics.v.
        let saved_env = self.env.clone();

        // Bind parameters
        for ((param_name, _), arg) in params.iter().zip(args) {
            self.env.extend(param_name.clone(), arg);
        }

        // Evaluate body
        let result = self.run(body);

        // Restore previous environment
        self.env = saved_env;

        result
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
        let result = interp.eval(&expr).expect("eval should succeed");
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
        let result = interp.eval(&expr).expect("eval should succeed");
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
        let result = interp.eval(&expr).expect("eval should succeed");
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
        let result = interp.eval(&app).expect("eval should succeed");
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
        let result = interp.eval(&fst).expect("eval should succeed");
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
                body: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                    ExprKind::Var("s".into()),
                ))))),
            })),
        });
        let result = interp.eval(&expr).expect("eval should succeed");
        assert!(matches!(result, Value::Unit));
    }

    // =========================================================================
    // ExprKind::Match — runtime evaluation
    // =========================================================================

    use ephapax_syntax::{ConstructorDef, MatchArm, Pattern as P, Visibility};

    fn option_module() -> Module {
        Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![Decl::Data {
                name: "Option".into(),
                type_params: vec!["a".into()],
                constructors: vec![
                    ConstructorDef {
                        name: "None".into(),
                        fields: vec![],
                    },
                    ConstructorDef {
                        name: "Some".into(),
                        fields: vec![Ty::Var("a".into())],
                    },
                ],
            }],
        }
    }

    fn lit_i32_expr(n: i32) -> Expr {
        dummy_expr(ExprKind::Lit(Literal::I32(n)))
    }

    /// `match Some(7) of | None => 0 | Some(v) => v end → 7`.
    #[test]
    fn test_eval_match_option_some() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());

        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32_expr(7)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: lit_i32_expr(0),
                },
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    },
                    guard: None,
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(7)), "got {:?}", result);
    }

    /// `match None of | None => 99 | Some(_) => 0 end → 99`. None is
    /// position-0-of-2 so the value is `Left(Unit)`; the matcher must
    /// pick the None arm.
    #[test]
    fn test_eval_match_option_none() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());

        let scrut = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: lit_i32_expr(99),
                },
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Wildcard],
                    },
                    guard: None,
                    body: lit_i32_expr(0),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(99)));
    }

    /// Wildcard arm fires when no constructor arm matches.
    #[test]
    fn test_eval_match_wildcard_fallback() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());

        let scrut = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Wildcard],
                    },
                    guard: None,
                    body: lit_i32_expr(1),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    body: lit_i32_expr(42),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(42)));
    }

    /// Literal patterns dispatch by equality.
    #[test]
    fn test_eval_match_literal_patterns() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(lit_i32_expr(2)),
            arms: vec![
                MatchArm {
                    pattern: P::Literal(Literal::I32(1)),
                    guard: None,
                    body: lit_i32_expr(10),
                },
                MatchArm {
                    pattern: P::Literal(Literal::I32(2)),
                    guard: None,
                    body: lit_i32_expr(20),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    body: lit_i32_expr(99),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(20)));
    }

    /// `data Tri = A | B | C` with three constructors: the last
    /// constructor `C` is encoded BARE (no trailing Left), so the
    /// matcher must NOT expect a Left wrap at position 2 of 3.
    #[test]
    fn test_eval_match_three_ctor_last_position_bare() {
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![Decl::Data {
                name: "Tri".into(),
                type_params: vec![],
                constructors: vec![
                    ConstructorDef {
                        name: "A".into(),
                        fields: vec![],
                    },
                    ConstructorDef {
                        name: "B".into(),
                        fields: vec![],
                    },
                    ConstructorDef {
                        name: "C".into(),
                        fields: vec![],
                    },
                ],
            }],
        };
        let mut interp = Interpreter::new();
        interp.load_module(&module);

        // Value for C: inr(inr(Unit)) — two Right wraps, no trailing Left.
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(dummy_expr(ExprKind::Inr {
                ty: Ty::Base(BaseTy::Unit),
                value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
            })),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "A".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: lit_i32_expr(1),
                },
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "B".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: lit_i32_expr(2),
                },
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "C".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: lit_i32_expr(3),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(3)), "got {:?}", result);
    }

    /// Variable binding inside constructor pattern is restored after
    /// the arm body runs — no leak into the enclosing scope.
    #[test]
    fn test_eval_match_binding_restored() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());

        // Pre-bind `v` to 100 in the enclosing scope.
        interp.env.extend("v".into(), Value::I32(100));

        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32_expr(7)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    },
                    guard: None,
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    body: lit_i32_expr(0),
                },
            ],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(7)));

        let outer = interp.env.get(&Var::from("v")).cloned().unwrap();
        assert!(
            matches!(outer, Value::I32(100)),
            "outer v leaked: {:?}",
            outer
        );
    }

    /// Multi-field constructor: `Pair(a, b)` of arity 2 lives in a
    /// `Value::Pair(va, vb)` payload — the matcher destructures via
    /// the right-nested chain.
    #[test]
    fn test_eval_match_multi_field_constructor() {
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![Decl::Data {
                name: "P".into(),
                type_params: vec![],
                constructors: vec![ConstructorDef {
                    name: "Pr".into(),
                    fields: vec![Ty::Base(BaseTy::I32), Ty::Base(BaseTy::I32)],
                }],
            }],
        };
        let mut interp = Interpreter::new();
        interp.load_module(&module);

        // Pr has total=1, so no Sum wrap — value is the payload directly:
        // (a, b) = Pair(I32(3), I32(4)).
        let scrut = dummy_expr(ExprKind::Pair {
            left: Box::new(lit_i32_expr(3)),
            right: Box::new(lit_i32_expr(4)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![MatchArm {
                pattern: P::Constructor {
                    ctor: "Pr".into(),
                    args: vec![P::Var("a".into()), P::Var("b".into())],
                },
                guard: None,
                body: dummy_expr(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(dummy_expr(ExprKind::Var("a".into()))),
                    right: Box::new(dummy_expr(ExprKind::Var("b".into()))),
                }),
            }],
        });
        let result = interp.eval(&expr).expect("match should evaluate");
        assert!(matches!(result, Value::I32(7)), "got {:?}", result);
    }

    /// No arms match → PatternMatchFailed.
    #[test]
    fn test_eval_match_no_arm_matches() {
        let mut interp = Interpreter::new();
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(lit_i32_expr(99)),
            arms: vec![MatchArm {
                pattern: P::Literal(Literal::I32(0)),
                guard: None,
                body: lit_i32_expr(1),
            }],
        });
        let err = interp.eval(&expr).unwrap_err();
        assert!(
            matches!(err, RuntimeError::PatternMatchFailed),
            "got {:?}",
            err
        );
        // suppress unused-import warning for Visibility (held for symmetry
        // with the typing test module pattern).
        let _ = Visibility::Private;
    }

    // ----- Match guards (#67) -----

    /// Guard reads pattern-bound var and evaluates to `true` → arm body
    /// runs. `match Some(7) { Some(v) if v > 0 => v | _ => 0 }` = 7.
    #[test]
    fn test_eval_match_guard_pass() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32_expr(7)),
        });
        let guard = dummy_expr(ExprKind::BinOp {
            op: BinOp::Gt,
            left: Box::new(dummy_expr(ExprKind::Var("v".into()))),
            right: Box::new(lit_i32_expr(0)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    },
                    guard: Some(Box::new(guard)),
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    body: lit_i32_expr(0),
                },
            ],
        });
        let result = interp.eval(&expr).expect("guarded match should evaluate");
        assert!(matches!(result, Value::I32(7)), "got {:?}", result);
    }

    /// Guard evaluates to `false` → arm is skipped, next arm runs.
    /// `match Some(-3) { Some(v) if v > 0 => v | _ => 0 }` = 0.
    #[test]
    fn test_eval_match_guard_fail_falls_through() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32_expr(-3)),
        });
        let guard = dummy_expr(ExprKind::BinOp {
            op: BinOp::Gt,
            left: Box::new(dummy_expr(ExprKind::Var("v".into()))),
            right: Box::new(lit_i32_expr(0)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    },
                    guard: Some(Box::new(guard)),
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    body: lit_i32_expr(0),
                },
            ],
        });
        let result = interp
            .eval(&expr)
            .expect("guard fall-through should evaluate");
        assert!(matches!(result, Value::I32(0)), "got {:?}", result);
    }

    /// Failed guard must not leak its bindings into subsequent arms.
    /// `v` is pre-bound in the enclosing scope; the first arm tries to
    /// rebind `v` and its guard fails — the second arm must see the
    /// original `v`.
    #[test]
    fn test_eval_match_failed_guard_does_not_leak_bindings() {
        let mut interp = Interpreter::new();
        interp.load_module(&option_module());
        interp.env.extend("v".into(), Value::I32(999));

        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32_expr(-1)),
        });
        let guard = dummy_expr(ExprKind::BinOp {
            op: BinOp::Gt,
            left: Box::new(dummy_expr(ExprKind::Var("v".into()))),
            right: Box::new(lit_i32_expr(0)),
        });
        let expr = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                MatchArm {
                    pattern: P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    },
                    guard: Some(Box::new(guard)),
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
                MatchArm {
                    pattern: P::Wildcard,
                    guard: None,
                    // Second arm reads the OUTER `v` (still 999).
                    body: dummy_expr(ExprKind::Var("v".into())),
                },
            ],
        });
        let result = interp.eval(&expr).expect("fall-through should evaluate");
        assert!(matches!(result, Value::I32(999)), "got {:?}", result);
    }

    /// A module with `fn f(n: I32): I32 = if n == 0 then 0 else 1 + f(n - step)`
    /// and the constant `K = 1 / 0`.
    fn recursion_module(step: i32) -> Module {
        let var = |name: &str| dummy_expr(ExprKind::Var(name.into()));
        let int = |n: i32| dummy_expr(ExprKind::Lit(Literal::I32(n)));
        let op = |op, left: Expr, right: Expr| {
            dummy_expr(ExprKind::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            })
        };
        let call = dummy_expr(ExprKind::App {
            func: Box::new(var("f")),
            arg: Box::new(op(BinOp::Sub, var("n"), int(step))),
        });
        let body = dummy_expr(ExprKind::If {
            cond: Box::new(op(BinOp::Eq, var("n"), int(0))),
            then_branch: Box::new(int(0)),
            else_branch: Box::new(op(BinOp::Add, int(1), call)),
        });
        Module {
            name: "m".into(),
            imports: Vec::new(),
            decls: vec![
                Decl::Fn {
                    name: "f".into(),
                    visibility: Default::default(),
                    type_params: Vec::new(),
                    params: vec![("n".into(), Ty::Base(BaseTy::I32))],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body,
                },
                Decl::Const {
                    name: "K".into(),
                    ty: None,
                    value: op(BinOp::Div, int(1), int(0)),
                },
            ],
        }
    }

    /// A call uses no native stack: 100000 calls deep give a value on the
    /// 2 MB stack of a test thread. (The recursive evaluator aborted the
    /// process at a depth of about 160 on a stack of 8 MB.)
    #[test]
    fn deep_calls_use_no_native_stack() {
        let mut interp = Interpreter::new();
        interp.load_module(&recursion_module(1));
        let result = interp.call("f", vec![Value::I32(100_000)]);
        assert!(matches!(result, Ok(Value::I32(100_000))), "{result:?}");
    }

    /// Calls with no end give the named error at the limit of the frames.
    #[test]
    fn calls_with_no_end_are_a_named_error() {
        let mut interp = Interpreter::new();
        interp.load_module(&recursion_module(0));
        let result = interp.call("f", vec![Value::I32(1)]);
        assert!(
            matches!(result, Err(RuntimeError::StackOverflow)),
            "{result:?}"
        );
        // The error ends the calls: the parameter of `f` is not bound.
        assert!(interp.get_binding("n").is_none());
        let call = dummy_expr(ExprKind::App {
            func: Box::new(dummy_expr(ExprKind::Var("f".into()))),
            arg: Box::new(lit_i32_expr(1)),
        });
        assert!(matches!(
            interp.eval(&call),
            Err(RuntimeError::StackOverflow)
        ));
        assert!(interp.get_binding("n").is_none());
    }

    /// The printed form of each kind of value.
    #[test]
    fn a_value_prints_each_of_its_parts() {
        let int = Value::I32;
        let string = Value::String {
            data: "a".into(),
            region: "r".into(),
        };
        let list = Value::List(vec![int(2), int(3)].into());
        let nested = Value::pair(int(1), Value::left(Value::borrow(list)));
        assert_eq!(nested.to_string(), "(1, inl(&[2, 3]))");
        let tuple = Value::Tuple(vec![Value::Unit, Value::right(string), Value::I64(5)].into());
        assert_eq!(tuple.to_string(), "((), inr(\"a\"@r), 5i64)");
        assert_eq!(Value::Tuple(Vec::new().into()).to_string(), "()");
        assert_eq!(Value::List(Vec::new().into()).to_string(), "[]");
        assert_eq!(format!("{:?}", Value::F32(1.5)), "1.5f32");
        assert_eq!(
            function_value(&[], &lower(&lit_i32_expr(1))).to_string(),
            "<fn(_)>"
        );
    }

    /// A list of 1000000 elements is a chain of 2000000 parts. Its copy,
    /// its print, its type, its linearity and its free use no native
    /// recursion: they run on the 2 MB stack of a test thread. (With
    /// boxed parts, the copy of 1000 elements overflowed that stack.)
    #[test]
    fn a_long_list_value_uses_no_native_stack() {
        let mut list = Value::left(Value::Unit);
        for i in 0..1_000_000 {
            list = Value::right(Value::pair(Value::I32(i), list));
        }
        let copy = list.clone();
        assert!(!list.is_linear());
        assert!(matches!(list.to_type(), Ty::Sum { .. }));
        // "inr((" + number + ", " for each element, "inl(())" at the end,
        // and "))" for each element.
        let digits: usize = (0..1_000_000).map(|i: i32| i.to_string().len()).sum();
        assert_eq!(list.to_string().len(), digits + 9 * 1_000_000 + 7);
        drop(list);
        drop(copy);
    }

    /// An error in the value of a constant gives the environment back to
    /// the code that used the constant.
    #[test]
    fn an_error_in_a_constant_keeps_the_environment_of_its_user() {
        let mut interp = Interpreter::new();
        interp.load_module(&recursion_module(1));
        interp.env.extend("v".into(), Value::I32(100));
        let result = interp.eval(&dummy_expr(ExprKind::Var("K".into())));
        assert!(
            matches!(result, Err(RuntimeError::DivisionByZero)),
            "{result:?}"
        );
        assert!(matches!(interp.get_binding("v"), Some(Value::I32(100))));
    }
}

#[cfg(test)]
mod ffi_regression {
    use super::*;
    use ephapax_syntax::Span;
    #[test]
    fn raw_ffi_is_rejected_before_arguments_are_evaluated() {
        let call = Expr::new(
            ExprKind::FFI {
                symbol: "unchecked".into(),
                args: vec![Expr::new(ExprKind::Var("missing".into()), Span::dummy())],
            },
            Span::dummy(),
        );
        assert!(matches!(
            Interpreter::new().eval(&call),
            Err(RuntimeError::Unimplemented(_))
        ));
    }
}
