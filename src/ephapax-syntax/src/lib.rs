// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Abstract Syntax Tree
//!
//! Core syntax definitions aligned with the formal Coq semantics.

use smol_str::SmolStr;

/// Variable identifier
pub type Var = SmolStr;

/// Region name
pub type RegionName = SmolStr;

/// Source location span
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }
}

/// Linearity annotation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Linearity {
    /// Must use exactly once
    Linear,
    /// May use any number of times
    Unrestricted,
}

/// Base (primitive) types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseTy {
    Unit,
    Bool,
    I32,
    I64,
    F32,
    F64,
}

/// Types with region and linearity annotations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// Primitive type
    Base(BaseTy),

    /// String allocated in a region
    String(RegionName),

    /// Reference with linearity
    Ref {
        linearity: Linearity,
        inner: Box<Ty>,
    },

    /// Function type A -> B
    Fun { param: Box<Ty>, ret: Box<Ty> },

    /// Product type A * B
    Prod { left: Box<Ty>, right: Box<Ty> },

    /// Sum type A + B
    Sum { left: Box<Ty>, right: Box<Ty> },

    /// Region-scoped type
    Region { name: RegionName, inner: Box<Ty> },

    /// Second-class borrow &T
    Borrow(Box<Ty>),

    /// Type variable (for polymorphism, future)
    Var(SmolStr),
}

impl Ty {
    /// Check if type is linear (must be used exactly once)
    pub fn is_linear(&self) -> bool {
        match self {
            Ty::String(_) => true,
            Ty::Ref {
                linearity: Linearity::Linear,
                ..
            } => true,
            Ty::Region { inner, .. } => inner.is_linear(),
            _ => false,
        }
    }
}

/// Literal values
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Unit,
    Bool(bool),
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    String(String),
}

/// Pattern for destructuring
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Wildcard _
    Wildcard,
    /// Variable binding
    Var(Var),
    /// Pair destructuring (p1, p2)
    Pair(Box<Pattern>, Box<Pattern>),
    /// Unit ()
    Unit,
}

/// Expressions
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Literal value
    Lit(Literal),

    /// Variable reference
    Var(Var),

    // ===== String operations =====
    /// String allocation: String.new@r("...")
    StringNew { region: RegionName, value: String },

    /// String concatenation (consumes both)
    StringConcat { left: Box<Expr>, right: Box<Expr> },

    /// String length (borrows)
    StringLen(Box<Expr>),

    // ===== Bindings =====
    /// Let binding: let x = e1 in e2
    Let {
        name: Var,
        ty: Option<Ty>,
        value: Box<Expr>,
        body: Box<Expr>,
    },

    /// Linear let binding: let! x = e1 in e2
    LetLin {
        name: Var,
        ty: Option<Ty>,
        value: Box<Expr>,
        body: Box<Expr>,
    },

    // ===== Functions =====
    /// Lambda: fn(x: T) -> e
    Lambda {
        param: Var,
        param_ty: Ty,
        body: Box<Expr>,
    },

    /// Application: e1 e2
    App { func: Box<Expr>, arg: Box<Expr> },

    // ===== Products =====
    /// Pair: (e1, e2)
    Pair { left: Box<Expr>, right: Box<Expr> },

    /// First projection: e.0
    Fst(Box<Expr>),

    /// Second projection: e.1
    Snd(Box<Expr>),

    // ===== Sums =====
    /// Left injection: inl[T] e
    Inl { ty: Ty, value: Box<Expr> },

    /// Right injection: inr[T] e
    Inr { ty: Ty, value: Box<Expr> },

    /// Case analysis
    Case {
        scrutinee: Box<Expr>,
        left_var: Var,
        left_body: Box<Expr>,
        right_var: Var,
        right_body: Box<Expr>,
    },

    // ===== Control flow =====
    /// Conditional: if e1 then e2 else e3
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    // ===== Regions =====
    /// Region scope: region r { e }
    Region { name: RegionName, body: Box<Expr> },

    // ===== Borrowing =====
    /// Create borrow: &e
    Borrow(Box<Expr>),

    /// Dereference: *e
    Deref(Box<Expr>),

    // ===== Resource management =====
    /// Explicit drop: drop(e)
    Drop(Box<Expr>),

    /// Explicit copy (unrestricted only): copy(e)
    Copy(Box<Expr>),

    // ===== Blocks =====
    /// Sequence of expressions
    Block(Vec<Expr>),
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn dummy(kind: ExprKind) -> Self {
        Self {
            kind,
            span: Span::dummy(),
        }
    }
}

/// Top-level declarations
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// Function definition
    Fn {
        name: Var,
        params: Vec<(Var, Ty)>,
        ret_ty: Ty,
        body: Expr,
    },

    /// Type alias
    Type { name: Var, ty: Ty },
}

/// A complete module
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub name: SmolStr,
    pub decls: Vec<Decl>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_is_linear() {
        let ty = Ty::String("r".into());
        assert!(ty.is_linear());
    }

    #[test]
    fn base_is_unrestricted() {
        let ty = Ty::Base(BaseTy::I32);
        assert!(!ty.is_linear());
    }
}
