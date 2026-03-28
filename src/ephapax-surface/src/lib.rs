#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Surface AST for Ephapax
//!
//! This is the **user-facing** syntax layer — what the parser produces and
//! what humans write. It includes constructs that don't exist in the verified
//! core calculus:
//!
//! - **`data` declarations** — named algebraic data types with constructors
//! - **`match` expressions** — multi-way pattern matching with exhaustiveness
//! - **Named constructors** — `Some(x)` instead of `inr(x)`
//! - **Rich patterns** — wildcards, nested destructuring, literal patterns
//! - **Named type application** — `Option(I32)` instead of `() + I32`
//!
//! The [`ephapax_desugar`] crate transforms this surface AST into the core
//! AST ([`ephapax_syntax`]), which is the minimal calculus that the Coq
//! formal proofs reason about. This layering means:
//!
//! - New surface features never invalidate the proofs
//! - The WASM codegen only handles the small core
//! - Users get expressive syntax without bloating the verified foundation
//!
//! # Shared types
//!
//! Many types are shared with the core: [`Literal`], [`BinOp`], [`UnaryOp`],
//! [`BaseTy`], [`Linearity`], [`Span`]. These are re-exported from
//! [`ephapax_syntax`] so surface consumers don't need to depend on both crates.

use serde::Serialize;
use smol_str::SmolStr;

// Re-export shared types from the core AST.
pub use ephapax_syntax::{BaseTy, BinOp, Linearity, Literal, Span, UnaryOp};

/// Variable identifier (same as core).
pub type Var = SmolStr;

/// Region name (same as core).
pub type RegionName = SmolStr;

/// Type variable name (for parametric data types).
pub type TyVar = SmolStr;

// =========================================================================
// Surface Types
// =========================================================================

/// Surface-level types.
///
/// Extends the core type system with named type application:
/// `Option(I32)`, `Result(String@r, Error)`.
/// The desugaring pass resolves these to the core binary-sum encoding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum SurfaceTy {
    /// Primitive type — same as core
    Base(BaseTy),

    /// String allocated in a region — same as core
    String(RegionName),

    /// Reference with linearity — same as core
    Ref {
        linearity: Linearity,
        inner: Box<SurfaceTy>,
    },

    /// Function type A -> B
    Fun {
        param: Box<SurfaceTy>,
        ret: Box<SurfaceTy>,
    },

    /// Product type A * B
    Prod {
        left: Box<SurfaceTy>,
        right: Box<SurfaceTy>,
    },

    /// Sum type A + B (raw, same as core)
    Sum {
        left: Box<SurfaceTy>,
        right: Box<SurfaceTy>,
    },

    /// Region-scoped type
    Region {
        name: RegionName,
        inner: Box<SurfaceTy>,
    },

    /// Second-class borrow &T
    Borrow(Box<SurfaceTy>),

    /// Type variable (bound by data declaration)
    Var(TyVar),

    /// List type [T]
    List(Box<SurfaceTy>),

    /// Tuple type (T, U, ...)
    Tuple(Vec<SurfaceTy>),

    // === Surface-only types ===
    /// Named type application: `Option(I32)`, `Result(String@r, Error)`
    ///
    /// `name` is the data type name, `args` are the type arguments.
    /// Desugars to the binary-sum encoding of the data declaration.
    Named { name: SmolStr, args: Vec<SurfaceTy> },
}

// =========================================================================
// Patterns
// =========================================================================

/// Patterns for match expressions.
///
/// Patterns are the core of the surface-level pattern matching system.
/// They are checked for exhaustiveness and desugared to nested `case`
/// expressions in the core AST.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum Pattern {
    /// Wildcard: `_` — matches anything, binds nothing.
    Wildcard,

    /// Variable binding: `x` — matches anything, binds it to `x`.
    Var(Var),

    /// Constructor pattern: `Some(x)`, `None`, `Ok((a, b))`
    ///
    /// `ctor` is the constructor name, `args` are the sub-patterns
    /// for the constructor's payload. Nullary constructors have empty args.
    Constructor { ctor: SmolStr, args: Vec<Pattern> },

    /// Literal pattern: `42`, `true`, `"hello"`
    Literal(Literal),

    /// Tuple pattern: `(a, b, c)`
    Tuple(Vec<Pattern>),

    /// Pair pattern: `(a, b)` — specifically two elements (for core Prod type)
    Pair(Box<Pattern>, Box<Pattern>),

    /// Unit pattern: `()`
    Unit,
}

impl Pattern {
    /// Collect all variable bindings in this pattern.
    /// Used for linearity checking — each bound variable gets tracked.
    pub fn bound_vars(&self) -> Vec<Var> {
        match self {
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Unit => vec![],
            Pattern::Var(v) => vec![v.clone()],
            Pattern::Constructor { args, .. } => args.iter().flat_map(|p| p.bound_vars()).collect(),
            Pattern::Tuple(elements) => elements.iter().flat_map(|p| p.bound_vars()).collect(),
            Pattern::Pair(l, r) => {
                let mut vars = l.bound_vars();
                vars.extend(r.bound_vars());
                vars
            }
        }
    }
}

/// A single arm in a match expression.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MatchArm {
    /// The pattern to match against.
    pub pattern: Pattern,
    /// Optional guard: `| Some(x) if x > 0 => ...`
    pub guard: Option<Box<SurfaceExpr>>,
    /// The body to evaluate if the pattern matches.
    pub body: SurfaceExpr,
}

// =========================================================================
// Data Declarations
// =========================================================================

/// A constructor in a data declaration.
///
/// ```text
/// data Option(a) = None | Some(a)
///                   ^^^^   ^^^^^^^
///                   ctor   ctor with payload
/// ```
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ConstructorDef {
    /// Constructor name (e.g. "Some", "None", "Ok")
    pub name: SmolStr,
    /// Payload types (empty for nullary constructors like None)
    pub fields: Vec<SurfaceTy>,
}

/// A data type declaration.
///
/// ```text
/// data Result(a, e) = Ok(a) | Err(e)
///      ^^^^^^ ^^^^    ^^^^    ^^^^^^
///      name   params  constructors
/// ```
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct DataDecl {
    /// The type name (e.g. "Option", "Result", "Color")
    pub name: SmolStr,
    /// Type parameters (e.g. ["a"] for Option, ["a", "e"] for Result)
    pub params: Vec<TyVar>,
    /// The constructors
    pub constructors: Vec<ConstructorDef>,
    /// Source span
    pub span: Span,
}

// =========================================================================
// Surface Expressions
// =========================================================================

/// Surface-level expression.
///
/// Mirrors the core `Expr` but adds `Match` and `Construct` nodes.
/// Everything else passes through to the core unchanged.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct SurfaceExpr {
    pub kind: SurfaceExprKind,
    pub span: Span,
}

impl SurfaceExpr {
    pub fn new(kind: SurfaceExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn dummy(kind: SurfaceExprKind) -> Self {
        Self {
            kind,
            span: Span::dummy(),
        }
    }
}

/// Surface expression kinds.
///
/// Every core expression kind has a counterpart here (for pass-through),
/// plus the surface-only nodes: `Match`, `Construct`.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "node", rename_all = "snake_case")]
pub enum SurfaceExprKind {
    // === Pass-through (same semantics as core) ===
    Lit(Literal),
    Var(Var),

    StringNew {
        region: RegionName,
        value: String,
    },
    StringConcat {
        left: Box<SurfaceExpr>,
        right: Box<SurfaceExpr>,
    },
    StringLen(Box<SurfaceExpr>),

    Let {
        name: Var,
        ty: Option<SurfaceTy>,
        value: Box<SurfaceExpr>,
        body: Box<SurfaceExpr>,
    },

    LetLin {
        name: Var,
        ty: Option<SurfaceTy>,
        value: Box<SurfaceExpr>,
        body: Box<SurfaceExpr>,
    },

    Lambda {
        param: Var,
        param_ty: SurfaceTy,
        body: Box<SurfaceExpr>,
    },

    App {
        func: Box<SurfaceExpr>,
        arg: Box<SurfaceExpr>,
    },

    Pair {
        left: Box<SurfaceExpr>,
        right: Box<SurfaceExpr>,
    },
    Fst(Box<SurfaceExpr>),
    Snd(Box<SurfaceExpr>),

    /// Raw sum injections (still valid at surface level for expert use)
    Inl {
        ty: SurfaceTy,
        value: Box<SurfaceExpr>,
    },
    Inr {
        ty: SurfaceTy,
        value: Box<SurfaceExpr>,
    },

    /// Raw binary case (still valid for expert use — desugars to itself)
    Case {
        scrutinee: Box<SurfaceExpr>,
        left_var: Var,
        left_body: Box<SurfaceExpr>,
        right_var: Var,
        right_body: Box<SurfaceExpr>,
    },

    If {
        cond: Box<SurfaceExpr>,
        then_branch: Box<SurfaceExpr>,
        else_branch: Box<SurfaceExpr>,
    },

    Region {
        name: RegionName,
        body: Box<SurfaceExpr>,
    },
    Borrow(Box<SurfaceExpr>),
    Deref(Box<SurfaceExpr>),
    Drop(Box<SurfaceExpr>),
    Copy(Box<SurfaceExpr>),
    Block(Vec<SurfaceExpr>),

    FFI {
        symbol: String,
        args: Vec<SurfaceExpr>,
    },

    BinOp {
        op: BinOp,
        left: Box<SurfaceExpr>,
        right: Box<SurfaceExpr>,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<SurfaceExpr>,
    },

    ListLit(Vec<SurfaceExpr>),
    ListIndex {
        list: Box<SurfaceExpr>,
        index: Box<SurfaceExpr>,
    },
    TupleLit(Vec<SurfaceExpr>),
    TupleIndex {
        tuple: Box<SurfaceExpr>,
        index: usize,
    },

    // === Surface-only nodes ===
    /// Named constructor application: `Some(x)`, `None`, `Ok(value)`
    ///
    /// Desugars to the appropriate chain of `inl`/`inr` based on
    /// the constructor's position in its data declaration.
    Construct {
        /// Constructor name
        ctor: SmolStr,
        /// Arguments (empty for nullary constructors)
        args: Vec<SurfaceExpr>,
    },

    /// Pattern matching: `match e of | Pat1 => e1 | Pat2 => e2`
    ///
    /// Desugars to nested `case`/`inl`/`inr` expressions.
    /// The desugaring pass also checks exhaustiveness.
    Match {
        /// Expression being matched
        scrutinee: Box<SurfaceExpr>,
        /// Match arms (pattern → body)
        arms: Vec<MatchArm>,
    },
}

// =========================================================================
// Surface Declarations
// =========================================================================

/// Surface-level declarations.
///
/// Extends core `Decl` with data type declarations.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SurfaceDecl {
    /// Function definition (same as core, but with surface types/exprs)
    Fn {
        name: Var,
        params: Vec<(Var, SurfaceTy)>,
        ret_ty: SurfaceTy,
        body: SurfaceExpr,
    },

    /// Type alias (same as core, but with surface types)
    Type { name: Var, ty: SurfaceTy },

    /// Data type declaration (surface-only)
    Data(DataDecl),
}

/// A complete surface-level module.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct SurfaceModule {
    pub name: SmolStr,
    pub decls: Vec<SurfaceDecl>,
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pattern_bound_vars_wildcard() {
        assert!(Pattern::Wildcard.bound_vars().is_empty());
    }

    #[test]
    fn pattern_bound_vars_var() {
        let vars = Pattern::Var("x".into()).bound_vars();
        assert_eq!(vars, vec![SmolStr::from("x")]);
    }

    #[test]
    fn pattern_bound_vars_constructor() {
        // Some((a, b))
        let pat = Pattern::Constructor {
            ctor: "Some".into(),
            args: vec![Pattern::Tuple(vec![
                Pattern::Var("a".into()),
                Pattern::Var("b".into()),
            ])],
        };
        let vars = pat.bound_vars();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&SmolStr::from("a")));
        assert!(vars.contains(&SmolStr::from("b")));
    }

    #[test]
    fn pattern_bound_vars_nested() {
        // Ok(Some(x))
        let pat = Pattern::Constructor {
            ctor: "Ok".into(),
            args: vec![Pattern::Constructor {
                ctor: "Some".into(),
                args: vec![Pattern::Var("x".into())],
            }],
        };
        assert_eq!(pat.bound_vars(), vec![SmolStr::from("x")]);
    }

    #[test]
    fn surface_expr_construct() {
        let expr = SurfaceExpr::dummy(SurfaceExprKind::Construct {
            ctor: "Some".into(),
            args: vec![SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::I32(42)))],
        });
        assert!(matches!(expr.kind, SurfaceExprKind::Construct { .. }));
    }

    #[test]
    fn surface_expr_match() {
        let expr = SurfaceExpr::dummy(SurfaceExprKind::Match {
            scrutinee: Box::new(SurfaceExpr::dummy(SurfaceExprKind::Var("x".into()))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::I32(0))),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Some".into(),
                        args: vec![Pattern::Var("v".into())],
                    },
                    guard: None,
                    body: SurfaceExpr::dummy(SurfaceExprKind::Var("v".into())),
                },
            ],
        });
        if let SurfaceExprKind::Match { arms, .. } = &expr.kind {
            assert_eq!(arms.len(), 2);
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn data_decl_option() {
        let decl = DataDecl {
            name: "Option".into(),
            params: vec!["a".into()],
            constructors: vec![
                ConstructorDef {
                    name: "None".into(),
                    fields: vec![],
                },
                ConstructorDef {
                    name: "Some".into(),
                    fields: vec![SurfaceTy::Var("a".into())],
                },
            ],
            span: Span::dummy(),
        };
        assert_eq!(decl.constructors.len(), 2);
        assert_eq!(decl.params.len(), 1);
    }

    #[test]
    fn data_decl_three_variants() {
        // data Color = Red | Green | Blue
        let decl = DataDecl {
            name: "Color".into(),
            params: vec![],
            constructors: vec![
                ConstructorDef {
                    name: "Red".into(),
                    fields: vec![],
                },
                ConstructorDef {
                    name: "Green".into(),
                    fields: vec![],
                },
                ConstructorDef {
                    name: "Blue".into(),
                    fields: vec![],
                },
            ],
            span: Span::dummy(),
        };
        assert_eq!(decl.constructors.len(), 3);
        assert!(decl.params.is_empty());
    }

    #[test]
    fn named_type() {
        let ty = SurfaceTy::Named {
            name: "Result".into(),
            args: vec![SurfaceTy::Base(BaseTy::I32), SurfaceTy::Base(BaseTy::Bool)],
        };
        if let SurfaceTy::Named { name, args } = &ty {
            assert_eq!(name.as_str(), "Result");
            assert_eq!(args.len(), 2);
        }
    }
}
