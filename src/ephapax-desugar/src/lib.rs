#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Desugaring Pass: Surface AST → Core AST
//!
//! Transforms the rich surface syntax into the minimal core calculus that
//! the Coq formal proofs reason about. The key transformations:
//!
//! 1. **Data declarations** → collected into a [`DataRegistry`] that maps
//!    constructor names to their encoding as right-nested binary sums.
//!
//! 2. **`Construct(ctor, args)`** → chain of `inl`/`inr` wrapping the
//!    constructor's payload, based on the constructor's position.
//!
//! 3. **`Match(scrutinee, arms)`** → nested `case` expressions that peel
//!    off one `inl`/`inr` layer at each level.
//!
//! 4. **`SurfaceTy::Named(name, args)`** → resolved to the core `Ty`
//!    by substituting type parameters in the sum encoding.
//!
//! 5. **All other nodes** → structural recursion (pass-through).
//!
//! # Encoding scheme
//!
//! Data types are encoded as **right-nested binary sums**:
//!
//! ```text
//! data Color = Red | Green | Blue
//! ⟹ () + (() + ())
//!
//! Red   ⟹ inl(())
//! Green ⟹ inr(inl(()))
//! Blue  ⟹ inr(inr(()))
//!
//! match c of
//!   | Red => e1
//!   | Green => e2
//!   | Blue => e3
//! ⟹ case c of
//!      inl _ => e1
//!      | inr rest => case rest of
//!          inl _ => e2
//!          | inr _ => e3
//! ```
//!
//! For constructors with payloads:
//! ```text
//! data Option(a) = None | Some(a)
//! ⟹ () + a
//!
//! None    ⟹ inl(())
//! Some(x) ⟹ inr(x)
//! ```

use std::collections::HashMap;

use ephapax_surface::{
    ConstructorDef, DataDecl, MatchArm, Pattern, Span, SurfaceDecl, SurfaceExpr, SurfaceExprKind,
    SurfaceModule, SurfaceTy,
};
use ephapax_syntax::{BaseTy, Decl, Expr, ExprKind, Literal, Module, Ty, Visibility};
use smol_str::SmolStr;
use thiserror::Error;

/// Desugaring errors.
#[derive(Debug, Clone, Error)]
pub enum DesugarError {
    #[error("unknown constructor `{ctor}`")]
    UnknownConstructor { ctor: String },

    #[error("unknown type `{name}`")]
    UnknownType { name: String },

    #[error("type `{name}` expects {expected} arguments, got {got}")]
    TypeArityMismatch {
        name: String,
        expected: usize,
        got: usize,
    },

    #[error("constructor `{ctor}` expects {expected} arguments, got {got}")]
    ConstructorArityMismatch {
        ctor: String,
        expected: usize,
        got: usize,
    },

    #[error("non-exhaustive match: missing constructor `{ctor}`")]
    NonExhaustive { ctor: String },

    #[error("empty match expression")]
    EmptyMatch,
}

// =========================================================================
// Data Registry
// =========================================================================

/// Information about a single constructor within a data type.
#[derive(Debug, Clone)]
struct ConstructorInfo {
    /// Index of this constructor in the data declaration (0-based).
    index: usize,
    /// Total number of constructors in the data type.
    _total: usize,
    /// Payload types (empty for nullary constructors).
    fields: Vec<SurfaceTy>,
    /// The data type this constructor belongs to.
    data_name: SmolStr,
    /// Type parameters of the data type.
    _data_params: Vec<SmolStr>,
}

/// Registry of all data declarations encountered during desugaring.
///
/// Maps constructor names to their encoding information. This is built
/// from `DataDecl` nodes and used to desugar `Construct` and `Match`.
#[derive(Debug, Clone, Default)]
pub struct DataRegistry {
    /// Constructor name → info
    constructors: HashMap<SmolStr, ConstructorInfo>,
    /// Data type name → (params, constructors)
    types: HashMap<SmolStr, (Vec<SmolStr>, Vec<ConstructorDef>)>,
}

impl DataRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a data declaration.
    pub fn register(&mut self, decl: &DataDecl) {
        let total = decl.constructors.len();
        for (index, ctor) in decl.constructors.iter().enumerate() {
            self.constructors.insert(
                ctor.name.clone(),
                ConstructorInfo {
                    index,
                    _total: total,
                    fields: ctor.fields.clone(),
                    data_name: decl.name.clone(),
                    _data_params: decl.params.clone(),
                },
            );
        }
        self.types.insert(
            decl.name.clone(),
            (decl.params.clone(), decl.constructors.clone()),
        );
    }

    /// Look up a constructor by name.
    fn get_ctor(&self, name: &str) -> Option<&ConstructorInfo> {
        self.constructors.get(name)
    }

    /// Get the constructors for a data type (in order).
    fn get_type_ctors(&self, name: &str) -> Option<&(Vec<SmolStr>, Vec<ConstructorDef>)> {
        self.types.get(name)
    }
}

// =========================================================================
// Desugarer
// =========================================================================

/// The desugaring pass.
///
/// Call [`Desugarer::desugar_module`] to transform a complete surface module
/// into a core module. The desugarer collects data declarations into a
/// [`DataRegistry`] and uses it to transform `Construct` and `Match` nodes.
pub struct Desugarer {
    registry: DataRegistry,
}

impl Desugarer {
    /// Create a new desugarer with an empty data registry.
    pub fn new() -> Self {
        Self {
            registry: DataRegistry::new(),
        }
    }

    /// Create a new desugarer with a pre-populated registry.
    pub fn with_registry(registry: DataRegistry) -> Self {
        Self { registry }
    }

    /// Desugar a complete surface module to a core module.
    ///
    /// First pass: collect all data declarations into the registry.
    /// Second pass: desugar all declarations.
    pub fn desugar_module(&mut self, module: &SurfaceModule) -> Result<Module, DesugarError> {
        // First pass: register all data types
        for decl in &module.decls {
            if let SurfaceDecl::Data(data) = decl {
                self.registry.register(data);
            }
        }

        // Second pass: desugar declarations
        let mut core_decls = Vec::new();
        for decl in &module.decls {
            match decl {
                SurfaceDecl::Fn {
                    name,
                    params,
                    ret_ty,
                    body,
                } => {
                    let core_params: Vec<_> = params
                        .iter()
                        .map(|(n, t)| Ok((n.clone(), self.desugar_ty(t)?)))
                        .collect::<Result<_, DesugarError>>()?;
                    let core_ret = self.desugar_ty(ret_ty)?;
                    let core_body = self.desugar_expr(body)?;
                    core_decls.push(Decl::Fn {
                        name: name.clone(),
                        visibility: Visibility::Private,
                        type_params: vec![],
                        params: core_params,
                        ret_ty: core_ret,
                        body: core_body,
                    });
                }
                SurfaceDecl::Type { name, ty } => {
                    core_decls.push(Decl::Type {
                        name: name.clone(),
                        visibility: Visibility::Private,
                        ty: self.desugar_ty(ty)?,
                    });
                }
                // Data declarations are consumed by the registry, not emitted
                // as core declarations. The type information lives in the
                // registry and is used to desugar Construct/Match nodes.
                SurfaceDecl::Data(_) => {}
            }
        }

        Ok(Module {
            name: module.name.clone(),
            imports: vec![],
            decls: core_decls,
        })
    }

    /// Desugar a single expression.
    pub fn desugar_expr(&self, expr: &SurfaceExpr) -> Result<Expr, DesugarError> {
        let span = expr.span;
        let kind = match &expr.kind {
            // === Pass-through nodes (structural recursion) ===
            SurfaceExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
            SurfaceExprKind::Var(v) => ExprKind::Var(v.clone()),

            SurfaceExprKind::StringNew { region, value } => ExprKind::StringNew {
                region: region.clone(),
                value: value.clone(),
            },
            SurfaceExprKind::StringConcat { left, right } => ExprKind::StringConcat {
                left: Box::new(self.desugar_expr(left)?),
                right: Box::new(self.desugar_expr(right)?),
            },
            SurfaceExprKind::StringLen(inner) => {
                ExprKind::StringLen(Box::new(self.desugar_expr(inner)?))
            }

            SurfaceExprKind::Let {
                name,
                ty,
                value,
                body,
            } => ExprKind::Let {
                name: name.clone(),
                ty: ty.as_ref().map(|t| self.desugar_ty(t)).transpose()?,
                value: Box::new(self.desugar_expr(value)?),
                body: Box::new(self.desugar_expr(body)?),
            },

            SurfaceExprKind::LetLin {
                name,
                ty,
                value,
                body,
            } => ExprKind::LetLin {
                name: name.clone(),
                ty: ty.as_ref().map(|t| self.desugar_ty(t)).transpose()?,
                value: Box::new(self.desugar_expr(value)?),
                body: Box::new(self.desugar_expr(body)?),
            },

            SurfaceExprKind::Lambda {
                param,
                param_ty,
                body,
            } => ExprKind::Lambda {
                param: param.clone(),
                param_ty: self.desugar_ty(param_ty)?,
                body: Box::new(self.desugar_expr(body)?),
            },

            SurfaceExprKind::App { func, arg } => ExprKind::App {
                func: Box::new(self.desugar_expr(func)?),
                arg: Box::new(self.desugar_expr(arg)?),
            },

            SurfaceExprKind::Pair { left, right } => ExprKind::Pair {
                left: Box::new(self.desugar_expr(left)?),
                right: Box::new(self.desugar_expr(right)?),
            },
            SurfaceExprKind::Fst(inner) => ExprKind::Fst(Box::new(self.desugar_expr(inner)?)),
            SurfaceExprKind::Snd(inner) => ExprKind::Snd(Box::new(self.desugar_expr(inner)?)),

            SurfaceExprKind::Inl { ty, value } => ExprKind::Inl {
                ty: self.desugar_ty(ty)?,
                value: Box::new(self.desugar_expr(value)?),
            },
            SurfaceExprKind::Inr { ty, value } => ExprKind::Inr {
                ty: self.desugar_ty(ty)?,
                value: Box::new(self.desugar_expr(value)?),
            },

            SurfaceExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => ExprKind::Case {
                scrutinee: Box::new(self.desugar_expr(scrutinee)?),
                left_var: left_var.clone(),
                left_body: Box::new(self.desugar_expr(left_body)?),
                right_var: right_var.clone(),
                right_body: Box::new(self.desugar_expr(right_body)?),
            },

            SurfaceExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => ExprKind::If {
                cond: Box::new(self.desugar_expr(cond)?),
                then_branch: Box::new(self.desugar_expr(then_branch)?),
                else_branch: Box::new(self.desugar_expr(else_branch)?),
            },

            SurfaceExprKind::Region { name, body } => ExprKind::Region {
                name: name.clone(),
                body: Box::new(self.desugar_expr(body)?),
            },

            SurfaceExprKind::Borrow(inner) => ExprKind::Borrow(Box::new(self.desugar_expr(inner)?)),
            SurfaceExprKind::Deref(inner) => ExprKind::Deref(Box::new(self.desugar_expr(inner)?)),
            SurfaceExprKind::Drop(inner) => ExprKind::Drop(Box::new(self.desugar_expr(inner)?)),
            SurfaceExprKind::Copy(inner) => ExprKind::Copy(Box::new(self.desugar_expr(inner)?)),

            SurfaceExprKind::Block(exprs) => {
                let desugared: Vec<_> = exprs
                    .iter()
                    .map(|e| self.desugar_expr(e))
                    .collect::<Result<_, _>>()?;
                ExprKind::Block(desugared)
            }

            SurfaceExprKind::FFI { symbol, args } => {
                let desugared_args: Vec<_> = args
                    .iter()
                    .map(|a| self.desugar_expr(a))
                    .collect::<Result<_, _>>()?;
                ExprKind::FFI {
                    symbol: symbol.clone(),
                    args: desugared_args,
                }
            }

            SurfaceExprKind::BinOp { op, left, right } => ExprKind::BinOp {
                op: *op,
                left: Box::new(self.desugar_expr(left)?),
                right: Box::new(self.desugar_expr(right)?),
            },
            SurfaceExprKind::UnaryOp { op, operand } => ExprKind::UnaryOp {
                op: *op,
                operand: Box::new(self.desugar_expr(operand)?),
            },

            SurfaceExprKind::ListLit(elements) => {
                let desugared: Vec<_> = elements
                    .iter()
                    .map(|e| self.desugar_expr(e))
                    .collect::<Result<_, _>>()?;
                ExprKind::ListLit(desugared)
            }
            SurfaceExprKind::ListIndex { list, index } => ExprKind::ListIndex {
                list: Box::new(self.desugar_expr(list)?),
                index: Box::new(self.desugar_expr(index)?),
            },
            SurfaceExprKind::TupleLit(elements) => {
                let desugared: Vec<_> = elements
                    .iter()
                    .map(|e| self.desugar_expr(e))
                    .collect::<Result<_, _>>()?;
                ExprKind::TupleLit(desugared)
            }
            SurfaceExprKind::TupleIndex { tuple, index } => ExprKind::TupleIndex {
                tuple: Box::new(self.desugar_expr(tuple)?),
                index: *index,
            },

            // === Surface-only nodes (real desugaring) ===
            SurfaceExprKind::Construct { ctor, args } => {
                return self.desugar_construct(ctor, args, span);
            }

            SurfaceExprKind::Match { scrutinee, arms } => {
                return self.desugar_match(scrutinee, arms, span);
            }
        };

        Ok(Expr::new(kind, span))
    }

    // =====================================================================
    // Type desugaring
    // =====================================================================

    /// Desugar a surface type to a core type.
    pub fn desugar_ty(&self, ty: &SurfaceTy) -> Result<Ty, DesugarError> {
        match ty {
            SurfaceTy::Base(b) => Ok(Ty::Base(*b)),
            SurfaceTy::String(r) => Ok(Ty::String(r.clone())),
            SurfaceTy::Ref { linearity, inner } => Ok(Ty::Ref {
                linearity: *linearity,
                inner: Box::new(self.desugar_ty(inner)?),
            }),
            SurfaceTy::Fun { param, ret } => Ok(Ty::Fun {
                param: Box::new(self.desugar_ty(param)?),
                ret: Box::new(self.desugar_ty(ret)?),
            }),
            SurfaceTy::Prod { left, right } => Ok(Ty::Prod {
                left: Box::new(self.desugar_ty(left)?),
                right: Box::new(self.desugar_ty(right)?),
            }),
            SurfaceTy::Sum { left, right } => Ok(Ty::Sum {
                left: Box::new(self.desugar_ty(left)?),
                right: Box::new(self.desugar_ty(right)?),
            }),
            SurfaceTy::Region { name, inner } => Ok(Ty::Region {
                name: name.clone(),
                inner: Box::new(self.desugar_ty(inner)?),
            }),
            SurfaceTy::Borrow(inner) => Ok(Ty::Borrow(Box::new(self.desugar_ty(inner)?))),
            SurfaceTy::Var(v) => Ok(Ty::Var(v.clone())),
            SurfaceTy::List(inner) => Ok(Ty::List(Box::new(self.desugar_ty(inner)?))),
            SurfaceTy::Tuple(elements) => {
                let desugared: Vec<_> = elements
                    .iter()
                    .map(|t| self.desugar_ty(t))
                    .collect::<Result<_, _>>()?;
                Ok(Ty::Tuple(desugared))
            }

            // Named type application: resolve from registry
            SurfaceTy::Named { name, args } => self.desugar_named_type(name, args),
        }
    }

    /// Desugar a named type application to the core sum encoding.
    ///
    /// `Option(I32)` → `() + I32`
    /// `Result(I32, Bool)` → `I32 + Bool`
    fn desugar_named_type(&self, name: &SmolStr, args: &[SurfaceTy]) -> Result<Ty, DesugarError> {
        let (params, ctors) = self.registry.get_type_ctors(name.as_str()).ok_or_else(|| {
            DesugarError::UnknownType {
                name: name.to_string(),
            }
        })?;

        if params.len() != args.len() {
            return Err(DesugarError::TypeArityMismatch {
                name: name.to_string(),
                expected: params.len(),
                got: args.len(),
            });
        }

        // Build substitution map: type param → concrete type
        let subst: HashMap<&SmolStr, &SurfaceTy> = params.iter().zip(args.iter()).collect();

        // Build right-nested sum from constructor field types
        self.build_sum_type(&ctors.clone(), &subst)
    }

    /// Build the right-nested binary sum type for a list of constructors.
    ///
    /// `[A, B, C]` → `A + (B + C)`
    /// Each constructor's payload becomes its summand:
    /// - Nullary: `()`
    /// - Single field: the field type
    /// - Multiple fields: product of field types
    fn build_sum_type(
        &self,
        ctors: &[ConstructorDef],
        subst: &HashMap<&SmolStr, &SurfaceTy>,
    ) -> Result<Ty, DesugarError> {
        assert!(
            !ctors.is_empty(),
            "data type must have at least one constructor"
        );

        if ctors.len() == 1 {
            return self.build_payload_type(&ctors[0].fields, subst);
        }

        let left = self.build_payload_type(&ctors[0].fields, subst)?;
        let right = self.build_sum_type(&ctors[1..], subst)?;

        Ok(Ty::Sum {
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    /// Build the type for a single constructor's payload.
    ///
    /// - No fields → `()`
    /// - One field → the field type
    /// - Multiple fields → right-nested product
    fn build_payload_type(
        &self,
        fields: &[SurfaceTy],
        subst: &HashMap<&SmolStr, &SurfaceTy>,
    ) -> Result<Ty, DesugarError> {
        match fields.len() {
            0 => Ok(Ty::Base(BaseTy::Unit)),
            1 => self.subst_and_desugar_ty(&fields[0], subst),
            _ => {
                let first = self.subst_and_desugar_ty(&fields[0], subst)?;
                let rest_fields = &fields[1..];
                let rest = self.build_payload_type(rest_fields, subst)?;
                Ok(Ty::Prod {
                    left: Box::new(first),
                    right: Box::new(rest),
                })
            }
        }
    }

    /// Apply type parameter substitution then desugar.
    fn subst_and_desugar_ty(
        &self,
        ty: &SurfaceTy,
        subst: &HashMap<&SmolStr, &SurfaceTy>,
    ) -> Result<Ty, DesugarError> {
        match ty {
            SurfaceTy::Var(v) => {
                if let Some(replacement) = subst.get(v) {
                    self.desugar_ty(replacement)
                } else {
                    Ok(Ty::Var(v.clone()))
                }
            }
            other => self.desugar_ty(other),
        }
    }

    // =====================================================================
    // Constructor desugaring
    // =====================================================================

    /// Desugar `Construct(ctor, args)` → chain of `inl`/`inr`.
    ///
    /// For constructor at index `i` out of `n` total:
    /// - Index 0: `inl(payload)`
    /// - Index 1: `inr(inl(payload))`
    /// - Index k: `inr(inr(...inr(inl(payload))...))`  (k layers of inr)
    /// - Last index (n-1): `inr(inr(...inr(payload)...))` (n-1 layers of inr, no inl)
    fn desugar_construct(
        &self,
        ctor: &SmolStr,
        args: &[SurfaceExpr],
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let info = self
            .registry
            .get_ctor(ctor.as_str())
            .ok_or_else(|| DesugarError::UnknownConstructor {
                ctor: ctor.to_string(),
            })?
            .clone();

        if info.fields.len() != args.len() {
            return Err(DesugarError::ConstructorArityMismatch {
                ctor: ctor.to_string(),
                expected: info.fields.len(),
                got: args.len(),
            });
        }

        // Build the payload expression
        let payload = self.build_payload_expr(args, span)?;

        // Get the full sum type for the "other side" annotations
        let empty_subst: HashMap<&SmolStr, &SurfaceTy> = HashMap::new();
        let (_, ctors) = self
            .registry
            .get_type_ctors(info.data_name.as_str())
            .unwrap();
        let ctors = ctors.clone();

        // Wrap in inl/inr chain based on index
        self.wrap_injection(payload, info.index, &ctors, &empty_subst, span)
    }

    /// Build the payload expression for a constructor application.
    ///
    /// - No args → `()`
    /// - One arg → the arg itself
    /// - Multiple args → right-nested pair
    fn build_payload_expr(&self, args: &[SurfaceExpr], span: Span) -> Result<Expr, DesugarError> {
        match args.len() {
            0 => Ok(Expr::new(ExprKind::Lit(Literal::Unit), span)),
            1 => self.desugar_expr(&args[0]),
            _ => {
                let first = self.desugar_expr(&args[0])?;
                let rest = self.build_payload_expr(&args[1..], span)?;
                Ok(Expr::new(
                    ExprKind::Pair {
                        left: Box::new(first),
                        right: Box::new(rest),
                    },
                    span,
                ))
            }
        }
    }

    /// Wrap a payload in the appropriate chain of inl/inr.
    fn wrap_injection(
        &self,
        payload: Expr,
        index: usize,
        ctors: &[ConstructorDef],
        subst: &HashMap<&SmolStr, &SurfaceTy>,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let total = ctors.len();

        if total == 1 {
            // Single constructor — no injection needed
            return Ok(payload);
        }

        if index == 0 {
            // First constructor: inl(payload)
            // The "right" type is the sum of remaining constructors
            let right_ty = self.build_sum_type(&ctors[1..], subst)?;
            Ok(Expr::new(
                ExprKind::Inl {
                    ty: right_ty,
                    value: Box::new(payload),
                },
                span,
            ))
        } else if index == total - 1 {
            // Last constructor: inr(inr(...inr(payload)...))
            // Need (total - 1) layers of inr, but we do it recursively
            let left_ty = self.build_payload_type(&ctors[0].fields, subst)?;
            let inner = self.wrap_injection(payload, index - 1, &ctors[1..], subst, span)?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty: left_ty,
                    value: Box::new(inner),
                },
                span,
            ))
        } else {
            // Middle constructor: inr(... inl(payload) ...)
            let left_ty = self.build_payload_type(&ctors[0].fields, subst)?;
            let inner = self.wrap_injection(payload, index - 1, &ctors[1..], subst, span)?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty: left_ty,
                    value: Box::new(inner),
                },
                span,
            ))
        }
    }

    // =====================================================================
    // Match desugaring
    // =====================================================================

    /// Desugar `Match(scrutinee, arms)` → nested `case` expressions.
    ///
    /// The strategy: determine which data type is being matched (from the
    /// first constructor pattern), then generate a nested case tree that
    /// peels off one inl/inr layer at each level.
    fn desugar_match(
        &self,
        scrutinee: &SurfaceExpr,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<Expr, DesugarError> {
        if arms.is_empty() {
            return Err(DesugarError::EmptyMatch);
        }

        let core_scrutinee = self.desugar_expr(scrutinee)?;

        // Find the data type from constructor patterns
        let data_name = self.find_data_type_from_arms(arms)?;

        let (_, ctors) = self.registry.get_type_ctors(data_name.as_str()).unwrap();
        let ctors = ctors.clone();

        // Build an ordered map: constructor index → (pattern bindings, body)
        let mut arm_map: HashMap<usize, &MatchArm> = HashMap::new();
        let mut wildcard_arm: Option<&MatchArm> = None;

        for arm in arms {
            match &arm.pattern {
                Pattern::Constructor { ctor, .. } => {
                    let info = self.registry.get_ctor(ctor.as_str()).ok_or_else(|| {
                        DesugarError::UnknownConstructor {
                            ctor: ctor.to_string(),
                        }
                    })?;
                    arm_map.insert(info.index, arm);
                }
                Pattern::Wildcard | Pattern::Var(_) => {
                    wildcard_arm = Some(arm);
                }
                _ => {
                    // Literal or tuple patterns at top level of match on ADT —
                    // treat as wildcard for now
                    wildcard_arm = Some(arm);
                }
            }
        }

        // Generate the nested case tree
        self.build_case_tree(&core_scrutinee, &ctors, &arm_map, wildcard_arm, 0, span)
    }

    /// Find which data type is being matched by examining constructor patterns.
    fn find_data_type_from_arms(&self, arms: &[MatchArm]) -> Result<SmolStr, DesugarError> {
        for arm in arms {
            if let Pattern::Constructor { ctor, .. } = &arm.pattern {
                if let Some(info) = self.registry.get_ctor(ctor.as_str()) {
                    return Ok(info.data_name.clone());
                } else {
                    return Err(DesugarError::UnknownConstructor {
                        ctor: ctor.to_string(),
                    });
                }
            }
        }
        // No constructor patterns found — all wildcards/vars
        // This is valid but we can't determine the type. Return a placeholder.
        // In practice, the type checker will resolve this.
        Err(DesugarError::EmptyMatch)
    }

    /// Build the nested case tree for a match expression.
    ///
    /// For constructors `[A, B, C]`, generates:
    /// ```text
    /// case scrutinee of
    ///   inl a_payload => <arm for A>
    ///   | inr rest => case rest of
    ///       inl b_payload => <arm for B>
    ///       | inr c_payload => <arm for C>
    /// ```
    fn build_case_tree(
        &self,
        scrutinee: &Expr,
        ctors: &[ConstructorDef],
        arm_map: &HashMap<usize, &MatchArm>,
        wildcard: Option<&MatchArm>,
        base_index: usize,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        match ctors.len() {
            0 => unreachable!("empty constructor list"),

            // Last (or only) constructor — no case needed, just bind
            1 => {
                let arm = arm_map
                    .get(&base_index)
                    .or(wildcard.as_ref())
                    .ok_or_else(|| DesugarError::NonExhaustive {
                        ctor: ctors[0].name.to_string(),
                    })?;

                self.build_arm_body(scrutinee, &ctors[0], arm, span)
            }

            // Two or more constructors — generate case
            _ => {
                let left_arm = arm_map
                    .get(&base_index)
                    .or(wildcard.as_ref())
                    .ok_or_else(|| DesugarError::NonExhaustive {
                        ctor: ctors[0].name.to_string(),
                    })?;

                // Variable name for the left (inl) payload
                let left_var = self.fresh_var_for_arm(left_arm, &ctors[0]);
                let left_body = self.build_arm_body_inner(
                    &Expr::new(ExprKind::Var(left_var.clone()), span),
                    &ctors[0],
                    left_arm,
                    span,
                )?;

                // Variable name for the right (inr) — the "rest" of the sum
                let rest_var: SmolStr = format!("__rest_{}", base_index).into();
                let rest_scrutinee = Expr::new(ExprKind::Var(rest_var.clone()), span);
                let right_body = self.build_case_tree(
                    &rest_scrutinee,
                    &ctors[1..],
                    arm_map,
                    wildcard,
                    base_index + 1,
                    span,
                )?;

                Ok(Expr::new(
                    ExprKind::Case {
                        scrutinee: Box::new(scrutinee.clone()),
                        left_var,
                        left_body: Box::new(left_body),
                        right_var: rest_var,
                        right_body: Box::new(right_body),
                    },
                    span,
                ))
            }
        }
    }

    /// Build the body for a match arm (single constructor, no more case needed).
    fn build_arm_body(
        &self,
        scrutinee: &Expr,
        ctor: &ConstructorDef,
        arm: &MatchArm,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        // For the last constructor, scrutinee IS the payload (no inl/inr wrapper)
        self.build_arm_body_inner(scrutinee, ctor, arm, span)
    }

    /// Build the arm body, binding pattern variables to the payload.
    fn build_arm_body_inner(
        &self,
        payload_expr: &Expr,
        ctor: &ConstructorDef,
        arm: &MatchArm,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let body = self.desugar_expr(&arm.body)?;

        match &arm.pattern {
            Pattern::Constructor { args, .. } => {
                // Bind constructor arguments from the payload
                self.bind_pattern_vars(payload_expr, args, &ctor.fields, body, span)
            }
            Pattern::Wildcard => Ok(body),
            Pattern::Var(v) => {
                // Bind the whole payload to the variable
                Ok(Expr::new(
                    ExprKind::Let {
                        name: v.clone(),
                        ty: None,
                        value: Box::new(payload_expr.clone()),
                        body: Box::new(body),
                    },
                    span,
                ))
            }
            _ => Ok(body),
        }
    }

    /// Bind pattern variables from a constructor's payload.
    ///
    /// For `Some(x)` with payload `p`: `let x = p in body`
    /// For `Pair(a, b)` with payload `p`: `let a = p.0 in let b = p.1 in body`
    fn bind_pattern_vars(
        &self,
        payload: &Expr,
        patterns: &[Pattern],
        _fields: &[SurfaceTy],
        body: Expr,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        match patterns.len() {
            0 => Ok(body),
            1 => self.bind_single_pattern(payload, &patterns[0], body, span),
            _ => {
                // Multiple fields: payload is a right-nested product
                // Extract with fst/snd
                let mut result = body;
                for i in (0..patterns.len()).rev() {
                    let field_expr = if patterns.len() == 2 {
                        if i == 0 {
                            Expr::new(ExprKind::Fst(Box::new(payload.clone())), span)
                        } else {
                            Expr::new(ExprKind::Snd(Box::new(payload.clone())), span)
                        }
                    } else if i == 0 {
                        // First field: fst
                        Expr::new(ExprKind::Fst(Box::new(payload.clone())), span)
                    } else if i == patterns.len() - 1 {
                        // Last field: snd of snd of ... snd
                        let mut access = payload.clone();
                        for _ in 0..i {
                            access = Expr::new(ExprKind::Snd(Box::new(access)), span);
                        }
                        access
                    } else {
                        // Middle field: fst of (snd^i payload)
                        let mut access = payload.clone();
                        for _ in 0..i {
                            access = Expr::new(ExprKind::Snd(Box::new(access)), span);
                        }
                        Expr::new(ExprKind::Fst(Box::new(access)), span)
                    };

                    result = self.bind_single_pattern(&field_expr, &patterns[i], result, span)?;
                }
                Ok(result)
            }
        }
    }

    /// Bind a single pattern variable.
    fn bind_single_pattern(
        &self,
        value: &Expr,
        pattern: &Pattern,
        body: Expr,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        match pattern {
            Pattern::Var(v) => Ok(Expr::new(
                ExprKind::Let {
                    name: v.clone(),
                    ty: None,
                    value: Box::new(value.clone()),
                    body: Box::new(body),
                },
                span,
            )),
            Pattern::Wildcard => Ok(body),
            Pattern::Unit => Ok(body),
            Pattern::Pair(l, r) => {
                let fst = Expr::new(ExprKind::Fst(Box::new(value.clone())), span);
                let snd = Expr::new(ExprKind::Snd(Box::new(value.clone())), span);
                let inner = self.bind_single_pattern(&snd, r, body, span)?;
                self.bind_single_pattern(&fst, l, inner, span)
            }
            Pattern::Tuple(elements) => {
                let as_fields: Vec<SurfaceTy> = vec![]; // placeholder
                self.bind_pattern_vars(value, elements, &as_fields, body, span)
            }
            Pattern::Constructor { .. } => {
                // Nested constructor pattern — would need recursive match desugaring.
                // For now, bind the whole thing and let the user destructure.
                // This is a known limitation that can be extended later.
                Ok(body)
            }
            Pattern::Literal(_) => {
                // Literal patterns need equality checks — not yet implemented.
                // For ADT matching, this shouldn't arise at the constructor level.
                Ok(body)
            }
        }
    }

    /// Generate a fresh variable name for a match arm's payload binding.
    fn fresh_var_for_arm(&self, arm: &MatchArm, ctor: &ConstructorDef) -> SmolStr {
        match &arm.pattern {
            Pattern::Constructor { args, .. } if args.len() == 1 => {
                // Single-field constructor: use the pattern variable if it's a Var
                if let Pattern::Var(v) = &args[0] {
                    return v.clone();
                }
                format!("__{}", ctor.name.to_lowercase()).into()
            }
            Pattern::Var(v) => v.clone(),
            _ => format!("__{}", ctor.name.to_lowercase()).into(),
        }
    }
}

impl Default for Desugarer {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Convenience functions
// =========================================================================

/// Desugar a surface module to a core module.
pub fn desugar(module: &SurfaceModule) -> Result<Module, DesugarError> {
    let mut desugarer = Desugarer::new();
    desugarer.desugar_module(module)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_surface::{
        BaseTy, ConstructorDef, DataDecl, Literal, MatchArm, Pattern, Span, SurfaceDecl,
        SurfaceExpr, SurfaceExprKind, SurfaceModule, SurfaceTy,
    };

    fn se(kind: SurfaceExprKind) -> SurfaceExpr {
        SurfaceExpr::dummy(kind)
    }

    fn option_decl() -> DataDecl {
        DataDecl {
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
        }
    }

    fn color_decl() -> DataDecl {
        DataDecl {
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
        }
    }

    // --- Type desugaring ---

    #[test]
    fn desugar_option_i32() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let ty = SurfaceTy::Named {
            name: "Option".into(),
            args: vec![SurfaceTy::Base(BaseTy::I32)],
        };

        let core = ds.desugar_ty(&ty).unwrap();
        // Option(I32) = () + I32
        assert_eq!(
            core,
            Ty::Sum {
                left: Box::new(Ty::Base(BaseTy::Unit)),
                right: Box::new(Ty::Base(BaseTy::I32)),
            }
        );
    }

    #[test]
    fn desugar_color_type() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let ty = SurfaceTy::Named {
            name: "Color".into(),
            args: vec![],
        };

        let core = ds.desugar_ty(&ty).unwrap();
        // Color = () + (() + ())
        assert_eq!(
            core,
            Ty::Sum {
                left: Box::new(Ty::Base(BaseTy::Unit)),
                right: Box::new(Ty::Sum {
                    left: Box::new(Ty::Base(BaseTy::Unit)),
                    right: Box::new(Ty::Base(BaseTy::Unit)),
                }),
            }
        );
    }

    #[test]
    fn desugar_type_arity_mismatch() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let ty = SurfaceTy::Named {
            name: "Option".into(),
            args: vec![], // Missing type argument
        };

        assert!(ds.desugar_ty(&ty).is_err());
    }

    // --- Constructor desugaring ---

    #[test]
    fn desugar_none_constructor() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let expr = se(SurfaceExprKind::Construct {
            ctor: "None".into(),
            args: vec![],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // None → inl(())
        assert!(matches!(core.kind, ExprKind::Inl { .. }));
    }

    #[test]
    fn desugar_some_constructor() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let expr = se(SurfaceExprKind::Construct {
            ctor: "Some".into(),
            args: vec![se(SurfaceExprKind::Lit(Literal::I32(42)))],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Some(42) → inr(42)
        assert!(matches!(core.kind, ExprKind::Inr { .. }));
    }

    #[test]
    fn desugar_color_green() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let expr = se(SurfaceExprKind::Construct {
            ctor: "Green".into(),
            args: vec![],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Green → inr(inl(()))
        if let ExprKind::Inr { value, .. } = &core.kind {
            assert!(matches!(value.kind, ExprKind::Inl { .. }));
        } else {
            panic!("expected inr");
        }
    }

    #[test]
    fn desugar_color_blue() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let expr = se(SurfaceExprKind::Construct {
            ctor: "Blue".into(),
            args: vec![],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Blue → inr(inr(()))
        if let ExprKind::Inr { value, .. } = &core.kind {
            if let ExprKind::Inr { .. } = &value.kind {
                // Correct: inr(inr(...))
            } else {
                panic!("expected inr(inr(...)), got inr({:?})", value.kind);
            }
        } else {
            panic!("expected inr");
        }
    }

    #[test]
    fn desugar_unknown_constructor() {
        let ds = Desugarer::new();
        let expr = se(SurfaceExprKind::Construct {
            ctor: "Foo".into(),
            args: vec![],
        });
        assert!(ds.desugar_expr(&expr).is_err());
    }

    #[test]
    fn desugar_constructor_arity_mismatch() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let expr = se(SurfaceExprKind::Construct {
            ctor: "None".into(),
            args: vec![se(SurfaceExprKind::Lit(Literal::I32(1)))], // None takes 0 args
        });
        assert!(ds.desugar_expr(&expr).is_err());
    }

    // --- Match desugaring ---

    #[test]
    fn desugar_match_option() {
        let mut ds = Desugarer::new();
        ds.registry.register(&option_decl());

        let expr = se(SurfaceExprKind::Match {
            scrutinee: Box::new(se(SurfaceExprKind::Var("x".into()))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(0))),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Some".into(),
                        args: vec![Pattern::Var("v".into())],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Var("v".into())),
                },
            ],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Should produce a case expression
        assert!(matches!(core.kind, ExprKind::Case { .. }));
    }

    #[test]
    fn desugar_match_color() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let expr = se(SurfaceExprKind::Match {
            scrutinee: Box::new(se(SurfaceExprKind::Var("c".into()))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Red".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(1))),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Green".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(2))),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Blue".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(3))),
                },
            ],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Should produce nested case: case c of inl _ => 1 | inr rest => case rest of ...
        if let ExprKind::Case { right_body, .. } = &core.kind {
            assert!(
                matches!(right_body.kind, ExprKind::Case { .. }),
                "3-variant match should produce nested case"
            );
        } else {
            panic!("expected Case");
        }
    }

    #[test]
    fn desugar_match_with_wildcard() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let expr = se(SurfaceExprKind::Match {
            scrutinee: Box::new(se(SurfaceExprKind::Var("c".into()))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Red".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(1))),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(0))),
                },
            ],
        });

        let core = ds.desugar_expr(&expr).unwrap();
        // Wildcard should fill in the missing Green and Blue arms
        assert!(matches!(core.kind, ExprKind::Case { .. }));
    }

    #[test]
    fn desugar_non_exhaustive_match() {
        let mut ds = Desugarer::new();
        ds.registry.register(&color_decl());

        let expr = se(SurfaceExprKind::Match {
            scrutinee: Box::new(se(SurfaceExprKind::Var("c".into()))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        ctor: "Red".into(),
                        args: vec![],
                    },
                    guard: None,
                    body: se(SurfaceExprKind::Lit(Literal::I32(1))),
                },
                // Missing Green and Blue, no wildcard
            ],
        });

        assert!(
            ds.desugar_expr(&expr).is_err(),
            "non-exhaustive match should be rejected"
        );
    }

    // --- Module desugaring ---

    #[test]
    fn desugar_module_with_data() {
        let module = SurfaceModule {
            name: "test".into(),
            decls: vec![
                SurfaceDecl::Data(option_decl()),
                SurfaceDecl::Fn {
                    name: "unwrap_or".into(),
                    params: vec![
                        (
                            "opt".into(),
                            SurfaceTy::Named {
                                name: "Option".into(),
                                args: vec![SurfaceTy::Base(BaseTy::I32)],
                            },
                        ),
                        ("default".into(), SurfaceTy::Base(BaseTy::I32)),
                    ],
                    ret_ty: SurfaceTy::Base(BaseTy::I32),
                    body: se(SurfaceExprKind::Match {
                        scrutinee: Box::new(se(SurfaceExprKind::Var("opt".into()))),
                        arms: vec![
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    ctor: "None".into(),
                                    args: vec![],
                                },
                                guard: None,
                                body: se(SurfaceExprKind::Var("default".into())),
                            },
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    ctor: "Some".into(),
                                    args: vec![Pattern::Var("v".into())],
                                },
                                guard: None,
                                body: se(SurfaceExprKind::Var("v".into())),
                            },
                        ],
                    }),
                },
            ],
        };

        let core = desugar(&module).unwrap();
        // Data declaration should not appear in core
        assert_eq!(
            core.decls.len(),
            1,
            "data decl should be consumed, only fn remains"
        );
        // Function should have sum type parameter
        if let Decl::Fn { params, .. } = &core.decls[0] {
            assert_eq!(
                params[0].1,
                Ty::Sum {
                    left: Box::new(Ty::Base(BaseTy::Unit)),
                    right: Box::new(Ty::Base(BaseTy::I32)),
                }
            );
        }
    }

    // --- Integration: parse → desugar → type check ---

    #[test]
    fn integration_desugar_typecheck_no_parser() {
        use ephapax_typing::type_check_module;

        // Build surface AST directly, skip parser
        let module = SurfaceModule {
            name: "test".into(),
            decls: vec![
                SurfaceDecl::Data(DataDecl {
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
                }),
                SurfaceDecl::Fn {
                    name: "test".into(),
                    params: vec![(
                        "opt".into(),
                        SurfaceTy::Named {
                            name: "Option".into(),
                            args: vec![SurfaceTy::Base(BaseTy::I32)],
                        },
                    )],
                    ret_ty: SurfaceTy::Base(BaseTy::I32),
                    body: SurfaceExpr::dummy(SurfaceExprKind::Match {
                        scrutinee: Box::new(SurfaceExpr::dummy(SurfaceExprKind::Var("opt".into()))),
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
                    }),
                },
            ],
        };

        let core = desugar(&module).unwrap();
        assert_eq!(core.decls.len(), 1);

        let result = type_check_module(&core);
        assert!(result.is_ok(), "type check should pass: {:?}", result.err());
    }

    #[test]
    fn integration_match_desugar_debug() {
        // Debug: check what the desugarer produces for a match
        let module = SurfaceModule {
            name: "test".into(),
            decls: vec![
                SurfaceDecl::Data(DataDecl {
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
                }),
                SurfaceDecl::Fn {
                    name: "test".into(),
                    params: vec![(
                        "opt".into(),
                        SurfaceTy::Named {
                            name: "Option".into(),
                            args: vec![SurfaceTy::Base(BaseTy::I32)],
                        },
                    )],
                    ret_ty: SurfaceTy::Base(BaseTy::I32),
                    body: SurfaceExpr::dummy(SurfaceExprKind::Match {
                        scrutinee: Box::new(SurfaceExpr::dummy(SurfaceExprKind::Var("opt".into()))),
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
                    }),
                },
            ],
        };

        let core = desugar(&module).unwrap();

        // Print desugared core for debugging
        assert_eq!(core.decls.len(), 1);
        if let Decl::Fn { body, .. } = &core.decls[0] {
            // Should be a Case expression
            if let ExprKind::Case {
                left_body,
                right_body,
                left_var,
                right_var,
                ..
            } = &body.kind
            {
                // Left body (None arm) should just be I32(0)
                assert!(
                    matches!(left_body.kind, ExprKind::Lit(Literal::I32(0))),
                    "None arm should be literal 0, got: {:?}",
                    left_body.kind
                );
                // Right body (Some arm) should be: let v = right_var in v
                // Actually since fresh_var_for_arm returns "v" for Some(v),
                // the right_var IS "v" and the body should just reference it
                // Verify structure
                let _ = (left_var, right_var);
            } else {
                panic!("expected Case, got: {:?}", body.kind);
            }
        }
    }
}
