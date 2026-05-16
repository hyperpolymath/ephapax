#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell

//! Ephapax Type Checker (Dyadic Design)
//!
//! Implements the dyadic type system where BOTH qualifiers coexist per-program:
//! - **`let` (affine)**: Values used ≤1 time (can be dropped implicitly)
//! - **`let!` (linear)**: Values used exactly 1 time (must be consumed)
//!
//! The dyadic property is per-binding, not a global mode. `let!` always means
//! exactly-once — there is no flag to weaken it. This matches the formal
//! semantics in Typing.v and the Orthogonality Lemma in RegionLinear.idr.
//!
//! Based on formal/Typing.v
//!
//! See [`discipline`] module for the complete rules reference.

pub mod discipline;

use ephapax_syntax::{
    BaseTy, BinOp, Decl, Expr, ExprKind, ExternItem, Literal, MatchArm, Module, Pattern,
    RegionName, Span, Ty, UnaryOp, Var, Visibility,
};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::fmt;
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

    #[error("Value of type {ty:?} escapes region `{region}`")]
    RegionEscape { region: RegionName, ty: Ty },

    #[error("Linear variable `{var}` in region `{region}` not consumed before region exit")]
    RegionLinearNotConsumed { var: Var, region: RegionName },

    #[error("String literal must be allocated with String.new@region(\"...\")")]
    UnallocatedStringLiteral,

    #[error("Type annotation mismatch: declared {declared:?}, but value has type {actual:?}")]
    AnnotationMismatch { declared: Ty, actual: Ty },

    #[error("Not yet supported in the core type checker: {0}. Use the surface (parse_surface_module → desugar) path instead.")]
    NotYetSupportedInCore(&'static str),

    #[error("Unknown constructor `{0}`")]
    UnknownConstructor(Var),

    #[error("Constructor `{ctor}` expects {expected} field(s), pattern has {got}")]
    ConstructorArityMismatch {
        ctor: Var,
        expected: usize,
        got: usize,
    },

    #[error("Duplicate constructor `{0}` in module")]
    DuplicateConstructor(Var),

    #[error("Non-exhaustive match: missing pattern for `{missing}`")]
    NonExhaustiveMatch { missing: SmolStr },

    #[error("Match expression must have at least one arm")]
    EmptyMatch,
}

/// A type error with source location.
///
/// Wraps a [`TypeError`] with the [`Span`] of the expression that caused it,
/// so the LSP and CLI can report the precise location.
#[derive(Debug, Clone, PartialEq)]
pub struct SpannedTypeError {
    /// The underlying type error.
    pub error: TypeError,
    /// Source location of the expression that caused the error.
    pub span: Span,
}

impl fmt::Display for SpannedTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl std::error::Error for SpannedTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

/// How a binding was introduced — determines the substructural discipline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingForm {
    /// `let x = ...` — affine discipline: use at most once, implicit drop OK.
    Let,
    /// `let! x = ...` — linear discipline: use exactly once, no implicit drop.
    LetBang,
    /// Function parameter — linear discipline if type is linear, affine otherwise.
    Param,
}

/// Typing context entry
#[derive(Debug, Clone)]
struct CtxEntry {
    ty: Ty,
    used: bool,
    /// How this binding was introduced — `let` (affine) vs `let!` (linear).
    binding_form: BindingForm,
    /// Which region this variable was bound in (None = top-level / no region).
    region: Option<RegionName>,
}

impl CtxEntry {
    /// Whether this binding demands exactly-once consumption.
    fn demands_consumption(&self) -> bool {
        match self.binding_form {
            BindingForm::LetBang => true,
            BindingForm::Let => false,
            BindingForm::Param => self.ty.is_linear(),
        }
    }
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

    /// Extend context with new binding, tagged with the current region and binding form.
    pub fn extend(&mut self, name: Var, ty: Ty, binding_form: BindingForm) {
        let region = self.regions.last().cloned();
        self.vars.insert(
            name,
            CtxEntry {
                ty,
                used: false,
                binding_form,
                region,
            },
        );
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

    /// Check all bindings that demand consumption have been consumed.
    pub fn check_all_consumed(&self) -> Result<(), TypeError> {
        for (name, entry) in &self.vars {
            if entry.demands_consumption() && !entry.used {
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
    pub fn snapshot(&self) -> Self {
        self.clone()
    }

    /// Check that two contexts agree on linear variable usage.
    pub fn check_branch_agreement(&self, other: &Context) -> Result<(), TypeError> {
        for (name, entry) in &self.vars {
            if !entry.demands_consumption() {
                continue;
            }

            match other.vars.get(name) {
                Some(other_entry) => {
                    if entry.used != other_entry.used {
                        return Err(TypeError::BranchLinearityMismatchDetailed {
                            var: name.clone(),
                            then_status: if entry.used {
                                "consumed"
                            } else {
                                "not consumed"
                            },
                            else_status: if other_entry.used {
                                "consumed"
                            } else {
                                "not consumed"
                            },
                        });
                    }
                }
                None => {
                    return Err(TypeError::BranchLinearityMismatch);
                }
            }
        }

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
    pub fn merge_branches(&mut self, _other: &Context) {
        // After branch agreement is verified, the usage should be identical.
    }
}

/// Information about a single constructor in a `data` declaration.
///
/// Constructed by [`DataCtorRegistry::populate_from_module`] from each
/// `Decl::Data`. Used by [`TypeChecker::check_pattern`] to resolve
/// `Pattern::Constructor` and build the binary-sum encoding that mirrors
/// `ephapax_desugar::build_sum_type`.
#[derive(Debug, Clone)]
pub struct CtorInfo {
    /// Name of the parent data type (e.g. `"Option"` for `Some`/`None`).
    pub parent: SmolStr,
    /// Type parameters of the parent data type (in declaration order).
    pub type_params: Vec<SmolStr>,
    /// 0-based position of this constructor in the parent's declaration.
    /// Defines the inl/inr nesting depth used by the binary-sum encoding.
    pub position: usize,
    /// Total number of constructors in the parent data type.
    pub total: usize,
    /// Field types in declaration order. Type parameters appear as
    /// `Ty::Var(name)` and are substituted with fresh unifs per use site.
    pub fields: Vec<Ty>,
}

/// Information about a `data` declaration.
#[derive(Debug, Clone)]
pub struct DataInfo {
    /// Name of the data type.
    pub name: SmolStr,
    /// Type parameters (e.g. `[a]` for `Option(a)`).
    pub type_params: Vec<SmolStr>,
    /// Constructor names in declaration order. Defines positions and
    /// the exhaustiveness coverage set.
    pub ctor_names: Vec<SmolStr>,
}

/// Registry mapping constructor → parent and data type → constructors.
///
/// Populated from `Decl::Data` declarations in the module pre-pass
/// before any function body is checked. Used by `check_match` to resolve
/// `Pattern::Constructor` to the right-nested binary-sum encoding that
/// `ephapax-desugar` would produce for surface code.
#[derive(Debug, Clone, Default)]
pub struct DataCtorRegistry {
    ctors: HashMap<SmolStr, CtorInfo>,
    types: HashMap<SmolStr, DataInfo>,
}

impl DataCtorRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_ctor(&self, name: &str) -> Option<&CtorInfo> {
        self.ctors.get(name)
    }

    pub fn get_type(&self, name: &str) -> Option<&DataInfo> {
        self.types.get(name)
    }

    /// Register every `Decl::Data` in `module`. Duplicate constructor
    /// names across the module are rejected.
    pub fn populate_from_module(&mut self, module: &Module) -> Result<(), TypeError> {
        for decl in &module.decls {
            if let Decl::Data {
                name,
                type_params,
                constructors,
            } = decl
            {
                let parent: SmolStr = name.as_str().into();
                let total = constructors.len();
                let mut ctor_names = Vec::with_capacity(total);
                for (position, ctor) in constructors.iter().enumerate() {
                    let ctor_name: SmolStr = ctor.name.as_str().into();
                    if self.ctors.contains_key(&ctor_name) {
                        return Err(TypeError::DuplicateConstructor(ctor_name));
                    }
                    self.ctors.insert(
                        ctor_name.clone(),
                        CtorInfo {
                            parent: parent.clone(),
                            type_params: type_params.clone(),
                            position,
                            total,
                            fields: ctor.fields.clone(),
                        },
                    );
                    ctor_names.push(ctor_name);
                }
                self.types.insert(
                    parent.clone(),
                    DataInfo {
                        name: parent,
                        type_params: type_params.clone(),
                        ctor_names,
                    },
                );
            }
        }
        Ok(())
    }
}

/// Substitute multiple type variables at once. Equivalent to chaining
/// `Ty::subst_var` over the substitution map but avoids the O(N·|ty|)
/// repeated traversal — useful when payload types reference several
/// type parameters of the parent data type at once.
fn subst_tys(ty: &Ty, subst: &HashMap<SmolStr, Ty>) -> Ty {
    match ty {
        Ty::Var(v) => subst.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Base(_) | Ty::Unif(_) => ty.clone(),
        Ty::String(_) => ty.clone(),
        Ty::Ref { linearity, inner } => Ty::Ref {
            linearity: *linearity,
            inner: Box::new(subst_tys(inner, subst)),
        },
        Ty::Fun { param, ret } => Ty::Fun {
            param: Box::new(subst_tys(param, subst)),
            ret: Box::new(subst_tys(ret, subst)),
        },
        Ty::Prod { left, right } => Ty::Prod {
            left: Box::new(subst_tys(left, subst)),
            right: Box::new(subst_tys(right, subst)),
        },
        Ty::Sum { left, right } => Ty::Sum {
            left: Box::new(subst_tys(left, subst)),
            right: Box::new(subst_tys(right, subst)),
        },
        Ty::Region { name, inner } => Ty::Region {
            name: name.clone(),
            inner: Box::new(subst_tys(inner, subst)),
        },
        Ty::Borrow(inner) => Ty::Borrow(Box::new(subst_tys(inner, subst))),
        Ty::ForAll { var, body } => {
            if subst.contains_key(var) {
                ty.clone() // shadowed by binder
            } else {
                Ty::ForAll {
                    var: var.clone(),
                    body: Box::new(subst_tys(body, subst)),
                }
            }
        }
        Ty::Effectful {
            param,
            ret,
            effects,
        } => Ty::Effectful {
            param: Box::new(subst_tys(param, subst)),
            ret: Box::new(subst_tys(ret, subst)),
            effects: effects.clone(),
        },
        Ty::List(inner) => Ty::List(Box::new(subst_tys(inner, subst))),
        Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| subst_tys(t, subst)).collect()),
    }
}

/// Build the payload type for a constructor's fields under a substitution.
/// Mirrors `ephapax_desugar::build_payload_type`:
/// - 0 fields → `Unit`
/// - 1 field  → the field's substituted type
/// - N fields → right-nested `Prod`
fn build_payload_ty(fields: &[Ty], subst: &HashMap<SmolStr, Ty>) -> Ty {
    match fields.len() {
        0 => Ty::Base(BaseTy::Unit),
        1 => subst_tys(&fields[0], subst),
        _ => Ty::Prod {
            left: Box::new(subst_tys(&fields[0], subst)),
            right: Box::new(build_payload_ty(&fields[1..], subst)),
        },
    }
}

/// Build the right-nested binary sum of payloads. Mirrors
/// `ephapax_desugar::build_sum_type`: a single-constructor data type
/// has no `Sum` wrapper (its encoding is just the payload).
fn right_nested_sum(payloads: &[Ty]) -> Ty {
    debug_assert!(
        !payloads.is_empty(),
        "data type must have at least one constructor"
    );
    if payloads.len() == 1 {
        payloads[0].clone()
    } else {
        Ty::Sum {
            left: Box::new(payloads[0].clone()),
            right: Box::new(right_nested_sum(&payloads[1..])),
        }
    }
}

// ---------------------------------------------------------------------------
// Maranget-style usefulness for `check_exhaustiveness`.
//
// We model each match as a 1-column pattern matrix and ask: is the row `[_]`
// useful with respect to the matrix? A "yes" witness is a missing case
// (non-exhaustive); a "no" answer means every value is covered.
//
// Specialization grows the column count (one constructor with N args yields
// N sub-columns); default reduction shrinks it. We recover the column's
// nominal data type from the first non-wildcard pattern actually used in
// that column, since `Ty` itself carries no nominal info in this codebase.
// ---------------------------------------------------------------------------

/// Constructor identifier for the usefulness algorithm.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Tag {
    Bool(bool),
    Unit,
    Pair,
    Tuple(usize),
    Data(SmolStr),
    LitI32(i32),
    LitI64(i64),
    /// Float literals compared by bit pattern (NaN matches itself by bits).
    LitF32(u32),
    LitF64(u64),
}

/// A reconstructed pattern showing a missing case.
#[derive(Clone, Debug)]
enum Witness {
    Wildcard,
    Unit,
    Bool(bool),
    Pair(Box<Witness>, Box<Witness>),
    Tuple(Vec<Witness>),
    Ctor { name: SmolStr, args: Vec<Witness> },
    LitI32(i32),
    LitI64(i64),
    LitF32(f32),
    LitF64(f64),
}

fn pretty_witness(w: &Witness) -> String {
    match w {
        Witness::Wildcard => "_".to_string(),
        Witness::Unit => "()".to_string(),
        Witness::Bool(b) => b.to_string(),
        Witness::Pair(a, b) => format!("({}, {})", pretty_witness(a), pretty_witness(b)),
        Witness::Tuple(parts) => {
            let inner: Vec<String> = parts.iter().map(pretty_witness).collect();
            format!("({})", inner.join(", "))
        }
        Witness::Ctor { name, args } => {
            if args.is_empty() {
                name.to_string()
            } else {
                let inner: Vec<String> = args.iter().map(pretty_witness).collect();
                format!("{}({})", name, inner.join(", "))
            }
        }
        Witness::LitI32(n) => n.to_string(),
        Witness::LitI64(n) => n.to_string(),
        Witness::LitF32(f) => f.to_string(),
        Witness::LitF64(f) => f.to_string(),
    }
}

fn reconstruct_witness(tag: &Tag, args: Vec<Witness>) -> Witness {
    match tag {
        Tag::Bool(b) => Witness::Bool(*b),
        Tag::Unit => Witness::Unit,
        Tag::Pair => Witness::Pair(Box::new(args[0].clone()), Box::new(args[1].clone())),
        Tag::Tuple(_) => Witness::Tuple(args),
        Tag::Data(name) => Witness::Ctor {
            name: name.clone(),
            args,
        },
        Tag::LitI32(n) => Witness::LitI32(*n),
        Tag::LitI64(n) => Witness::LitI64(*n),
        Tag::LitF32(bits) => Witness::LitF32(f32::from_bits(*bits)),
        Tag::LitF64(bits) => Witness::LitF64(f64::from_bits(*bits)),
    }
}

fn tag_of_pattern(p: &Pattern) -> Option<Tag> {
    match p {
        Pattern::Wildcard | Pattern::Var(_) => None,
        Pattern::Unit => Some(Tag::Unit),
        Pattern::Pair(_, _) => Some(Tag::Pair),
        Pattern::Tuple(parts) => Some(Tag::Tuple(parts.len())),
        Pattern::Constructor { ctor, .. } => Some(Tag::Data(ctor.clone())),
        Pattern::Literal(Literal::Unit) => Some(Tag::Unit),
        Pattern::Literal(Literal::Bool(b)) => Some(Tag::Bool(*b)),
        Pattern::Literal(Literal::I32(n)) => Some(Tag::LitI32(*n)),
        Pattern::Literal(Literal::I64(n)) => Some(Tag::LitI64(*n)),
        Pattern::Literal(Literal::F32(f)) => Some(Tag::LitF32(f.to_bits())),
        Pattern::Literal(Literal::F64(f)) => Some(Tag::LitF64(f.to_bits())),
        // Unallocated string literals are rejected earlier; treat as no tag.
        Pattern::Literal(Literal::String(_)) => None,
    }
}

fn pattern_matches_tag(p: &Pattern, tag: &Tag) -> bool {
    match (p, tag) {
        (Pattern::Wildcard | Pattern::Var(_), _) => true,
        (Pattern::Unit | Pattern::Literal(Literal::Unit), Tag::Unit) => true,
        (Pattern::Literal(Literal::Bool(a)), Tag::Bool(b)) => a == b,
        (Pattern::Literal(Literal::I32(a)), Tag::LitI32(b)) => a == b,
        (Pattern::Literal(Literal::I64(a)), Tag::LitI64(b)) => a == b,
        (Pattern::Literal(Literal::F32(a)), Tag::LitF32(b)) => a.to_bits() == *b,
        (Pattern::Literal(Literal::F64(a)), Tag::LitF64(b)) => a.to_bits() == *b,
        (Pattern::Pair(_, _), Tag::Pair) => true,
        (Pattern::Tuple(parts), Tag::Tuple(n)) => parts.len() == *n,
        (Pattern::Constructor { ctor, .. }, Tag::Data(name)) => ctor == name,
        _ => false,
    }
}

/// Sub-patterns exposed when a row's head matches `tag`. Wildcard/Var
/// expand to `arity` wildcards; concrete patterns return their args.
fn sub_patterns_for(p: &Pattern, arity: usize) -> Vec<Pattern> {
    match p {
        Pattern::Wildcard | Pattern::Var(_) => vec![Pattern::Wildcard; arity],
        Pattern::Pair(a, b) => vec![(**a).clone(), (**b).clone()],
        Pattern::Tuple(parts) => parts.clone(),
        Pattern::Constructor { args, .. } => args.clone(),
        _ => Vec::new(),
    }
}

/// Specialize the matrix on `tag` with the given constructor arity.
/// Keeps rows whose head matches the tag and any row whose head is a
/// wildcard/var (expanded into `arity` wildcards).
fn specialize_matrix(
    matrix: &[Vec<Pattern>],
    tag: &Tag,
    arity: usize,
) -> Vec<Vec<Pattern>> {
    let mut out = Vec::with_capacity(matrix.len());
    for row in matrix {
        let head = &row[0];
        if !pattern_matches_tag(head, tag) {
            continue;
        }
        let mut new_row = sub_patterns_for(head, arity);
        new_row.extend(row[1..].iter().cloned());
        out.push(new_row);
    }
    out
}

/// Default matrix: rows whose head pattern is a wildcard/var, with the
/// head column dropped. Concrete-headed rows are discarded.
fn default_matrix(matrix: &[Vec<Pattern>]) -> Vec<Vec<Pattern>> {
    let mut out = Vec::new();
    for row in matrix {
        if matches!(&row[0], Pattern::Wildcard | Pattern::Var(_)) {
            out.push(row[1..].to_vec());
        }
    }
    out
}

/// Recovered nominal/structural type of column 0.
#[derive(Clone, Debug)]
enum ColTy {
    Bool,
    Unit,
    Pair,
    Tuple(usize),
    /// Any constructor name — we look up its parent in the registry to
    /// enumerate the data type's full constructor list.
    Data(SmolStr),
    Other,
}

fn column_type(matrix: &[Vec<Pattern>]) -> ColTy {
    for row in matrix {
        match &row[0] {
            Pattern::Wildcard | Pattern::Var(_) => continue,
            Pattern::Unit => return ColTy::Unit,
            Pattern::Literal(Literal::Unit) => return ColTy::Unit,
            Pattern::Literal(Literal::Bool(_)) => return ColTy::Bool,
            Pattern::Pair(_, _) => return ColTy::Pair,
            Pattern::Tuple(parts) => return ColTy::Tuple(parts.len()),
            Pattern::Constructor { ctor, .. } => return ColTy::Data(ctor.clone()),
            Pattern::Literal(_) => return ColTy::Other,
        }
    }
    ColTy::Other
}

/// If `col` has a finite signature, return `(Tag, arity)` for each
/// constructor in declaration order. Returns `None` for infinite
/// domains (integers, floats, opaque types).
fn complete_signature(
    col: &ColTy,
    registry: &DataCtorRegistry,
) -> Option<Vec<(Tag, usize)>> {
    match col {
        ColTy::Bool => Some(vec![(Tag::Bool(false), 0), (Tag::Bool(true), 0)]),
        ColTy::Unit => Some(vec![(Tag::Unit, 0)]),
        ColTy::Pair => Some(vec![(Tag::Pair, 2)]),
        ColTy::Tuple(n) => Some(vec![(Tag::Tuple(*n), *n)]),
        ColTy::Data(any_ctor) => {
            let ci = registry.get_ctor(any_ctor.as_str())?;
            let di = registry.get_type(ci.parent.as_str())?;
            let mut sigs = Vec::with_capacity(di.ctor_names.len());
            for cname in &di.ctor_names {
                let arity = registry.get_ctor(cname.as_str())?.fields.len();
                sigs.push((Tag::Data(cname.clone()), arity));
            }
            Some(sigs)
        }
        ColTy::Other => None,
    }
}

/// Compute whether the row `[_; num_cols]` is useful with respect to
/// `matrix`. Returns a witness pattern (as a Vec of `num_cols`
/// `Witness` values) when useful, `None` when the matrix already
/// covers every value.
fn is_useful(
    matrix: &[Vec<Pattern>],
    num_cols: usize,
    registry: &DataCtorRegistry,
) -> Option<Vec<Witness>> {
    if num_cols == 0 {
        return if matrix.is_empty() {
            Some(Vec::new())
        } else {
            None
        };
    }

    let col = column_type(matrix);
    let mut used_tags: HashSet<Tag> = HashSet::new();
    for row in matrix {
        if let Some(tag) = tag_of_pattern(&row[0]) {
            used_tags.insert(tag);
        }
    }

    if let Some(sig) = complete_signature(&col, registry) {
        let all_present = sig.iter().all(|(t, _)| used_tags.contains(t));
        if all_present {
            for (tag, arity) in &sig {
                let sub_matrix = specialize_matrix(matrix, tag, *arity);
                let sub_cols = arity + (num_cols - 1);
                if let Some(witness) = is_useful(&sub_matrix, sub_cols, registry) {
                    let head_args = witness[..*arity].to_vec();
                    let tail = witness[*arity..].to_vec();
                    let mut out = Vec::with_capacity(num_cols);
                    out.push(reconstruct_witness(tag, head_args));
                    out.extend(tail);
                    return Some(out);
                }
            }
            None
        } else {
            let (missing_tag, missing_arity) = sig
                .iter()
                .find(|(t, _)| !used_tags.contains(t))
                .expect("not all_present implies a missing tag");
            let default = default_matrix(matrix);
            if let Some(tail_witness) = is_useful(&default, num_cols - 1, registry) {
                let head = reconstruct_witness(
                    missing_tag,
                    vec![Witness::Wildcard; *missing_arity],
                );
                let mut out = Vec::with_capacity(num_cols);
                out.push(head);
                out.extend(tail_witness);
                return Some(out);
            }
            None
        }
    } else {
        let default = default_matrix(matrix);
        if let Some(tail_witness) = is_useful(&default, num_cols - 1, registry) {
            let mut out = Vec::with_capacity(num_cols);
            out.push(Witness::Wildcard);
            out.extend(tail_witness);
            return Some(out);
        }
        None
    }
}

/// Type checker state
pub struct TypeChecker {
    ctx: Context,
    /// Next fresh unification variable ID.
    next_unif: u32,
    /// Solved unification variables: id -> type.
    unif_solutions: HashMap<u32, Ty>,
    /// Data declarations visible to the current module.
    /// Populated by `type_check_module_inner` from `Decl::Data` decls
    /// before any function body is checked.
    data_registry: DataCtorRegistry,
}

impl TypeChecker {
    /// Create a new type checker.
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
            next_unif: 0,
            unif_solutions: HashMap::new(),
            data_registry: DataCtorRegistry::new(),
        }
    }

    /// Access the data-constructor registry — useful for tests and
    /// downstream tooling that wants to inspect resolved constructor
    /// positions without re-walking `Decl::Data`.
    pub fn data_registry(&self) -> &DataCtorRegistry {
        &self.data_registry
    }

    /// Construct a SpannedTypeError at the given span.
    fn at(&self, span: Span, error: TypeError) -> SpannedTypeError {
        SpannedTypeError { error, span }
    }

    /// Generate a fresh unification variable.
    fn fresh_unif(&mut self) -> Ty {
        let id = self.next_unif;
        self.next_unif += 1;
        Ty::Unif(id)
    }

    /// Instantiate a ForAll type by replacing bound variables with fresh
    /// unification variables. Non-ForAll types pass through unchanged.
    fn instantiate(&mut self, ty: Ty) -> Ty {
        match ty {
            Ty::ForAll { var, body } => {
                let fresh = self.fresh_unif();
                let instantiated = body.subst_var(&var, &fresh);
                self.instantiate(instantiated)
            }
            other => other,
        }
    }

    /// Resolve a type by chasing unification variable solutions.
    fn resolve(&self, ty: &Ty) -> Ty {
        ty.resolve(&self.unif_solutions)
    }

    /// Unify two types. On success, updates unification solutions.
    /// On failure, returns a TypeMismatch error at the given span.
    fn unify(&mut self, s: Span, a: &Ty, b: &Ty) -> Result<(), SpannedTypeError> {
        let a = self.resolve(a);
        let b = self.resolve(b);

        match (&a, &b) {
            // Same structure — trivially equal
            _ if a == b => Ok(()),

            // Unification variable cases
            (Ty::Unif(id), _) => {
                if b.contains_unif(*id) {
                    return Err(self.at(s, TypeError::TypeMismatch { expected: a, found: b }));
                }
                self.unif_solutions.insert(*id, b);
                Ok(())
            }
            (_, Ty::Unif(id)) => {
                if a.contains_unif(*id) {
                    return Err(self.at(s, TypeError::TypeMismatch { expected: a, found: b }));
                }
                self.unif_solutions.insert(*id, a);
                Ok(())
            }

            // Structural cases
            (Ty::Fun { param: p1, ret: r1 }, Ty::Fun { param: p2, ret: r2 }) => {
                self.unify(s, p1, p2)?;
                self.unify(s, r1, r2)
            }
            (Ty::Prod { left: l1, right: r1 }, Ty::Prod { left: l2, right: r2 }) => {
                self.unify(s, l1, l2)?;
                self.unify(s, r1, r2)
            }
            (Ty::Sum { left: l1, right: r1 }, Ty::Sum { left: l2, right: r2 }) => {
                self.unify(s, l1, l2)?;
                self.unify(s, r1, r2)
            }
            (Ty::Ref { linearity: l1, inner: i1 }, Ty::Ref { linearity: l2, inner: i2 })
                if l1 == l2 =>
            {
                self.unify(s, i1, i2)
            }
            (Ty::Region { name: n1, inner: i1 }, Ty::Region { name: n2, inner: i2 })
                if n1 == n2 =>
            {
                self.unify(s, i1, i2)
            }
            (Ty::Borrow(i1), Ty::Borrow(i2)) => self.unify(s, i1, i2),
            (Ty::List(i1), Ty::List(i2)) => self.unify(s, i1, i2),
            (Ty::Tuple(e1), Ty::Tuple(e2)) if e1.len() == e2.len() => {
                for (t1, t2) in e1.iter().zip(e2.iter()) {
                    self.unify(s, t1, t2)?;
                }
                Ok(())
            }

            // Mismatch
            _ => Err(self.at(s, TypeError::TypeMismatch { expected: a, found: b })),
        }
    }

    /// Type check an expression.
    ///
    /// Errors from sub-expression checks carry the sub-expression's span
    /// (most precise). Errors originating at THIS level carry this
    /// expression's span.
    pub fn check(&mut self, expr: &Expr) -> Result<Ty, SpannedTypeError> {
        let s = expr.span;
        match &expr.kind {
            ExprKind::Lit(lit) => self.check_lit(s, lit),
            ExprKind::Var(name) => self.check_var(s, name),
            ExprKind::StringNew { region, .. } => self.check_string_new(s, region),
            ExprKind::StringConcat { left, right } => self.check_string_concat(s, left, right),
            ExprKind::Let {
                name,
                ty,
                value,
                body,
            } => self.check_let(s, name, ty.as_ref(), value, body),
            ExprKind::Lambda {
                param,
                param_ty,
                body,
            } => self.check_lambda(s, param, param_ty, body),
            ExprKind::App { func, arg } => self.check_app(s, func, arg),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.check_if(s, cond, then_branch, else_branch),
            ExprKind::Region { name, body } => self.check_region(s, name, body),
            ExprKind::Borrow(inner) => self.check_borrow(s, inner),
            ExprKind::Drop(inner) => self.check_drop(s, inner),
            ExprKind::Copy(inner) => self.check_copy(s, inner),
            ExprKind::StringLen(inner) => self.check_string_len(s, inner),
            ExprKind::LetLin {
                name,
                ty,
                value,
                body,
            } => self.check_let_lin(s, name, ty.as_ref(), value, body),
            ExprKind::Pair { left, right } => self.check_pair(left, right),
            ExprKind::Fst(inner) => self.check_fst(s, inner),
            ExprKind::Snd(inner) => self.check_snd(s, inner),
            ExprKind::Inl { ty, value } => self.check_inl(s, ty, value),
            ExprKind::Inr { ty, value } => self.check_inr(s, ty, value),
            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => self.check_case(s, scrutinee, left_var, left_body, right_var, right_body),
            ExprKind::Deref(inner) => self.check_deref(s, inner),
            ExprKind::Block(exprs) => self.check_block(s, exprs),
            ExprKind::BinOp { op, left, right } => self.check_binop(s, *op, left, right),
            ExprKind::UnaryOp { op, operand } => self.check_unaryop(s, *op, operand),
            ExprKind::ListLit(elements) => self.check_list_lit(s, elements),
            ExprKind::ListIndex { list, index } => self.check_list_index(s, list, index),
            ExprKind::TupleLit(elements) => self.check_tuple_lit(s, elements),
            ExprKind::TupleIndex { tuple, index } => self.check_tuple_index(s, tuple, *index),
            ExprKind::FFI { args, .. } => self.check_ffi(s, args),
            ExprKind::Perform { op, args } => self.check_perform(s, op, args),
            ExprKind::Handle { body, clauses } => self.check_handle(s, body, clauses),
            ExprKind::Match { scrutinee, arms } => self.check_match(s, scrutinee, arms),
        }
    }

    fn check_lit(&self, s: Span, lit: &Literal) -> Result<Ty, SpannedTypeError> {
        Ok(match lit {
            Literal::Unit => Ty::Base(BaseTy::Unit),
            Literal::Bool(_) => Ty::Base(BaseTy::Bool),
            Literal::I32(_) => Ty::Base(BaseTy::I32),
            Literal::I64(_) => Ty::Base(BaseTy::I64),
            Literal::F32(_) => Ty::Base(BaseTy::F32),
            Literal::F64(_) => Ty::Base(BaseTy::F64),
            Literal::String(_) => {
                return Err(self.at(s, TypeError::UnallocatedStringLiteral));
            }
        })
    }

    fn check_var(&mut self, s: Span, name: &Var) -> Result<Ty, SpannedTypeError> {
        let ty = self
            .ctx
            .lookup(name)
            .ok_or_else(|| self.at(s, TypeError::UnboundVariable(name.clone())))?
            .clone();

        self.ctx.mark_used(name).map_err(|e| self.at(s, e))?;

        // Instantiate ForAll types with fresh unification variables.
        // E.g. `identity : forall T. T -> T` becomes `?0 -> ?0`.
        Ok(self.instantiate(ty))
    }

    fn check_string_new(&self, s: Span, region: &RegionName) -> Result<Ty, SpannedTypeError> {
        // The wildcard region name `_` is implicitly active everywhere —
        // it stands for the global / data-section pool that holds bare
        // string literals lowered by desugar. Other named regions still
        // require a surrounding `region r { ... }` block.
        if region.as_str() != "_" && !self.ctx.region_active(region) {
            return Err(self.at(s, TypeError::InactiveRegion(region.clone())));
        }
        Ok(Ty::String(region.clone()))
    }

    fn check_string_concat(
        &mut self,
        s: Span,
        left: &Expr,
        right: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        match (&left_ty, &right_ty) {
            (Ty::String(r1), Ty::String(r2)) if r1 == r2 => Ok(Ty::String(r1.clone())),
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: left_ty,
                    found: right_ty,
                },
            )),
        }
    }

    fn check_let(
        &mut self,
        s: Span,
        name: &Var,
        ty_ann: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let value_ty = self.check(value)?;

        if let Some(declared) = ty_ann {
            self.unify(s, declared, &value_ty).map_err(|_| {
                self.at(
                    s,
                    TypeError::AnnotationMismatch {
                        declared: declared.clone(),
                        actual: self.resolve(&value_ty),
                    },
                )
            })?;
        }

        let resolved_ty = if ty_ann.is_some() {
            self.resolve(&value_ty)
        } else {
            value_ty
        };

        self.ctx
            .extend(name.clone(), resolved_ty, BindingForm::Let);
        let body_ty = self.check(body)?;

        // `let` is AFFINE — unconsumed bindings are allowed (implicit drop).
        Ok(body_ty)
    }

    fn check_lambda(
        &mut self,
        s: Span,
        param: &Var,
        param_ty: &Ty,
        body: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        self.ctx
            .extend(param.clone(), param_ty.clone(), BindingForm::Param);
        let body_ty = self.check(body)?;

        if let Some(entry) = self.ctx.vars.get(param) {
            if entry.demands_consumption() && !entry.used {
                return Err(self.at(
                    s,
                    TypeError::LinearVariableNotConsumed(param.clone()),
                ));
            }
        }

        Ok(Ty::Fun {
            param: Box::new(param_ty.clone()),
            ret: Box::new(body_ty),
        })
    }

    fn check_app(
        &mut self,
        s: Span,
        func: &Expr,
        arg: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let func_ty = self.check(func)?;
        let arg_ty = self.check(arg)?;

        // Resolve func_ty in case it's a unification variable
        let func_ty = self.resolve(&func_ty);

        match func_ty {
            Ty::Fun { param, ret } => {
                self.unify(s, &param, &arg_ty)?;
                Ok(self.resolve(&ret))
            }
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Fun {
                        param: Box::new(arg_ty.clone()),
                        ret: Box::new(Ty::Base(BaseTy::Unit)),
                    },
                    found: func_ty,
                },
            )),
        }
    }

    fn check_if(
        &mut self,
        s: Span,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let cond_ty = self.check(cond)?;

        if cond_ty != Ty::Base(BaseTy::Bool) {
            return Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Base(BaseTy::Bool),
                    found: cond_ty,
                },
            ));
        }

        let ctx_after_cond = self.ctx.snapshot();

        let then_ty = self.check(then_branch)?;
        let ctx_after_then = self.ctx.snapshot();

        self.ctx = ctx_after_cond;

        let else_ty = self.check(else_branch)?;
        let ctx_after_else = self.ctx.snapshot();

        self.unify(s, &then_ty, &else_ty)?;

        ctx_after_then
            .check_branch_agreement(&ctx_after_else)
            .map_err(|e| self.at(s, e))?;

        self.ctx = ctx_after_then;

        Ok(self.resolve(&then_ty))
    }

    /// Type check a region block: `region r: { body }`
    ///
    /// Implements the region-linear fusion rules:
    /// 1. **NoRegionInType**: Return type must NOT reference region `r`.
    /// 2. **AllLinearsConsumed**: Linear variables bound in `r` must be consumed.
    /// 3. **Region Safety**: After exit, region is no longer active.
    fn check_region(
        &mut self,
        s: Span,
        name: &RegionName,
        body: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        self.ctx.enter_region(name.clone());

        let body_ty = self.check(body)?;

        // Rule 1: NoRegionInType
        if body_ty.references_region(name) {
            self.ctx.exit_region();
            return Err(self.at(
                s,
                TypeError::RegionEscape {
                    region: name.clone(),
                    ty: body_ty,
                },
            ));
        }

        // Rule 2: AllLinearsConsumed
        for (var_name, entry) in &self.ctx.vars {
            if entry.region.as_ref() != Some(name) {
                continue;
            }
            if entry.demands_consumption() && !entry.used {
                let var = var_name.clone();
                let region = name.clone();
                self.ctx.exit_region();
                return Err(self.at(s, TypeError::RegionLinearNotConsumed { var, region }));
            }
        }

        // Rule 3: Region Safety
        self.ctx.exit_region();

        Ok(body_ty)
    }

    fn check_borrow(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        match &inner.kind {
            ExprKind::Var(name) => {
                let ty = self
                    .ctx
                    .lookup(name)
                    .ok_or_else(|| self.at(s, TypeError::UnboundVariable(name.clone())))?
                    .clone();
                Ok(Ty::Borrow(Box::new(ty)))
            }
            _ => {
                let inner_ty = self.check(inner)?;
                Ok(Ty::Borrow(Box::new(inner_ty)))
            }
        }
    }

    fn check_drop(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        if !inner_ty.is_linear() {
            return Err(self.at(s, TypeError::UnnecessaryDrop));
        }

        Ok(Ty::Base(BaseTy::Unit))
    }

    fn check_copy(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        if inner_ty.is_linear() {
            return Err(self.at(s, TypeError::CannotCopyLinear(inner_ty)));
        }

        Ok(Ty::Prod {
            left: Box::new(inner_ty.clone()),
            right: Box::new(inner_ty),
        })
    }

    fn check_string_len(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::String(_) => Ok(Ty::Base(BaseTy::I32)),
            Ty::Borrow(ref boxed) => match boxed.as_ref() {
                Ty::String(_) => Ok(Ty::Base(BaseTy::I32)),
                _ => Err(self.at(
                    s,
                    TypeError::TypeMismatch {
                        expected: Ty::String("_".into()),
                        found: inner_ty,
                    },
                )),
            },
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::String("_".into()),
                    found: inner_ty,
                },
            )),
        }
    }

    fn check_let_lin(
        &mut self,
        s: Span,
        name: &Var,
        ty_ann: Option<&Ty>,
        value: &Expr,
        body: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let value_ty = self.check(value)?;

        if let Some(declared) = ty_ann {
            if *declared != value_ty {
                return Err(self.at(
                    s,
                    TypeError::AnnotationMismatch {
                        declared: declared.clone(),
                        actual: value_ty,
                    },
                ));
            }
        }

        self.ctx
            .extend(name.clone(), value_ty.clone(), BindingForm::LetBang);
        let body_ty = self.check(body)?;

        // let! bindings MUST be consumed — regardless of type.
        if let Some(entry) = self.ctx.vars.get(name) {
            if !entry.used {
                return Err(self.at(
                    s,
                    TypeError::LinearVariableNotConsumed(name.clone()),
                ));
            }
        }

        Ok(body_ty)
    }

    fn check_pair(&mut self, left: &Expr, right: &Expr) -> Result<Ty, SpannedTypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        Ok(Ty::Prod {
            left: Box::new(left_ty),
            right: Box::new(right_ty),
        })
    }

    fn check_fst(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Prod { left, right } => {
                if right.is_linear() {
                    return Err(self.at(
                        s,
                        TypeError::LinearVariableNotConsumed("_pair_snd".into()),
                    ));
                }
                Ok(*left)
            }
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Prod {
                        left: Box::new(Ty::Base(BaseTy::Unit)),
                        right: Box::new(Ty::Base(BaseTy::Unit)),
                    },
                    found: inner_ty,
                },
            )),
        }
    }

    fn check_snd(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Prod { left, right } => {
                if left.is_linear() {
                    return Err(self.at(
                        s,
                        TypeError::LinearVariableNotConsumed("_pair_fst".into()),
                    ));
                }
                Ok(*right)
            }
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Prod {
                        left: Box::new(Ty::Base(BaseTy::Unit)),
                        right: Box::new(Ty::Base(BaseTy::Unit)),
                    },
                    found: inner_ty,
                },
            )),
        }
    }

    fn check_inl(&mut self, _s: Span, ty: &Ty, value: &Expr) -> Result<Ty, SpannedTypeError> {
        let value_ty = self.check(value)?;

        Ok(Ty::Sum {
            left: Box::new(value_ty),
            right: Box::new(ty.clone()),
        })
    }

    fn check_inr(&mut self, _s: Span, ty: &Ty, value: &Expr) -> Result<Ty, SpannedTypeError> {
        let value_ty = self.check(value)?;

        Ok(Ty::Sum {
            left: Box::new(ty.clone()),
            right: Box::new(value_ty),
        })
    }

    fn check_case(
        &mut self,
        s: Span,
        scrutinee: &Expr,
        left_var: &Var,
        left_body: &Expr,
        right_var: &Var,
        right_body: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let scrutinee_ty = self.check(scrutinee)?;

        match scrutinee_ty {
            Ty::Sum { left, right } => {
                let ctx_after_scrutinee = self.ctx.snapshot();

                // Check left branch
                self.ctx
                    .extend(left_var.clone(), *left.clone(), BindingForm::Param);
                let left_result_ty = self.check(left_body)?;

                if let Some(entry) = self.ctx.vars.get(left_var) {
                    if entry.demands_consumption() && !entry.used {
                        return Err(self.at(
                            s,
                            TypeError::LinearVariableNotConsumed(left_var.clone()),
                        ));
                    }
                }

                let mut ctx_after_left = self.ctx.snapshot();
                ctx_after_left.vars.remove(left_var);

                // Check right branch
                self.ctx = ctx_after_scrutinee;

                self.ctx
                    .extend(right_var.clone(), *right.clone(), BindingForm::Param);
                let right_result_ty = self.check(right_body)?;

                if let Some(entry) = self.ctx.vars.get(right_var) {
                    if entry.demands_consumption() && !entry.used {
                        return Err(self.at(
                            s,
                            TypeError::LinearVariableNotConsumed(right_var.clone()),
                        ));
                    }
                }

                let mut ctx_after_right = self.ctx.snapshot();
                ctx_after_right.vars.remove(right_var);

                self.unify(s, &left_result_ty, &right_result_ty)?;

                ctx_after_left
                    .check_branch_agreement(&ctx_after_right)
                    .map_err(|e| self.at(s, e))?;

                self.ctx = ctx_after_left;

                Ok(self.resolve(&left_result_ty))
            }
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Sum {
                        left: Box::new(Ty::Base(BaseTy::Unit)),
                        right: Box::new(Ty::Base(BaseTy::Unit)),
                    },
                    found: scrutinee_ty,
                },
            )),
        }
    }

    /// Type check a core `ExprKind::Match`.
    ///
    /// Each arm is checked against a snapshot of the post-scrutinee
    /// context. Arm body types are unified pairwise so the whole
    /// expression has a single type. Pattern-bound variables are
    /// removed from the post-arm snapshot before branch agreement so
    /// arms that bind different names still agree on the rest of the
    /// linear environment (matching `check_case`'s convention).
    /// Exhaustiveness is checked after all arms pass.
    fn check_match(
        &mut self,
        s: Span,
        scrutinee: &Expr,
        arms: &[MatchArm],
    ) -> Result<Ty, SpannedTypeError> {
        if arms.is_empty() {
            return Err(self.at(s, TypeError::EmptyMatch));
        }

        let scrutinee_ty = self.check(scrutinee)?;
        let ctx_after_scrutinee = self.ctx.snapshot();

        let mut arm_result_ty: Option<Ty> = None;
        let mut first_post_ctx: Option<Context> = None;

        for arm in arms {
            self.ctx = ctx_after_scrutinee.clone();

            let bound = self.check_pattern(s, &arm.pattern, &scrutinee_ty)?;

            if arm.guard.is_some() {
                return Err(self.at(s, TypeError::NotYetSupportedInCore("match guards")));
            }

            let body_ty = self.check(&arm.body)?;

            for name in &bound {
                if let Some(entry) = self.ctx.vars.get(name) {
                    if entry.demands_consumption() && !entry.used {
                        return Err(self
                            .at(s, TypeError::LinearVariableNotConsumed(name.clone())));
                    }
                }
            }

            let mut ctx_after_arm = self.ctx.snapshot();
            for name in &bound {
                ctx_after_arm.vars.remove(name);
            }

            if let Some(prev_ty) = &arm_result_ty {
                self.unify(arm.body.span, prev_ty, &body_ty)?;
            }
            arm_result_ty = Some(body_ty);

            match &first_post_ctx {
                Some(first) => {
                    first
                        .check_branch_agreement(&ctx_after_arm)
                        .map_err(|e| self.at(s, e))?;
                }
                None => first_post_ctx = Some(ctx_after_arm),
            }
        }

        self.ctx = first_post_ctx.expect("at least one arm processed");

        self.check_exhaustiveness(s, arms, &scrutinee_ty)?;

        Ok(self.resolve(&arm_result_ty.expect("at least one arm produced a type")))
    }

    /// Type check a `Pattern` against an `expected_ty` and bind its
    /// variables in the current context. Returns the names bound by
    /// this pattern so `check_match` can scope them out for branch
    /// agreement and verify linear consumption.
    fn check_pattern(
        &mut self,
        s: Span,
        pattern: &Pattern,
        expected_ty: &Ty,
    ) -> Result<Vec<Var>, SpannedTypeError> {
        let expected = self.resolve(expected_ty);
        match pattern {
            Pattern::Wildcard => Ok(Vec::new()),
            Pattern::Var(name) => {
                self.ctx
                    .extend(name.clone(), expected, BindingForm::Param);
                Ok(vec![name.clone()])
            }
            Pattern::Literal(lit) => {
                let lit_ty = match lit {
                    Literal::Unit => Ty::Base(BaseTy::Unit),
                    Literal::Bool(_) => Ty::Base(BaseTy::Bool),
                    Literal::I32(_) => Ty::Base(BaseTy::I32),
                    Literal::I64(_) => Ty::Base(BaseTy::I64),
                    Literal::F32(_) => Ty::Base(BaseTy::F32),
                    Literal::F64(_) => Ty::Base(BaseTy::F64),
                    Literal::String(_) => {
                        return Err(self.at(s, TypeError::UnallocatedStringLiteral));
                    }
                };
                self.unify(s, &lit_ty, &expected)?;
                Ok(Vec::new())
            }
            Pattern::Unit => {
                self.unify(s, &Ty::Base(BaseTy::Unit), &expected)?;
                Ok(Vec::new())
            }
            Pattern::Pair(left, right) => {
                let lu = self.fresh_unif();
                let ru = self.fresh_unif();
                self.unify(
                    s,
                    &Ty::Prod {
                        left: Box::new(lu.clone()),
                        right: Box::new(ru.clone()),
                    },
                    &expected,
                )?;
                let mut bound = self.check_pattern(s, left, &lu)?;
                bound.extend(self.check_pattern(s, right, &ru)?);
                Ok(bound)
            }
            Pattern::Tuple(parts) => {
                let unifs: Vec<Ty> = (0..parts.len()).map(|_| self.fresh_unif()).collect();
                self.unify(s, &Ty::Tuple(unifs.clone()), &expected)?;
                let mut bound = Vec::new();
                for (p, u) in parts.iter().zip(unifs.iter()) {
                    bound.extend(self.check_pattern(s, p, u)?);
                }
                Ok(bound)
            }
            Pattern::Constructor { ctor, args } => {
                let ctor_info = self
                    .data_registry
                    .get_ctor(ctor.as_str())
                    .ok_or_else(|| self.at(s, TypeError::UnknownConstructor(ctor.clone())))?
                    .clone();

                if args.len() != ctor_info.fields.len() {
                    return Err(self.at(
                        s,
                        TypeError::ConstructorArityMismatch {
                            ctor: ctor.clone(),
                            expected: ctor_info.fields.len(),
                            got: args.len(),
                        },
                    ));
                }

                let data_info = self
                    .data_registry
                    .get_type(&ctor_info.parent)
                    .expect("ctor's parent must be registered")
                    .clone();

                let mut subst: HashMap<SmolStr, Ty> = HashMap::new();
                for tp in &data_info.type_params {
                    subst.insert(tp.clone(), self.fresh_unif());
                }

                let mut payloads: Vec<Ty> = Vec::with_capacity(data_info.ctor_names.len());
                for cname in &data_info.ctor_names {
                    let ci = self
                        .data_registry
                        .get_ctor(cname.as_str())
                        .expect("parent's ctor must be registered");
                    payloads.push(build_payload_ty(&ci.fields, &subst));
                }
                let parent_ty = right_nested_sum(&payloads);

                self.unify(s, &parent_ty, &expected)?;

                let field_tys: Vec<Ty> = ctor_info
                    .fields
                    .iter()
                    .map(|f| subst_tys(f, &subst))
                    .collect();

                let mut bound = Vec::new();
                for (arg, field_ty) in args.iter().zip(field_tys.iter()) {
                    bound.extend(self.check_pattern(s, arg, field_ty)?);
                }
                Ok(bound)
            }
        }
    }

    /// Check exhaustiveness of a match's arm patterns using a
    /// Maranget-style specialize/default usefulness algorithm.
    ///
    /// Builds a single-column pattern matrix from the arms and asks
    /// whether the wildcard row `[_]` is useful with respect to that
    /// matrix. A useful witness is a pretty-printed missing case;
    /// "not useful" means every value is covered.
    ///
    /// Handles bool full coverage without a wildcard, nested
    /// constructor patterns (recursive column specialization), and
    /// mixed literal-plus-constructor columns. Infinite domains (Int,
    /// Float, opaque types) require a wildcard / `Var` arm to be
    /// exhaustive.
    fn check_exhaustiveness(
        &self,
        s: Span,
        arms: &[MatchArm],
        _scrutinee_ty: &Ty,
    ) -> Result<(), SpannedTypeError> {
        let matrix: Vec<Vec<Pattern>> = arms
            .iter()
            .map(|a| vec![a.pattern.clone()])
            .collect();
        if let Some(witness) = is_useful(&matrix, 1, &self.data_registry) {
            let pretty = pretty_witness(&witness[0]);
            return Err(self.at(
                s,
                TypeError::NonExhaustiveMatch {
                    missing: SmolStr::new(&pretty),
                },
            ));
        }
        Ok(())
    }

    fn check_deref(&mut self, s: Span, inner: &Expr) -> Result<Ty, SpannedTypeError> {
        let inner_ty = self.check(inner)?;

        match inner_ty {
            Ty::Borrow(boxed) => Ok(*boxed),
            Ty::Ref { inner, .. } => Ok(*inner),
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Borrow(Box::new(Ty::Base(BaseTy::Unit))),
                    found: inner_ty,
                },
            )),
        }
    }

    fn check_block(&mut self, _s: Span, exprs: &[Expr]) -> Result<Ty, SpannedTypeError> {
        if exprs.is_empty() {
            return Ok(Ty::Base(BaseTy::Unit));
        }

        let mut result_ty = Ty::Base(BaseTy::Unit);
        for expr in exprs {
            result_ty = self.check(expr)?;
        }
        Ok(result_ty)
    }

    fn check_binop(
        &mut self,
        s: Span,
        op: BinOp,
        left: &Expr,
        right: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let left_ty = self.check(left)?;
        let right_ty = self.check(right)?;

        self.unify(s, &left_ty, &right_ty)?;
        let left_ty = self.resolve(&left_ty);

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => match &left_ty {
                Ty::Base(BaseTy::I32)
                | Ty::Base(BaseTy::I64)
                | Ty::Base(BaseTy::F32)
                | Ty::Base(BaseTy::F64) => Ok(left_ty),
                _ => Err(self.at(
                    s,
                    TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::I32),
                        found: left_ty,
                    },
                )),
            },
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                Ok(Ty::Base(BaseTy::Bool))
            }
            BinOp::And | BinOp::Or => {
                if left_ty != Ty::Base(BaseTy::Bool) {
                    return Err(self.at(
                        s,
                        TypeError::TypeMismatch {
                            expected: Ty::Base(BaseTy::Bool),
                            found: left_ty,
                        },
                    ));
                }
                Ok(Ty::Base(BaseTy::Bool))
            }
        }
    }

    fn check_unaryop(
        &mut self,
        s: Span,
        op: UnaryOp,
        operand: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let operand_ty = self.check(operand)?;

        match op {
            UnaryOp::Not => {
                if operand_ty != Ty::Base(BaseTy::Bool) {
                    return Err(self.at(
                        s,
                        TypeError::TypeMismatch {
                            expected: Ty::Base(BaseTy::Bool),
                            found: operand_ty,
                        },
                    ));
                }
                Ok(Ty::Base(BaseTy::Bool))
            }
            UnaryOp::Neg => match &operand_ty {
                Ty::Base(BaseTy::I32)
                | Ty::Base(BaseTy::I64)
                | Ty::Base(BaseTy::F32)
                | Ty::Base(BaseTy::F64) => Ok(operand_ty),
                _ => Err(self.at(
                    s,
                    TypeError::TypeMismatch {
                        expected: Ty::Base(BaseTy::I32),
                        found: operand_ty,
                    },
                )),
            },
        }
    }

    fn check_list_lit(&mut self, s: Span, elements: &[Expr]) -> Result<Ty, SpannedTypeError> {
        if elements.is_empty() {
            return Ok(Ty::List(Box::new(Ty::Base(BaseTy::I32))));
        }

        let elem_ty = self.check(&elements[0])?;

        for elem in &elements[1..] {
            let ty = self.check(elem)?;
            if ty != elem_ty {
                return Err(self.at(
                    s,
                    TypeError::TypeMismatch {
                        expected: elem_ty.clone(),
                        found: ty,
                    },
                ));
            }
        }

        Ok(Ty::List(Box::new(elem_ty)))
    }

    fn check_list_index(
        &mut self,
        s: Span,
        list: &Expr,
        index: &Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let list_ty = self.check(list)?;
        let index_ty = self.check(index)?;

        if index_ty != Ty::Base(BaseTy::I32) {
            return Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Base(BaseTy::I32),
                    found: index_ty,
                },
            ));
        }

        match list_ty {
            Ty::List(elem_ty) => Ok(*elem_ty),
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::List(Box::new(Ty::Base(BaseTy::I32))),
                    found: list_ty,
                },
            )),
        }
    }

    fn check_tuple_lit(&mut self, _s: Span, elements: &[Expr]) -> Result<Ty, SpannedTypeError> {
        if elements.is_empty() {
            return Ok(Ty::Base(BaseTy::Unit));
        }

        if elements.len() == 1 {
            return self.check(&elements[0]);
        }

        if elements.len() == 2 {
            let left_ty = self.check(&elements[0])?;
            let right_ty = self.check(&elements[1])?;
            return Ok(Ty::Prod {
                left: Box::new(left_ty),
                right: Box::new(right_ty),
            });
        }

        let mut elem_types = Vec::new();
        for elem in elements {
            elem_types.push(self.check(elem)?);
        }
        Ok(Ty::Tuple(elem_types))
    }

    fn check_tuple_index(
        &mut self,
        s: Span,
        tuple: &Expr,
        index: usize,
    ) -> Result<Ty, SpannedTypeError> {
        let tuple_ty = self.check(tuple)?;

        match &tuple_ty {
            Ty::Prod { left, right } => {
                if index == 0 {
                    Ok((**left).clone())
                } else if index == 1 {
                    Ok((**right).clone())
                } else {
                    Err(self.at(
                        s,
                        TypeError::TypeMismatch {
                            expected: Ty::Base(BaseTy::Unit),
                            found: tuple_ty,
                        },
                    ))
                }
            }
            Ty::Tuple(elem_types) => {
                if index < elem_types.len() {
                    Ok(elem_types[index].clone())
                } else {
                    Err(self.at(
                        s,
                        TypeError::TypeMismatch {
                            expected: Ty::Base(BaseTy::Unit),
                            found: Ty::Tuple(elem_types.clone()),
                        },
                    ))
                }
            }
            _ => Err(self.at(
                s,
                TypeError::TypeMismatch {
                    expected: Ty::Tuple(vec![]),
                    found: tuple_ty.clone(),
                },
            )),
        }
    }

    /// Type-check an FFI call.
    ///
    /// String literal arguments are allowed WITHOUT region allocation.
    /// Linear variables passed to FFI are consumed.
    /// Return type is I64 (opaque C handle).
    fn check_ffi(&mut self, _s: Span, args: &[Expr]) -> Result<Ty, SpannedTypeError> {
        for arg in args {
            match &arg.kind {
                ExprKind::Lit(Literal::String(_)) => {
                    // OK — string literal is passed as C string pointer
                }
                _ => {
                    self.check(arg)?;
                }
            }
        }
        Ok(Ty::Base(BaseTy::I64))
    }

    /// Type check a perform expression: `perform op(args...)`.
    ///
    /// Performs an effect operation. All arguments are type-checked.
    /// The return type is a fresh unification variable — it will be
    /// constrained by the enclosing handler's return clause or by
    /// the context where the result is used.
    ///
    /// Linear variables passed as arguments are consumed.
    fn check_perform(
        &mut self,
        _s: Span,
        _op: &Var,
        args: &[Expr],
    ) -> Result<Ty, SpannedTypeError> {
        // Type check all arguments (consumes linear resources)
        for arg in args {
            self.check(arg)?;
        }
        // Return type determined by handler — use fresh unification variable
        Ok(self.fresh_unif())
    }

    /// Type check a handle expression: `handle body with clauses end`.
    ///
    /// The body is type-checked. Each handler clause is checked:
    /// - **Return clause** (op = ""): binds the body's result type, produces
    ///   the handle expression's overall return type.
    /// - **Operation clause**: binds operation parameters, optionally a resume
    ///   continuation. The clause body must produce the same type as the
    ///   return clause.
    ///
    /// If `resume(multi)` is used and the continuation captures linear values,
    /// this is a type error (linear values would be duplicated).
    fn check_handle(
        &mut self,
        s: Span,
        body: &Expr,
        clauses: &[ephapax_syntax::HandlerClause],
    ) -> Result<Ty, SpannedTypeError> {
        // Type check the body — its type is what the return clause receives
        let body_ty = self.check(body)?;

        // Find the return clause to determine the overall type
        let mut result_ty: Option<Ty> = None;

        for clause in clauses {
            if clause.op.is_empty() {
                // Return clause: return(x) => body
                // x has the body's type
                if let Some(param) = clause.params.first() {
                    self.ctx
                        .extend(param.clone(), body_ty.clone(), BindingForm::Let);
                }
                let clause_ty = self.check(&clause.body)?;
                result_ty = Some(clause_ty);
            } else {
                // Operation clause: op(params..., resume?) => body
                // Parameters get fresh unification variables
                for param in &clause.params {
                    let param_ty = self.fresh_unif();
                    self.ctx
                        .extend(param.clone(), param_ty, BindingForm::Let);
                }

                // If resume mode is specified, add a resume callback to scope
                if let Some(mode) = clause.resume_mode {
                    // resume : answer_ty -> result_ty
                    // For resume(multi), check no linear captures exist
                    if mode == ephapax_syntax::ResumeMode::Multi {
                        // Check context for linear variables — multi-shot with
                        // linear captures is a type error
                        for (name, entry) in &self.ctx.vars {
                            if entry.demands_consumption() && !entry.used {
                                return Err(self.at(
                                    s,
                                    TypeError::LinearVariableNotConsumed(name.clone()),
                                ));
                            }
                        }
                    }
                }

                let clause_ty = self.check(&clause.body)?;

                // All clauses must produce the same type
                if let Some(ref rt) = result_ty {
                    self.unify(s, rt, &clause_ty)?;
                } else {
                    result_ty = Some(clause_ty);
                }
            }
        }

        Ok(result_ty.unwrap_or(self.resolve(&body_ty)))
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

// Re-export for backward compatibility during migration.
/// Deprecated: The dyadic property is per-binding, not a global mode.
#[deprecated(
    note = "Mode removed: dyadic property is per-binding (let vs let!), not a global switch"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Linear (the only real mode — kept for migration)
    Linear,
}

/// Deprecated: Use `type_check_module` directly.
#[deprecated(note = "Use type_check_module() — Mode parameter removed")]
#[allow(deprecated)]
pub fn type_check_module_with_mode(module: &Module, _mode: Mode) -> Result<(), SpannedTypeError> {
    type_check_module(module)
}

/// Deprecated: Use `type_check_expr` directly.
#[deprecated(note = "Use type_check_expr() — Mode parameter removed")]
#[allow(deprecated)]
pub fn type_check_expr_with_mode(expr: &Expr, _mode: Mode) -> Result<Ty, SpannedTypeError> {
    type_check_expr(expr)
}

/// Type check an entire module (standalone, no imports).
///
/// The dyadic property is per-binding: `let` is affine, `let!` is linear.
pub fn type_check_module(module: &Module) -> Result<(), SpannedTypeError> {
    let mut tc = TypeChecker::new();
    type_check_module_inner(&mut tc, module)
}

/// Registry of type-checked modules for cross-module resolution.
///
/// After a module is type-checked, its public declarations are registered
/// here so that dependent modules can import them.
#[derive(Debug, Default)]
pub struct ModuleRegistry {
    /// Module name -> list of (decl_name, type, visibility).
    modules: HashMap<Var, Vec<(Var, Ty, Visibility)>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a module's declarations after type checking.
    pub fn register(&mut self, module: &Module) {
        let mut entries = Vec::new();
        for decl in &module.decls {
            match decl {
                Decl::Fn {
                    name,
                    visibility,
                    type_params,
                    params,
                    ret_ty,
                    ..
                } => {
                    // Nullary fn `fn foo(): T = ...` has type `() -> T`,
                    // not `T`. Without this wrap, `foo()` at a call site
                    // fails to unify `T applied to ()`.
                    let fn_ty = if params.is_empty() {
                        Ty::Fun {
                            param: Box::new(Ty::Base(BaseTy::Unit)),
                            ret: Box::new(ret_ty.clone()),
                        }
                    } else {
                        params
                            .iter()
                            .rev()
                            .fold(ret_ty.clone(), |acc, (_, param_ty)| Ty::Fun {
                                param: Box::new(param_ty.clone()),
                                ret: Box::new(acc),
                            })
                    };
                    let poly_ty =
                        type_params.iter().rev().fold(fn_ty, |acc, tv| Ty::ForAll {
                            var: tv.clone(),
                            body: Box::new(acc),
                        });
                    entries.push((name.clone(), poly_ty, *visibility));
                }
                Decl::Type {
                    name, visibility, ty,
                } => {
                    entries.push((name.clone(), ty.clone(), *visibility));
                }
                Decl::Const { name, ty, value: _ } => {
                    // Constants are module-level values; add with inferred or annotated type
                    let const_ty = ty.clone().unwrap_or(Ty::Base(BaseTy::Unit));
                    entries.push((name.clone(), const_ty, Visibility::Private));
                }
                Decl::Extern {
                    name,
                    abi: _,
                    params,
                    ret_ty,
                } => {
                    // Extern items are publicly available to importers — the
                    // host runtime / wasm imports resolve them; we don't gate
                    // visibility at the language level here.
                    let fn_ty = if params.is_empty() {
                        Ty::Fun {
                            param: Box::new(Ty::Base(BaseTy::Unit)),
                            ret: Box::new(ret_ty.clone()),
                        }
                    } else {
                        params
                            .iter()
                            .rev()
                            .fold(ret_ty.clone(), |acc, (_, param_ty)| Ty::Fun {
                                param: Box::new(param_ty.clone()),
                                ret: Box::new(acc),
                            })
                    };
                    entries.push((name.clone(), fn_ty, Visibility::Public));
                }
            }
        }
        self.modules.insert(module.name.clone(), entries);
    }

    /// Look up a public name from a registered module.
    pub fn lookup(&self, module_name: &Var, decl_name: &Var) -> Option<&Ty> {
        self.modules.get(module_name).and_then(|entries| {
            entries.iter().find_map(|(name, ty, vis)| {
                if name == decl_name && *vis == Visibility::Public {
                    Some(ty)
                } else {
                    None
                }
            })
        })
    }

    /// Get all public names from a module.
    pub fn public_names(&self, module_name: &Var) -> Vec<(Var, Ty)> {
        self.modules
            .get(module_name)
            .map(|entries| {
                entries
                    .iter()
                    .filter(|(_, _, vis)| *vis == Visibility::Public)
                    .map(|(name, ty, _)| (name.clone(), ty.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }
}

/// Type check a module with access to a registry of previously checked modules.
///
/// Imports are resolved against the registry. After successful checking,
/// the module is automatically registered.
pub fn type_check_module_with_registry(
    module: &Module,
    registry: &mut ModuleRegistry,
) -> Result<(), SpannedTypeError> {
    let mut tc = TypeChecker::new();

    // Resolve imports: bring imported names into scope
    for import in &module.imports {
        if import.names.is_empty() {
            // Import all public names
            for (name, ty) in registry.public_names(&import.module) {
                tc.ctx.extend(name, ty, BindingForm::Let);
            }
        } else {
            // Import specific names
            for name in &import.names {
                if let Some(ty) = registry.lookup(&import.module, name) {
                    tc.ctx.extend(name.clone(), ty.clone(), BindingForm::Let);
                } else {
                    // Import resolution error — use dummy span since Import has no span
                    return Err(SpannedTypeError {
                        error: TypeError::UnboundVariable(
                            Var::from(format!("{}::{}", import.module, name)),
                        ),
                        span: Span::dummy(),
                    });
                }
            }
        }
    }

    // Delegate to regular module checking (which handles signatures + bodies)
    type_check_module_inner(&mut tc, module)?;

    // Register this module's declarations for dependents
    registry.register(module);

    Ok(())
}

/// Internal module checking logic shared by single-module and registry paths.
fn type_check_module_inner(
    tc: &mut TypeChecker,
    module: &Module,
) -> Result<(), SpannedTypeError> {
    // First pass: collect all function signatures, including externs.
    for decl in &module.decls {
        match decl {
            Decl::Fn {
                name,
                params,
                ret_ty,
                type_params,
                ..
            } => {
                let fn_ty = if params.is_empty() {
                    Ty::Fun {
                        param: Box::new(Ty::Base(BaseTy::Unit)),
                        ret: Box::new(ret_ty.clone()),
                    }
                } else {
                    params
                        .iter()
                        .rev()
                        .fold(ret_ty.clone(), |acc, (_, param_ty)| Ty::Fun {
                            param: Box::new(param_ty.clone()),
                            ret: Box::new(acc),
                        })
                };
                let poly_ty = type_params.iter().rev().fold(fn_ty, |acc, tv| Ty::ForAll {
                    var: tv.clone(),
                    body: Box::new(acc),
                });
                tc.ctx.extend(name.clone(), poly_ty, BindingForm::Let);
            }
            Decl::Extern {
                name,
                abi: _,
                params,
                ret_ty,
            } => {
                let fn_ty = if params.is_empty() {
                    Ty::Fun {
                        param: Box::new(Ty::Base(BaseTy::Unit)),
                        ret: Box::new(ret_ty.clone()),
                    }
                } else {
                    params
                        .iter()
                        .rev()
                        .fold(ret_ty.clone(), |acc, (_, param_ty)| Ty::Fun {
                            param: Box::new(param_ty.clone()),
                            ret: Box::new(acc),
                        })
                };
                tc.ctx.extend(name.clone(), fn_ty, BindingForm::Let);
            }
            Decl::Type { .. } | Decl::Const { .. } => {}
        }
    }

    // Second pass: type check each function body
    for decl in &module.decls {
        match decl {
            Decl::Fn {
                name: _,
                type_params: _,
                visibility: _,
                params,
                ret_ty,
                body,
            } => {
                let saved_ctx = tc.ctx.clone();
                let saved_unif = tc.next_unif;

                for (param_name, param_ty) in params {
                    tc.ctx
                        .extend(param_name.clone(), param_ty.clone(), BindingForm::Param);
                }

                let body_ty = tc.check(body)?;

                tc.unify(body.span, ret_ty, &body_ty)?;

                for (param_name, _param_ty) in params {
                    if let Some(entry) = tc.ctx.vars.get(param_name) {
                        if entry.demands_consumption() && !entry.used {
                            return Err(SpannedTypeError {
                                error: TypeError::LinearVariableNotConsumed(param_name.clone()),
                                span: body.span,
                            });
                        }
                    }
                }

                tc.ctx = saved_ctx;
                tc.next_unif = saved_unif;
                tc.unif_solutions.clear();
            }
            Decl::Type { .. } => {}
            Decl::Const { .. } => {} // Constants are handled in module registration
            // Extern items have no body to check — registered in first pass.
            Decl::Extern { .. } => {}
        }
    }

    Ok(())
}

/// Type check a single expression.
pub fn type_check_expr(expr: &Expr) -> Result<Ty, SpannedTypeError> {
    let mut tc = TypeChecker::new();
    tc.check(expr)
}

/// Type check a single expression (alias for type_check_expr).
pub fn type_check(expr: &Expr) -> Result<Ty, SpannedTypeError> {
    type_check_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::{Span, Visibility};

    fn dummy_expr(kind: ExprKind) -> Expr {
        Expr::new(kind, Span::dummy())
    }

    /// Helper to match on the inner TypeError, ignoring the span.
    fn err_kind(result: &Result<Ty, SpannedTypeError>) -> Option<&TypeError> {
        match result {
            Err(spanned) => Some(&spanned.error),
            Ok(_) => None,
        }
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
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let var = dummy_expr(ExprKind::Var("s".into()));
        assert!(tc.check(&var).is_ok());

        let var2 = dummy_expr(ExprKind::Var("s".into()));
        assert!(matches!(
            err_kind(&tc.check(&var2)),
            Some(TypeError::LinearVariableReused(_))
        ));
    }

    #[test]
    fn test_if_branch_agreement_both_consume() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

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
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(2)))),
        });

        assert!(tc.check(&expr).is_ok());
    }

    #[test]
    fn test_if_branch_disagreement_then_consumes() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

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
                err_kind(&result),
                Some(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Expected BranchLinearityMismatchDetailed, got {:?}",
            result
        );
    }

    #[test]
    fn test_if_branch_disagreement_else_consumes() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

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
                err_kind(&result),
                Some(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Expected BranchLinearityMismatchDetailed, got {:?}",
            result
        );
    }

    #[test]
    fn test_borrow_does_not_consume() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        let result = tc.check(&borrow_expr);
        assert!(result.is_ok());

        let var = dummy_expr(ExprKind::Var("s".into()));
        let result2 = tc.check(&var);
        assert!(result2.is_ok(), "Variable should not be consumed by borrow");
    }

    #[test]
    fn test_borrow_then_consume_ok() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let borrow_expr = dummy_expr(ExprKind::Borrow(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(tc.check(&borrow_expr).is_ok());

        let drop_expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(tc.check(&drop_expr).is_ok());

        let var = dummy_expr(ExprKind::Var("s".into()));
        assert!(matches!(
            err_kind(&tc.check(&var)),
            Some(TypeError::LinearVariableReused(_))
        ));
    }

    #[test]
    fn test_string_literal_error() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Lit(Literal::String("hello".to_string())));
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::UnallocatedStringLiteral)
        ));
    }

    #[test]
    fn test_let_annotation_match() {
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
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Let {
            name: "x".into(),
            ty: Some(Ty::Base(BaseTy::Bool)),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
        });
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::AnnotationMismatch { .. })
        ));
    }

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
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Fst(Box::new(dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        }))));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::I32));
    }

    #[test]
    fn test_fst_linear_snd_rejected() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Fst(Box::new(dummy_expr(ExprKind::Pair {
            left: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(dummy_expr(ExprKind::Var("s".into()))),
        }))));
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::LinearVariableNotConsumed(_))
        ));
    }

    #[test]
    fn test_inl_typing() {
        let mut tc = TypeChecker::new();
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

    #[test]
    fn test_region_string_allocation() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Region {
            name: "r".into(),
            body: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
        });
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::RegionEscape { .. })
        ));
    }

    #[test]
    fn test_region_non_escaping() {
        let mut tc = TypeChecker::new();
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
        let expr = dummy_expr(ExprKind::StringNew {
            region: "r".into(),
            value: "hello".to_string(),
        });
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::InactiveRegion(_))
        ));
    }

    #[test]
    fn test_lambda_typing() {
        let mut tc = TypeChecker::new();
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
        let expr = dummy_expr(ExprKind::App {
            func: Box::new(dummy_expr(ExprKind::Lambda {
                param: "x".into(),
                param_ty: Ty::Base(BaseTy::I32),
                body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
            })),
            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
        });
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::TypeMismatch { .. })
        ));
    }

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
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Copy(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::CannotCopyLinear(_))
        ));
    }

    #[test]
    fn test_drop_linear_ok() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Var(
            "s".into(),
        )))));
        assert_eq!(tc.check(&expr).unwrap(), Ty::Base(BaseTy::Unit));
    }

    #[test]
    fn test_drop_unrestricted_rejected() {
        let mut tc = TypeChecker::new();
        let expr = dummy_expr(ExprKind::Drop(Box::new(dummy_expr(ExprKind::Lit(
            Literal::I32(42),
        )))));
        assert!(matches!(
            err_kind(&tc.check(&expr)),
            Some(TypeError::UnnecessaryDrop)
        ));
    }

    #[test]
    fn test_module_basic() {
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "add".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![
                    ("a".into(), Ty::Base(BaseTy::I32)),
                    ("b".into(), Ty::Base(BaseTy::I32)),
                ],
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
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "bad".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![],
                ret_ty: Ty::Base(BaseTy::Bool),
                body: dummy_expr(ExprKind::Lit(Literal::I32(42))),
            }],
        };
        assert!(matches!(
            type_check_module(&module).map_err(|e| e.error),
            Err(TypeError::TypeMismatch { .. })
        ));
    }

    // ===== DYADIC DESIGN: let (affine) vs let! (linear) Tests =====

    #[test]
    fn test_let_bang_rejects_unconsumed() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::LetLin {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            matches!(
                err_kind(&tc.check(&expr)),
                Some(TypeError::LinearVariableNotConsumed(_))
            ),
            "let! unconsumed must be rejected"
        );
    }

    #[test]
    fn test_let_allows_unconsumed_linear() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());

        let expr = dummy_expr(ExprKind::Let {
            name: "s".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::StringNew {
                region: "r".into(),
                value: "hello".to_string(),
            })),
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            tc.check(&expr).is_ok(),
            "let (affine) should allow unconsumed linear values"
        );
    }

    #[test]
    fn test_let_bang_rejects_unconsumed_unrestricted() {
        let mut tc = TypeChecker::new();

        let expr = dummy_expr(ExprKind::LetLin {
            name: "x".into(),
            ty: None,
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            matches!(
                err_kind(&tc.check(&expr)),
                Some(TypeError::LinearVariableNotConsumed(_))
            ),
            "let! of unrestricted type must still reject unconsumed"
        );
    }

    #[test]
    fn test_linear_rejects_double_use() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let var1 = dummy_expr(ExprKind::Var("s".into()));
        assert!(tc.check(&var1).is_ok());

        let var2 = dummy_expr(ExprKind::Var("s".into()));
        assert!(
            matches!(
                err_kind(&tc.check(&var2)),
                Some(TypeError::LinearVariableReused(_))
            ),
            "Double use of linear variable must be rejected"
        );
    }

    #[test]
    fn test_module_rejects_unconsumed_linear_param() {
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "forget".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![("s".into(), Ty::String("r".into()))],
                ret_ty: Ty::Base(BaseTy::Unit),
                body: dummy_expr(ExprKind::Lit(Literal::Unit)),
            }],
        };

        assert!(
            type_check_module(&module).is_err(),
            "Unconsumed linear param must be rejected"
        );
    }

    #[test]
    fn test_if_branches_must_agree_on_linear_consumption() {
        let mut tc = TypeChecker::new();
        tc.ctx.enter_region("r".into());
        tc.ctx
            .extend("s".into(), Ty::String("r".into()), BindingForm::LetBang);

        let expr = dummy_expr(ExprKind::If {
            cond: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(dummy_expr(ExprKind::Drop(Box::new(dummy_expr(
                ExprKind::Var("s".into()),
            ))))),
            else_branch: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });

        assert!(
            matches!(
                err_kind(&tc.check(&expr)),
                Some(TypeError::BranchLinearityMismatchDetailed { .. })
            ),
            "Branch disagreement on linear consumption must be rejected"
        );
    }

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

    #[test]
    fn test_span_propagation() {
        // Verify that error spans point to the right expression.
        let mut tc = TypeChecker::new();
        let inner = Expr::new(ExprKind::Lit(Literal::String("bare".into())), Span::new(10, 25));
        let outer = Expr::new(
            ExprKind::Let {
                name: "x".into(),
                ty: None,
                value: Box::new(inner),
                body: Box::new(dummy_expr(ExprKind::Var("x".into()))),
            },
            Span::new(0, 40),
        );
        let result = tc.check(&outer);
        let err = result.unwrap_err();
        // The error should point to the string literal (inner), not the let (outer)
        assert_eq!(err.span, Span::new(10, 25));
        assert!(matches!(err.error, TypeError::UnallocatedStringLiteral));
    }

    // ===== GENERICS / POLYMORPHISM Tests =====

    #[test]
    fn test_generic_identity_function() {
        // fn identity<T>(x: T) : T = x
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "identity".into(),
                visibility: Visibility::Private,
                type_params: vec!["T".into()],
                params: vec![("x".into(), Ty::Var("T".into()))],
                ret_ty: Ty::Var("T".into()),
                body: dummy_expr(ExprKind::Var("x".into())),
            }],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_generic_identity_called_with_i32() {
        // fn identity<T>(x: T) : T = x
        // fn main() : I32 = identity(42)
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Fn {
                    name: "identity".into(),
                    visibility: Visibility::Private,
                    type_params: vec!["T".into()],
                    params: vec![("x".into(), Ty::Var("T".into()))],
                    ret_ty: Ty::Var("T".into()),
                    body: dummy_expr(ExprKind::Var("x".into())),
                },
                Decl::Fn {
                    name: "main".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: dummy_expr(ExprKind::App {
                        func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                        arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
                    }),
                },
            ],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_generic_identity_called_with_bool() {
        // fn identity<T>(x: T) : T = x
        // fn main() : Bool = identity(true)
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Fn {
                    name: "identity".into(),
                    visibility: Visibility::Private,
                    type_params: vec!["T".into()],
                    params: vec![("x".into(), Ty::Var("T".into()))],
                    ret_ty: Ty::Var("T".into()),
                    body: dummy_expr(ExprKind::Var("x".into())),
                },
                Decl::Fn {
                    name: "main".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::Bool),
                    body: dummy_expr(ExprKind::App {
                        func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                        arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
                    }),
                },
            ],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_generic_identity_wrong_return_type() {
        // fn identity<T>(x: T) : T = x
        // fn main() : Bool = identity(42)  — returns I32, not Bool
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Fn {
                    name: "identity".into(),
                    visibility: Visibility::Private,
                    type_params: vec!["T".into()],
                    params: vec![("x".into(), Ty::Var("T".into()))],
                    ret_ty: Ty::Var("T".into()),
                    body: dummy_expr(ExprKind::Var("x".into())),
                },
                Decl::Fn {
                    name: "main".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::Bool),
                    body: dummy_expr(ExprKind::App {
                        func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                        arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
                    }),
                },
            ],
        };
        assert!(type_check_module(&module).is_err());
    }

    #[test]
    fn test_generic_two_params() {
        // fn const_fn<A, B>(x: A, y: B) : A = x
        // fn main() : I32 = const_fn(42, true)
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Fn {
                    name: "const_fn".into(),
                    visibility: Visibility::Private,
                    type_params: vec!["A".into(), "B".into()],
                    params: vec![
                        ("x".into(), Ty::Var("A".into())),
                        ("y".into(), Ty::Var("B".into())),
                    ],
                    ret_ty: Ty::Var("A".into()),
                    // const_fn is curried: fn(x: A) -> fn(y: B) -> x
                    // But our module checker expects multi-param.
                    // Actually module checker expects the body to be checked
                    // with all params in scope, so just return x.
                    body: dummy_expr(ExprKind::Var("x".into())),
                },
                Decl::Fn {
                    name: "main".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::I32),
                    // const_fn(42)(true) — curried application
                    body: dummy_expr(ExprKind::App {
                        func: Box::new(dummy_expr(ExprKind::App {
                            func: Box::new(dummy_expr(ExprKind::Var("const_fn".into()))),
                            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
                        })),
                        arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
                    }),
                },
            ],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_generic_called_multiple_times_different_types() {
        // fn identity<T>(x: T) : T = x
        // fn main() : I32 =
        //   let a = identity(42) in     -- T = I32
        //   let b = identity(true) in   -- T = Bool (fresh instantiation)
        //   a
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Fn {
                    name: "identity".into(),
                    visibility: Visibility::Private,
                    type_params: vec!["T".into()],
                    params: vec![("x".into(), Ty::Var("T".into()))],
                    ret_ty: Ty::Var("T".into()),
                    body: dummy_expr(ExprKind::Var("x".into())),
                },
                Decl::Fn {
                    name: "main".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: dummy_expr(ExprKind::Let {
                        name: "a".into(),
                        ty: None,
                        value: Box::new(dummy_expr(ExprKind::App {
                            func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                            arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(42)))),
                        })),
                        body: Box::new(dummy_expr(ExprKind::Let {
                            name: "b".into(),
                            ty: None,
                            value: Box::new(dummy_expr(ExprKind::App {
                                func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                                arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
                            })),
                            body: Box::new(dummy_expr(ExprKind::Var("a".into()))),
                        })),
                    }),
                },
            ],
        };
        assert!(type_check_module(&module).is_ok());
    }

    #[test]
    fn test_unification_basic() {
        // Directly test the unification engine
        let mut tc = TypeChecker::new();
        let s = Span::dummy();

        // Unify I32 with I32 — should succeed
        assert!(tc.unify(s, &Ty::Base(BaseTy::I32), &Ty::Base(BaseTy::I32)).is_ok());

        // Unify I32 with Bool — should fail
        assert!(tc.unify(s, &Ty::Base(BaseTy::I32), &Ty::Base(BaseTy::Bool)).is_err());

        // Unify ?0 with I32 — should succeed and solve ?0 = I32
        let u = tc.fresh_unif();
        assert!(tc.unify(s, &u, &Ty::Base(BaseTy::I32)).is_ok());
        assert_eq!(tc.resolve(&u), Ty::Base(BaseTy::I32));

        // Unify ?1 with ?2, then ?2 with Bool — should chain
        let u1 = tc.fresh_unif();
        let u2 = tc.fresh_unif();
        assert!(tc.unify(s, &u1, &u2).is_ok());
        assert!(tc.unify(s, &u2, &Ty::Base(BaseTy::Bool)).is_ok());
        assert_eq!(tc.resolve(&u1), Ty::Base(BaseTy::Bool));
    }

    #[test]
    fn test_instantiate_forall() {
        let mut tc = TypeChecker::new();

        // ForAll T. T -> T instantiates to ?0 -> ?0
        let forall_ty = Ty::ForAll {
            var: "T".into(),
            body: Box::new(Ty::Fun {
                param: Box::new(Ty::Var("T".into())),
                ret: Box::new(Ty::Var("T".into())),
            }),
        };
        let instantiated = tc.instantiate(forall_ty);

        // Should be Fun { param: Unif(0), ret: Unif(0) }
        match &instantiated {
            Ty::Fun { param, ret } => {
                assert!(matches!(param.as_ref(), Ty::Unif(0)));
                assert!(matches!(ret.as_ref(), Ty::Unif(0)));
            }
            other => panic!("Expected Fun, got {:?}", other),
        }
    }

    // ===== MODULE SYSTEM Tests =====

    #[test]
    fn test_cross_module_import() {
        use ephapax_syntax::Import;

        // Module "lib": pub fn double(x: I32) : I32 = x + x
        let lib_module = Module {
            name: "lib".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "double".into(),
                visibility: Visibility::Public,
                type_params: vec![],
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: dummy_expr(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(dummy_expr(ExprKind::Var("x".into()))),
                    right: Box::new(dummy_expr(ExprKind::Var("x".into()))),
                }),
            }],
        };

        // Module "main": import lib; fn main() : I32 = double(21)
        let main_module = Module {
            name: "main".into(),
            imports: vec![Import {
                module: "lib".into(),
                names: vec![],
            }],
            decls: vec![Decl::Fn {
                name: "main".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: dummy_expr(ExprKind::App {
                    func: Box::new(dummy_expr(ExprKind::Var("double".into()))),
                    arg: Box::new(dummy_expr(ExprKind::Lit(Literal::I32(21)))),
                }),
            }],
        };

        let mut registry = ModuleRegistry::new();

        // Type check lib first
        type_check_module_with_registry(&lib_module, &mut registry).unwrap();

        // Type check main — imports double from lib
        type_check_module_with_registry(&main_module, &mut registry).unwrap();
    }

    #[test]
    fn test_private_not_importable() {
        use ephapax_syntax::Import;

        // Module "lib": fn secret(x: I32) : I32 = x  (PRIVATE)
        let lib_module = Module {
            name: "lib".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "secret".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: dummy_expr(ExprKind::Var("x".into())),
            }],
        };

        // Module "main": import lib (secret)  — should fail
        let main_module = Module {
            name: "main".into(),
            imports: vec![Import {
                module: "lib".into(),
                names: vec!["secret".into()],
            }],
            decls: vec![Decl::Fn {
                name: "main".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: dummy_expr(ExprKind::Lit(Literal::I32(0))),
            }],
        };

        let mut registry = ModuleRegistry::new();
        type_check_module_with_registry(&lib_module, &mut registry).unwrap();
        // Should fail — "secret" is private
        assert!(type_check_module_with_registry(&main_module, &mut registry).is_err());
    }

    #[test]
    fn test_import_generic_function() {
        use ephapax_syntax::Import;

        // Module "lib": pub fn identity<T>(x: T) : T = x
        let lib_module = Module {
            name: "lib".into(),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: "identity".into(),
                visibility: Visibility::Public,
                type_params: vec!["T".into()],
                params: vec![("x".into(), Ty::Var("T".into()))],
                ret_ty: Ty::Var("T".into()),
                body: dummy_expr(ExprKind::Var("x".into())),
            }],
        };

        // Module "main": import lib; fn main() : Bool = identity(true)
        let main_module = Module {
            name: "main".into(),
            imports: vec![Import {
                module: "lib".into(),
                names: vec![],
            }],
            decls: vec![Decl::Fn {
                name: "main".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![],
                ret_ty: Ty::Base(BaseTy::Bool),
                body: dummy_expr(ExprKind::App {
                    func: Box::new(dummy_expr(ExprKind::Var("identity".into()))),
                    arg: Box::new(dummy_expr(ExprKind::Lit(Literal::Bool(true)))),
                }),
            }],
        };

        let mut registry = ModuleRegistry::new();
        type_check_module_with_registry(&lib_module, &mut registry).unwrap();
        type_check_module_with_registry(&main_module, &mut registry).unwrap();
    }

    // =========================================================================
    // Extern blocks (#43 phase 2B-i)
    // =========================================================================
    //
    // These tests cover the typechecker's handling of `extern "abi" {
    // ... }` declarations: extern types are registered as nominal
    // opaque types (resolved by the desugar pass to `Ty::Var(name)`),
    // and extern fn signatures are added to the type environment so
    // regular fn bodies can call them.

    /// A module with an extern block + a regular fn that returns an
    /// extern fn's value type-checks successfully. The extern fn is
    /// nullary (`open_handle(): Window`) so its type is just
    /// `Ty::Var("Window")` after the signature fold — referencing it
    /// directly in the body should produce that opaque type.
    #[test]
    fn typecheck_extern_nullary_fn_callable() {
        // extern "gossamer" { fn open_handle(): Window }
        // fn entry(): Window = open_handle
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Extern {
                    abi: "gossamer".to_string(),
                    items: vec![ExternItem::Fn {
                        name: "open_handle".into(),
                        params: vec![],
                        ret_ty: Ty::Var("Window".into()),
                    }],
                },
                Decl::Fn {
                    name: "entry".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Var("Window".into()),
                    body: Expr::dummy(ExprKind::Var("open_handle".into())),
                },
            ],
        };

        type_check_module(&module).expect("extern reference should type-check");
    }

    /// A unary extern fn called with the correct argument type-checks;
    /// the result flows back through the regular fn's return.
    #[test]
    fn typecheck_extern_unary_fn_applied() {
        // extern "gossamer" { fn open(h: I32): Window }
        // fn entry(): Window = open(7)
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Extern {
                    abi: "gossamer".to_string(),
                    items: vec![ExternItem::Fn {
                        name: "open".into(),
                        params: vec![("h".into(), Ty::Base(BaseTy::I32))],
                        ret_ty: Ty::Var("Window".into()),
                    }],
                },
                Decl::Fn {
                    name: "entry".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Var("Window".into()),
                    body: Expr::dummy(ExprKind::App {
                        func: Box::new(Expr::dummy(ExprKind::Var("open".into()))),
                        arg: Box::new(Expr::dummy(ExprKind::Lit(Literal::I32(7)))),
                    }),
                },
            ],
        };

        type_check_module(&module).expect("unary extern call should type-check");
    }

    /// Calling an extern fn with the wrong argument type is rejected.
    /// Here the extern signature is `(I32) -> Window`, but the call
    /// passes a `Bool` — must surface as a typing error rather than
    /// silently succeed.
    #[test]
    fn typecheck_extern_fn_arg_mismatch_rejected() {
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Extern {
                    abi: "gossamer".to_string(),
                    items: vec![ExternItem::Fn {
                        name: "open".into(),
                        params: vec![("h".into(), Ty::Base(BaseTy::I32))],
                        ret_ty: Ty::Var("Window".into()),
                    }],
                },
                Decl::Fn {
                    name: "entry".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Var("Window".into()),
                    body: Expr::dummy(ExprKind::App {
                        func: Box::new(Expr::dummy(ExprKind::Var("open".into()))),
                        arg: Box::new(Expr::dummy(ExprKind::Lit(Literal::Bool(true)))),
                    }),
                },
            ],
        };

        assert!(
            type_check_module(&module).is_err(),
            "passing Bool to a fn expecting I32 must fail"
        );
    }

    /// Two distinct extern types are nominal — they do not unify with
    /// each other or with base types. `Window` and `IpcChannel` are
    /// both `Ty::Var(name)` rigid types from the type checker's view;
    /// declaring `entry: Window` but returning `IpcChannel` must fail.
    #[test]
    fn typecheck_distinct_extern_types_do_not_unify() {
        let module = Module {
            name: "test".into(),
            imports: vec![],
            decls: vec![
                Decl::Extern {
                    abi: "gossamer".to_string(),
                    items: vec![ExternItem::Fn {
                        name: "open_ipc".into(),
                        params: vec![],
                        ret_ty: Ty::Var("IpcChannel".into()),
                    }],
                },
                Decl::Fn {
                    name: "entry".into(),
                    visibility: Visibility::Private,
                    type_params: vec![],
                    params: vec![],
                    ret_ty: Ty::Var("Window".into()),
                    body: Expr::dummy(ExprKind::Var("open_ipc".into())),
                },
            ],
        };

        assert!(
            type_check_module(&module).is_err(),
            "Ty::Var(\"IpcChannel\") must not unify with Ty::Var(\"Window\")"
        );
    }

    // =========================================================================
    // ExprKind::Match — typing, exhaustiveness, error paths
    // =========================================================================

    use ephapax_syntax::{ConstructorDef, MatchArm, Pattern as P};

    /// Build a `data Option(a) = None | Some(a)` declaration.
    fn option_data_decl() -> Decl {
        Decl::Data {
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
        }
    }

    /// Build `data Result(a, e) = Ok(a) | Err(e)`.
    fn result_data_decl() -> Decl {
        Decl::Data {
            name: "Result".into(),
            type_params: vec!["a".into(), "e".into()],
            constructors: vec![
                ConstructorDef {
                    name: "Ok".into(),
                    fields: vec![Ty::Var("a".into())],
                },
                ConstructorDef {
                    name: "Err".into(),
                    fields: vec![Ty::Var("e".into())],
                },
            ],
        }
    }

    /// Wrap an expression as a private `fn test_fn(scrut: T): R = expr`.
    fn fn_decl(name: &str, params: Vec<(Var, Ty)>, ret_ty: Ty, body: Expr) -> Decl {
        Decl::Fn {
            name: name.into(),
            visibility: Visibility::Private,
            type_params: vec![],
            params,
            ret_ty,
            body,
        }
    }

    fn lit_i32(n: i32) -> Expr {
        dummy_expr(ExprKind::Lit(Literal::I32(n)))
    }

    #[test]
    fn test_data_registry_populated_from_decl_data() {
        let mut tc = TypeChecker::new();
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![option_data_decl()],
        };
        tc.data_registry.populate_from_module(&module).unwrap();

        let none = tc.data_registry.get_ctor("None").unwrap();
        assert_eq!(none.parent, SmolStr::from("Option"));
        assert_eq!(none.position, 0);
        assert_eq!(none.total, 2);
        assert!(none.fields.is_empty());

        let some = tc.data_registry.get_ctor("Some").unwrap();
        assert_eq!(some.position, 1);
        assert_eq!(some.fields, vec![Ty::Var("a".into())]);

        let info = tc.data_registry.get_type("Option").unwrap();
        assert_eq!(info.ctor_names, vec![SmolStr::from("None"), SmolStr::from("Some")]);
    }

    #[test]
    fn test_data_registry_rejects_duplicate_ctor() {
        let mut tc = TypeChecker::new();
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                Decl::Data {
                    name: "A".into(),
                    type_params: vec![],
                    constructors: vec![ConstructorDef {
                        name: "X".into(),
                        fields: vec![],
                    }],
                },
                Decl::Data {
                    name: "B".into(),
                    type_params: vec![],
                    constructors: vec![ConstructorDef {
                        name: "X".into(),
                        fields: vec![],
                    }],
                },
            ],
        };
        let err = tc.data_registry.populate_from_module(&module);
        assert!(matches!(err, Err(TypeError::DuplicateConstructor(_))));
    }

    /// `match Some(42) of | None => 0 | Some(v) => v end : I32` — full
    /// pattern resolution: literal, constructor with var arg, binary-sum
    /// encoding, arm-body unification, and exhaustiveness all in one.
    #[test]
    fn test_match_option_exhaustive_typecheck() {
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "None".into(),
                    args: vec![],
                },
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Var("v".into())],
                },
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        type_check_module(&module).expect("Option match should type-check");
    }

    /// Missing `None` arm → NonExhaustiveMatch with `missing: None`.
    #[test]
    fn test_match_non_exhaustive_missing_ctor() {
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![MatchArm {
            pattern: P::Constructor {
                ctor: "Some".into(),
                args: vec![P::Var("v".into())],
            },
            guard: None,
            body: dummy_expr(ExprKind::Var("v".into())),
        }];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(
            matches!(
                err.error,
                TypeError::NonExhaustiveMatch { ref missing } if missing == &SmolStr::from("None")
            ),
            "expected NonExhaustiveMatch{{missing:\"None\"}}, got {:?}",
            err.error
        );
    }

    /// Wildcard arm covers everything else → exhaustive.
    #[test]
    fn test_match_wildcard_makes_exhaustive() {
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![
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
                body: lit_i32(0),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        type_check_module(&module).expect("wildcard should make match exhaustive");
    }

    /// Unknown constructor → UnknownConstructor.
    #[test]
    fn test_match_unknown_constructor() {
        let scrut = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });
        let arms = vec![MatchArm {
            pattern: P::Constructor {
                ctor: "Ghost".into(),
                args: vec![],
            },
            guard: None,
            body: lit_i32(0),
        }];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(
            matches!(err.error, TypeError::UnknownConstructor(ref c) if c == &Var::from("Ghost")),
            "got {:?}",
            err.error
        );
    }

    /// `Some(a, b)` for `Some` of arity 1 → ConstructorArityMismatch.
    #[test]
    fn test_match_constructor_arity_mismatch() {
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Var("a".into()), P::Var("b".into())],
                },
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Wildcard,
                guard: None,
                body: lit_i32(0),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(
            matches!(
                err.error,
                TypeError::ConstructorArityMismatch { expected: 1, got: 2, .. }
            ),
            "got {:?}",
            err.error
        );
    }

    /// Arms return different types → TypeMismatch from inter-arm unify.
    #[test]
    fn test_match_arm_type_mismatch() {
        let scrut = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "None".into(),
                    args: vec![],
                },
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Wildcard],
                },
                guard: None,
                body: dummy_expr(ExprKind::Lit(Literal::Bool(true))),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(
            matches!(err.error, TypeError::TypeMismatch { .. }),
            "got {:?}",
            err.error
        );
    }

    /// Literal patterns over i32 without wildcard → NonExhaustiveMatch.
    #[test]
    fn test_match_literal_non_exhaustive() {
        let arms = vec![
            MatchArm {
                pattern: P::Literal(Literal::I32(0)),
                guard: None,
                body: lit_i32(10),
            },
            MatchArm {
                pattern: P::Literal(Literal::I32(1)),
                guard: None,
                body: lit_i32(20),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(lit_i32(0)),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![fn_decl("f", vec![], Ty::Base(BaseTy::I32), body)],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(
            matches!(err.error, TypeError::NonExhaustiveMatch { .. }),
            "got {:?}",
            err.error
        );
    }

    /// Empty arms list → EmptyMatch.
    #[test]
    fn test_match_empty_arms() {
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(lit_i32(0)),
            arms: vec![],
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![fn_decl("f", vec![], Ty::Base(BaseTy::I32), body)],
        };
        let err = type_check_module(&module).unwrap_err();
        assert!(matches!(err.error, TypeError::EmptyMatch), "got {:?}", err.error);
    }

    /// Multi-param data type with substitution: `Result(I32, Bool)`.
    #[test]
    fn test_match_result_multi_type_param() {
        // scrutinee is `Inl(42)` of declared type `Sum { I32, Bool }`
        let scrut = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::Bool),
            value: Box::new(lit_i32(42)),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Ok".into(),
                    args: vec![P::Var("v".into())],
                },
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Err".into(),
                    args: vec![P::Wildcard],
                },
                guard: None,
                body: lit_i32(0),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                result_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        type_check_module(&module).expect("Result(I32, Bool) match should type-check");
    }

    // ----- Maranget usefulness: nested patterns, bool, mixed columns -----

    /// `match b: Bool { true => ... | false => ... }` is exhaustive
    /// without a wildcard — Maranget should see both Bool constructors.
    #[test]
    fn test_match_bool_full_coverage_no_wildcard() {
        let scrut = dummy_expr(ExprKind::Lit(Literal::Bool(true)));
        let arms = vec![
            MatchArm {
                pattern: P::Literal(Literal::Bool(true)),
                guard: None,
                body: lit_i32(1),
            },
            MatchArm {
                pattern: P::Literal(Literal::Bool(false)),
                guard: None,
                body: lit_i32(0),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![fn_decl("f", vec![], Ty::Base(BaseTy::I32), body)],
        };
        type_check_module(&module)
            .expect("bool true/false should be exhaustive without a wildcard");
    }

    /// `match b: Bool { true => ... }` is non-exhaustive; witness is
    /// `false`.
    #[test]
    fn test_match_bool_missing_false() {
        let scrut = dummy_expr(ExprKind::Lit(Literal::Bool(true)));
        let arms = vec![MatchArm {
            pattern: P::Literal(Literal::Bool(true)),
            guard: None,
            body: lit_i32(1),
        }];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![fn_decl("f", vec![], Ty::Base(BaseTy::I32), body)],
        };
        let err = type_check_module(&module).unwrap_err();
        match err.error {
            TypeError::NonExhaustiveMatch { missing } => {
                assert_eq!(missing, SmolStr::from("false"), "got missing={missing}")
            }
            other => panic!("expected NonExhaustiveMatch, got {other:?}"),
        }
    }

    /// `Option(Option(I32))` covered by `None`, `Some(None)`,
    /// `Some(Some(_))` — exhaustive via specialization.
    #[test]
    fn test_match_nested_option_exhaustive() {
        let inner = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let outer = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(inner),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "None".into(),
                    args: vec![],
                },
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    }],
                },
                guard: None,
                body: lit_i32(1),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    }],
                },
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(outer),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        type_check_module(&module)
            .expect("nested Option(Option(_)) should be exhaustive");
    }

    /// `Option(Option(I32))` with `None` + `Some(Some(_))` only —
    /// missing `Some(None)`. Witness must surface that case.
    #[test]
    fn test_match_nested_option_non_exhaustive_witness() {
        let inner = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(lit_i32(42)),
        });
        let outer = dummy_expr(ExprKind::Inr {
            ty: Ty::Base(BaseTy::Unit),
            value: Box::new(inner),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Constructor {
                    ctor: "None".into(),
                    args: vec![],
                },
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Constructor {
                    ctor: "Some".into(),
                    args: vec![P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    }],
                },
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(outer),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        match err.error {
            TypeError::NonExhaustiveMatch { missing } => {
                assert_eq!(
                    missing,
                    SmolStr::from("Some(None)"),
                    "expected Some(None) witness, got {missing}"
                );
            }
            other => panic!("expected NonExhaustiveMatch, got {other:?}"),
        }
    }

    /// Tuple of `(Option(I32), Bool)` covered by the cross product
    /// `{None,Some(_)} × {true,false}` — exhaustive.
    #[test]
    fn test_match_tuple_option_bool_exhaustive() {
        // scrutinee: `(None, true)` — Pair { Sum{Unit, I32}, Bool }
        let none_val = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });
        let bool_val = dummy_expr(ExprKind::Lit(Literal::Bool(true)));
        let scrut = dummy_expr(ExprKind::Pair {
            left: Box::new(none_val),
            right: Box::new(bool_val),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    }),
                    Box::new(P::Literal(Literal::Bool(true))),
                ),
                guard: None,
                body: lit_i32(1),
            },
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    }),
                    Box::new(P::Literal(Literal::Bool(false))),
                ),
                guard: None,
                body: lit_i32(2),
            },
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    }),
                    Box::new(P::Literal(Literal::Bool(true))),
                ),
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    }),
                    Box::new(P::Literal(Literal::Bool(false))),
                ),
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        type_check_module(&module).expect(
            "cross product (Option, Bool) of all combinations should be exhaustive",
        );
    }

    /// Tuple of `(Option(I32), Bool)` missing `(Some(_), false)` —
    /// witness should reflect that combination.
    #[test]
    fn test_match_tuple_option_bool_missing_one() {
        let none_val = dummy_expr(ExprKind::Inl {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(dummy_expr(ExprKind::Lit(Literal::Unit))),
        });
        let bool_val = dummy_expr(ExprKind::Lit(Literal::Bool(true)));
        let scrut = dummy_expr(ExprKind::Pair {
            left: Box::new(none_val),
            right: Box::new(bool_val),
        });
        let arms = vec![
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "None".into(),
                        args: vec![],
                    }),
                    Box::new(P::Wildcard),
                ),
                guard: None,
                body: lit_i32(0),
            },
            MatchArm {
                pattern: P::Pair(
                    Box::new(P::Constructor {
                        ctor: "Some".into(),
                        args: vec![P::Var("v".into())],
                    }),
                    Box::new(P::Literal(Literal::Bool(true))),
                ),
                guard: None,
                body: dummy_expr(ExprKind::Var("v".into())),
            },
        ];
        let body = dummy_expr(ExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        });
        let module = Module {
            name: "t".into(),
            imports: vec![],
            decls: vec![
                option_data_decl(),
                fn_decl("f", vec![], Ty::Base(BaseTy::I32), body),
            ],
        };
        let err = type_check_module(&module).unwrap_err();
        match err.error {
            TypeError::NonExhaustiveMatch { missing } => {
                // Pair witness should include "Some(_)" and "false"
                let s = missing.as_str();
                assert!(
                    s.contains("Some") && s.contains("false"),
                    "expected witness mentioning Some(_) and false, got {s}"
                );
            }
            other => panic!("expected NonExhaustiveMatch, got {other:?}"),
        }
    }
}
