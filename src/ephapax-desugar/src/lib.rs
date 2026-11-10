#![forbid(unsafe_code)]
// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use ephapax_surface::{
    ConstructorDef, DataDecl, MatchArm, Pattern, Span, SurfaceDecl, SurfaceExpr, SurfaceExprKind,
    SurfaceExternItem, SurfaceModule, SurfaceTy, SurfaceVisibility,
};
use ephapax_syntax::{BaseTy, Decl, Expr, ExprKind, ExternItem, Literal, Module, Ty, Visibility};
use smol_str::SmolStr;
use thiserror::Error;

fn lower_visibility(v: SurfaceVisibility) -> Visibility {
    match v {
        SurfaceVisibility::Public => Visibility::Public,
        SurfaceVisibility::Private => Visibility::Private,
    }
}

/// The qualifier name of a `base.member` access, if `base` is a bare
/// module name — a `Var(m)` (lower-case module) or a nullary
/// `Construct { ctor: m }` (upper-case module). Anything else (a value,
/// a call result, …) has no module qualifier.
fn module_qualifier_of(base: &SurfaceExpr) -> Option<SmolStr> {
    match &base.kind {
        SurfaceExprKind::Var(v) => Some(v.clone()),
        SurfaceExprKind::Construct { ctor, args } if args.is_empty() => Some(ctor.clone()),
        _ => None,
    }
}

/// The last `/`- or `.`-separated segment of an import path
/// (`lib/math` → `math`, `Foo.Bar` → `Bar`, `Coproc` → `Coproc`). This is
/// the name a `M.member` qualifier must use.
fn last_segment(path: &str) -> SmolStr {
    path.rsplit(['/', '.']).next().unwrap_or(path).into()
}

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

    #[error("type arguments need the name of a generic function before them, as in `id[I32](3)`")]
    TypeArgumentsOnExpression,

    /// A `match` with a guard goes to the core `match`, which has no
    /// form for a constructor inside another pattern.
    #[error(
        "a match with a guard cannot have the constructor pattern `{ctor}` inside another pattern"
    )]
    GuardWithNestedConstructor { ctor: String },

    #[error("qualified access `{qualifier}.{member}`: `{qualifier}` is not an imported module (record field access is not yet supported)")]
    QualifiedAccessUnknownModule { qualifier: String, member: String },

    #[error("member access on a non-module expression is not supported (only `Module.member` qualified access)")]
    FieldAccessOnNonModule,

    /// A `data` declaration (or `type` alias) refers to itself. The core
    /// has no recursive types: the binary-sum encoding expands every
    /// named type structurally, so a self-reference would expand forever
    /// (probe `rec1` used to abort with a stack overflow).
    #[error("recursive type `{name}` is not supported: the core type language has no recursive types (expansion cycle: {cycle})")]
    RecursiveType { name: String, cycle: String },
}

// =========================================================================
// Data Registry
// =========================================================================

/// Information about a single constructor within a data type.
#[derive(Debug, Clone)]
struct ConstructorInfo {
    /// Index of this constructor in the data declaration (0-based).
    index: usize,
    /// Payload types (empty for nullary constructors).
    fields: Vec<SurfaceTy>,
    /// The data type this constructor belongs to, by its name in `home`.
    data_name: SmolStr,
    /// Key of the module that declares the data type.
    home: SmolStr,
}

/// A data type as its module declares it.
#[derive(Debug, Clone)]
struct DataInfo {
    params: Vec<SmolStr>,
    ctors: Vec<ConstructorDef>,
    /// Key of the module that declares the type. The names in the
    /// fields of `ctors` are names in the scope of that module.
    home: SmolStr,
    /// `pub data`: a module that imports `home` can name the type.
    public: bool,
}

/// The data types and the constructors that one module can name: its
/// own, and the public ones of the modules that it imports.
#[derive(Debug, Clone, Default)]
struct Scope {
    /// Constructor name → info
    constructors: HashMap<SmolStr, ConstructorInfo>,
    /// Data type name → declaration
    types: HashMap<SmolStr, DataInfo>,
}

/// The key of a module in the registry. `Foo.Bar` and `Foo/Bar` name the
/// same module, so an import can spell it either way.
fn module_key(name: &str) -> SmolStr {
    name.replace('.', "/").into()
}

/// Registry of all data declarations encountered during desugaring.
///
/// Maps constructor names to their encoding information. This is built
/// from `DataDecl` nodes and used to desugar `Construct` and `Match`.
/// Each module has its own [`Scope`], as it has for functions: a module
/// names a data type of another module only when it imports that module
/// and the type is `pub`.
#[derive(Debug, Clone, Default)]
pub struct DataRegistry {
    /// Module key → what the module can name. The key is the empty
    /// string for declarations registered with no module.
    scopes: HashMap<SmolStr, Scope>,
    /// Names declared via `extern "abi" { type Foo }` blocks.
    ///
    /// Extern types are nominal and opaque: the desugar pass resolves
    /// `SurfaceTy::Named { name: "Foo", args: [] }` to `Ty::Var("Foo")`
    /// rather than emitting an `UnknownType` error. The type checker
    /// then treats them as rigid type variables that only unify with
    /// themselves (so values of type `Window` cannot be confused with
    /// `IpcChannel`, etc.).
    extern_types: std::collections::HashSet<SmolStr>,
    /// `type Foo = T` aliases — captured in their pre-desugar surface
    /// form so `desugar_named_type` can recursively expand them on
    /// demand. The stored value is whatever the parser produced for the
    /// alias body (record/sum decls already pre-lowered to `Prod`/`Sum`/
    /// `Tuple` by `parse_type_decl`). An alias is visible in each module.
    /// Each entry has the key of the module that declares the alias: the
    /// body expands in the scope of that module, and a module that
    /// declares an alias of the same name gets its own.
    type_aliases: HashMap<SmolStr, Vec<(SmolStr, SurfaceTy)>>,
}

impl DataRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a data declaration of the module `home`.
    pub fn register(&mut self, home: &str, decl: &DataDecl) {
        let scope = self.scopes.entry(home.into()).or_default();
        for (index, ctor) in decl.constructors.iter().enumerate() {
            scope.constructors.insert(
                ctor.name.clone(),
                ConstructorInfo {
                    index,
                    fields: ctor.fields.clone(),
                    data_name: decl.name.clone(),
                    home: home.into(),
                },
            );
        }
        scope.types.insert(
            decl.name.clone(),
            DataInfo {
                params: decl.params.clone(),
                ctors: decl.constructors.clone(),
                home: home.into(),
                public: decl.visibility == SurfaceVisibility::Public,
            },
        );
    }

    /// Bring the public data types that the module `from` declares, with
    /// their constructors, into the scope of the module `into`. A list of
    /// `names` that is not empty limits the import to the types in it.
    /// Returns the names of the imported types.
    fn import(&mut self, into: &str, from: &str, names: &[SmolStr]) -> HashSet<SmolStr> {
        let Some(source) = self.scopes.get(from) else {
            return HashSet::new();
        };
        let mut imported = Scope::default();
        for (name, data) in &source.types {
            if !data.public || data.home != from || !(names.is_empty() || names.contains(name)) {
                continue;
            }
            for ctor in &data.ctors {
                // A later data type of `from` can have a constructor of
                // the same name: the constructor is then not of `name`.
                let info = source.constructors.get(&ctor.name);
                if let Some(info) = info.filter(|i| i.home == from && i.data_name == *name) {
                    imported
                        .constructors
                        .insert(ctor.name.clone(), info.clone());
                }
            }
            imported.types.insert(name.clone(), data.clone());
        }
        let types = imported.types.keys().cloned().collect();
        let scope = self.scopes.entry(into.into()).or_default();
        scope.constructors.extend(imported.constructors);
        scope.types.extend(imported.types);
        types
    }

    /// Register an opaque extern type name (from
    /// `extern "abi" { type Foo }`).
    pub fn register_extern_type(&mut self, name: &SmolStr) {
        self.extern_types.insert(name.clone());
    }

    /// Register a `type Foo = T` alias of the module `home` in surface
    /// form. Lookups in `desugar_named_type` find the entry and
    /// recursively desugar it.
    pub fn register_type_alias(&mut self, home: &str, name: SmolStr, ty: SurfaceTy) {
        let entries = self.type_aliases.entry(name).or_default();
        entries.retain(|(module, _)| module != home);
        entries.push((home.into(), ty));
    }

    /// The alias `name` as the module `scope` sees it, with the key of
    /// the module that declares it: the alias of `scope`, or else the
    /// alias that was registered last.
    fn lookup_type_alias(&self, scope: &str, name: &str) -> Option<&(SmolStr, SurfaceTy)> {
        let entries = self.type_aliases.get(name)?;
        entries
            .iter()
            .find(|(module, _)| module == scope)
            .or(entries.last())
    }

    /// Look up a constructor by its name in the module `scope`.
    fn get_ctor(&self, scope: &str, name: &str) -> Option<&ConstructorInfo> {
        self.scopes.get(scope)?.constructors.get(name)
    }

    /// Look up a data type by its name in the module `scope`.
    fn get_type_ctors(&self, scope: &str, name: &str) -> Option<&DataInfo> {
        self.scopes.get(scope)?.types.get(name)
    }

    /// Is this name a registered extern (opaque) type?
    fn is_extern_type(&self, name: &str) -> bool {
        self.extern_types.contains(name)
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
    /// Last-segment names of the importer's modules (e.g. `math` for
    /// `import lib/math`), used to recognise a `M.member` qualifier as a
    /// module reference at desugar time. Reset per-module by
    /// [`Desugarer::desugar_module`].
    module_qualifiers: HashSet<SmolStr>,
    /// Named types currently being expanded by `desugar_named_type`,
    /// innermost last, each with the key of the module that declares it.
    /// Re-entering one is a recursive type.
    expanding: RefCell<Vec<(SmolStr, SmolStr)>>,
    /// Key of the module whose scope gives a name its meaning: the module
    /// being desugared, or, while the body of a named type expands, the
    /// module that declares that type.
    scope: RefCell<SmolStr>,
    /// The type parameters of the function being desugared. In its
    /// signature and body such a name is a type variable, also when it
    /// starts with an upper-case letter (`fn id<T>(x: T): T`).
    fn_type_params: Vec<SmolStr>,
}

impl Desugarer {
    /// Create a new desugarer with an empty data registry.
    pub fn new() -> Self {
        Self {
            registry: DataRegistry::new(),
            module_qualifiers: HashSet::new(),
            expanding: RefCell::new(Vec::new()),
            scope: RefCell::default(),
            fn_type_params: Vec::new(),
        }
    }

    /// Create a new desugarer with a pre-populated registry.
    pub fn with_registry(registry: DataRegistry) -> Self {
        Self {
            registry,
            module_qualifiers: HashSet::new(),
            expanding: RefCell::new(Vec::new()),
            scope: RefCell::default(),
            fn_type_params: Vec::new(),
        }
    }

    /// The constructor `name` in the current scope.
    fn ctor(&self, name: &str) -> Result<&ConstructorInfo, DesugarError> {
        self.registry
            .get_ctor(&self.scope.borrow(), name)
            .ok_or_else(|| DesugarError::UnknownConstructor {
                ctor: name.to_string(),
            })
    }

    /// The constructors of the data type of the constructor `info`.
    fn ctors_of(&self, info: &ConstructorInfo) -> Result<Vec<ConstructorDef>, DesugarError> {
        self.registry
            .get_type_ctors(&info.home, &info.data_name)
            .map(|data| data.ctors.clone())
            .ok_or_else(|| DesugarError::UnknownType {
                name: info.data_name.to_string(),
            })
    }

    /// Run `f` with the names of the module `home` in scope: the names
    /// in the body of a type are names of the module that declares it.
    fn in_scope<T>(&self, home: &SmolStr, f: impl FnOnce(&Self) -> T) -> T {
        let outer = self.scope.replace(home.clone());
        let result = f(self);
        self.scope.replace(outer);
        result
    }

    /// Desugar a complete surface module to a core module.
    ///
    /// First pass: collect all data declarations into the registry.
    /// Second pass: desugar all declarations.
    pub fn desugar_module(&mut self, module: &SurfaceModule) -> Result<Module, DesugarError> {
        // Record this module's import qualifiers (the last path segment of
        // each `import`), so qualified `M.member` access resolves against
        // them. Reset per module — qualifiers are not inherited.
        self.module_qualifiers = module
            .imports
            .iter()
            .map(|i| last_segment(i.module.as_str()))
            .collect();

        // The public data types of each imported module, in the order of
        // the imports: a later one shadows an earlier one, and a
        // declaration of this module shadows both.
        let key = module_key(&module.name);
        // The imports of the core module: the type checker reads each
        // name in an import list as a function, so the list keeps only
        // the names that are not data types. An import that names only
        // data types imports no function.
        let mut imports = Vec::with_capacity(module.imports.len());
        for import in &module.imports {
            let types = self
                .registry
                .import(&key, &module_key(&import.module), &import.names);
            let mut import = import.clone();
            let listed = !import.names.is_empty();
            import.names.retain(|name| !types.contains(name));
            // An empty list is each public name of the module.
            if !(listed && import.names.is_empty()) {
                imports.push(import);
            }
        }
        self.scope.replace(key.clone());

        // First pass: register all data types and extern types
        for decl in &module.decls {
            match decl {
                SurfaceDecl::Data(data) => {
                    self.registry.register(&key, data);
                }
                SurfaceDecl::Extern { items, .. } => {
                    for item in items {
                        if let SurfaceExternItem::Type { name } = item {
                            self.registry.register_extern_type(name);
                        }
                    }
                }
                SurfaceDecl::Type { name, ty, .. } => {
                    self.registry
                        .register_type_alias(&key, name.clone(), ty.clone());
                }
                _ => {}
            }
        }

        // Second pass: desugar declarations
        let mut core_decls = Vec::new();
        for decl in &module.decls {
            match decl {
                SurfaceDecl::Fn {
                    name,
                    visibility,
                    type_params,
                    params,
                    ret_ty,
                    body,
                } => {
                    self.fn_type_params.clone_from(type_params);
                    let core_params: Vec<_> = params
                        .iter()
                        .map(|(n, t)| Ok((n.clone(), self.desugar_ty(t)?)))
                        .collect::<Result<_, DesugarError>>()?;
                    let core_ret = self.desugar_ty(ret_ty)?;
                    let core_body = self.desugar_expr(body)?;
                    self.fn_type_params.clear();
                    core_decls.push(Decl::Fn {
                        name: name.clone(),
                        visibility: lower_visibility(*visibility),
                        type_params: type_params.clone(),
                        params: core_params,
                        ret_ty: core_ret,
                        body: core_body,
                    });
                }
                SurfaceDecl::Type {
                    name,
                    visibility,
                    ty,
                } => {
                    core_decls.push(Decl::Type {
                        name: name.clone(),
                        visibility: lower_visibility(*visibility),
                        ty: self.desugar_ty(ty)?,
                    });
                }
                // Data declarations are consumed by the registry, not emitted
                // as core declarations. The type information lives in the
                // registry and is used to desugar Construct/Match nodes.
                SurfaceDecl::Data(_) => {}
                // Extern blocks lower their items' surface types to core
                // types and keep them as `Decl::Extern`. The type checker
                // and codegen pick them up from there. No body to desugar.
                SurfaceDecl::Extern { abi, items, .. } => {
                    let mut core_items: Vec<ExternItem> = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            SurfaceExternItem::Type { name } => {
                                core_items.push(ExternItem::Type { name: name.clone() });
                            }
                            SurfaceExternItem::Fn {
                                name,
                                params,
                                ret_ty,
                            } => {
                                let core_params: Vec<(SmolStr, Ty)> = params
                                    .iter()
                                    .map(|(n, t)| Ok((n.clone(), self.desugar_ty(t)?)))
                                    .collect::<Result<_, DesugarError>>()?;
                                let core_ret = self.desugar_ty(ret_ty)?;
                                core_items.push(ExternItem::Fn {
                                    name: name.clone(),
                                    params: core_params,
                                    ret_ty: core_ret,
                                });
                            }
                        }
                    }
                    core_decls.push(Decl::Extern {
                        abi: abi.clone(),
                        items: core_items,
                    });
                }
            }
        }

        Ok(Module {
            name: module.name.clone(),
            imports,
            decls: core_decls,
        })
    }

    /// Desugar a single expression.
    pub fn desugar_expr(&self, expr: &SurfaceExpr) -> Result<Expr, DesugarError> {
        let span = expr.span;
        let kind = match &expr.kind {
            // === Pass-through nodes (structural recursion) ===
            SurfaceExprKind::Lit(lit) => match lit {
                // Bare string literals (`"hello"` written inline) lower
                // to a `StringNew` allocating in the synthetic `_`
                // region — the wildcard region the typechecker uses for
                // inferred String types (see check_string_new).
                Literal::String(s) => ExprKind::StringNew {
                    region: SmolStr::new("_"),
                    value: s.clone(),
                },
                _ => ExprKind::Lit(lit.clone()),
            },
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

            SurfaceExprKind::App { func, arg } => {
                if let Some((ctor, args)) = self.qualified_ctor_call(expr) {
                    return self.desugar_construct(ctor, &args, span);
                }
                ExprKind::App {
                    func: Box::new(self.desugar_expr(func)?),
                    arg: Box::new(self.desugar_expr(arg)?),
                }
            }

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

            SurfaceExprKind::Borrow { inner, mutable } => ExprKind::Borrow {
                inner: Box::new(self.desugar_expr(inner)?),
                mutable: *mutable,
            },
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
            SurfaceExprKind::TypeApp { func, type_args } => {
                let func = self.desugar_expr(func)?;
                match (&type_args[..], func.kind) {
                    // `xs[i](3)`: a lower-case name is a type only as a
                    // type parameter of this function. Any other name
                    // is a variable, and the brackets are an index.
                    ([SurfaceTy::Var(v)], list) if !self.fn_type_params.contains(v) => {
                        ExprKind::ListIndex {
                            list: Box::new(Expr::new(list, func.span)),
                            index: Box::new(Expr::new(ExprKind::Var(v.clone()), span)),
                        }
                    }
                    (_, ExprKind::Var(name)) => ExprKind::TypeApp {
                        name,
                        type_args: type_args
                            .iter()
                            .map(|ty| self.desugar_ty(ty))
                            .collect::<Result<_, _>>()?,
                    },
                    _ => return Err(DesugarError::TypeArgumentsOnExpression),
                }
            }
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

            SurfaceExprKind::FieldAccess { base, field } => {
                return self.desugar_field_access(base, field, span);
            }
        };

        Ok(Expr::new(kind, span))
    }

    /// The constructor and the arguments of `M.Ctor(a, b)`, if `expr` is
    /// such a call on an imported module. The parser gives the call as
    /// `App(App(M.Ctor, a), b)`, and `M.Ctor()` as `App(M.Ctor, ())`.
    fn qualified_ctor_call<'e>(
        &self,
        expr: &'e SurfaceExpr,
    ) -> Option<(&'e SmolStr, Vec<SurfaceExpr>)> {
        let mut args = Vec::new();
        let mut head = expr;
        while let SurfaceExprKind::App { func, arg } = &head.kind {
            args.push(arg.as_ref().clone());
            head = func;
        }
        let SurfaceExprKind::FieldAccess { base, field } = &head.kind else {
            return None;
        };
        let imported =
            module_qualifier_of(base).is_some_and(|q| self.module_qualifiers.contains(&q));
        if !imported || !field.starts_with(|c: char| c.is_ascii_uppercase()) {
            return None;
        }
        args.reverse();
        let nullary = self.ctor(field).is_ok_and(|info| info.fields.is_empty());
        if nullary
            && matches!(
                args[..],
                [SurfaceExpr {
                    kind: SurfaceExprKind::Lit(Literal::Unit),
                    ..
                }]
            )
        {
            args.clear();
        }
        Some((field, args))
    }

    /// Desugar qualified module-member access `M.member`.
    ///
    /// `M` must be an imported module (matched by the last segment of its
    /// import path); phase-I import resolution has already made `M`'s
    /// public items visible in the importer's shared scope, so the member
    /// resolves *unqualified*: an upper-case `member` is a constructor
    /// (`Construct`), otherwise a function / value reference (`Var`).
    /// Record field access on a value is not yet supported.
    fn desugar_field_access(
        &self,
        base: &SurfaceExpr,
        field: &SmolStr,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let qualifier = module_qualifier_of(base).ok_or(DesugarError::FieldAccessOnNonModule)?;
        if !self.module_qualifiers.contains(&qualifier) {
            return Err(DesugarError::QualifiedAccessUnknownModule {
                qualifier: qualifier.to_string(),
                member: field.to_string(),
            });
        }
        let resolved = if field.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            SurfaceExpr::new(
                SurfaceExprKind::Construct {
                    ctor: field.clone(),
                    args: Vec::new(),
                },
                span,
            )
        } else {
            SurfaceExpr::new(SurfaceExprKind::Var(field.clone()), span)
        };
        self.desugar_expr(&resolved)
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
            SurfaceTy::Borrow { inner, mutable } => Ok(Ty::Borrow {
                inner: Box::new(self.desugar_ty(inner)?),
                mutable: *mutable,
            }),
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
    ///
    /// **Extern types** (registered via `extern "abi" { type Foo }`) are
    /// nominal and opaque — they resolve to `Ty::Var(name)` regardless
    /// of any args. Type arguments on extern names are accepted but
    /// ignored: extern types currently have no parameter abstraction
    /// (parameterised externs are a phase-2C concern, post wasm
    /// codegen). Two distinct extern types `Window` and `IpcChannel`
    /// produce two distinct `Ty::Var` rigids that never unify.
    fn desugar_named_type(&self, name: &SmolStr, args: &[SurfaceTy]) -> Result<Ty, DesugarError> {
        // A type parameter of the enclosing function shadows every other
        // meaning of the name.
        if self.fn_type_params.contains(name) {
            if !args.is_empty() {
                return Err(DesugarError::TypeArityMismatch {
                    name: name.to_string(),
                    expected: 0,
                    got: args.len(),
                });
            }
            return Ok(Ty::Var(name.clone()));
        }
        // Built-in type aliases that aren't (yet) keywords in the lexer.
        // `Unit` is the type-position spelling of the literal `()`;
        // bridge.eph and other ML-adjacent corpora write it freely.
        if name.as_str() == "Unit" {
            if !args.is_empty() {
                return Err(DesugarError::TypeArityMismatch {
                    name: name.to_string(),
                    expected: 0,
                    got: args.len(),
                });
            }
            return Ok(Ty::Base(BaseTy::Unit));
        }
        // `Bytes` is the conventional name for a host-managed buffer.
        // Until the stdlib publishes a real `Bytes` ADT, treat it as an
        // I32 handle (the wasm host passes pointer/length pairs across
        // `__ffi`; for direct extern-fn signatures the handle is enough).
        if name.as_str() == "Bytes" {
            if !args.is_empty() {
                return Err(DesugarError::TypeArityMismatch {
                    name: name.to_string(),
                    expected: 0,
                    got: args.len(),
                });
            }
            return Ok(Ty::Base(BaseTy::I32));
        }

        if self.registry.is_extern_type(name.as_str()) {
            return Ok(Ty::Var(name.clone()));
        }

        // `type Foo = T` aliases — recursively desugar the stored surface
        // form. Aliases are monomorphic here (parameterised aliases would
        // carry their args via the body).
        let alias = self
            .registry
            .lookup_type_alias(&self.scope.borrow(), name.as_str())
            .cloned();
        if let Some((home, aliased)) = alias {
            if !args.is_empty() {
                return Err(DesugarError::TypeArityMismatch {
                    name: name.to_string(),
                    expected: 0,
                    got: args.len(),
                });
            }
            return self.with_expansion(name, &home, |this| this.desugar_ty(&aliased));
        }

        let DataInfo {
            params,
            ctors,
            home,
            ..
        } = self
            .registry
            .get_type_ctors(&self.scope.borrow(), name.as_str())
            .ok_or_else(|| DesugarError::UnknownType {
                name: name.to_string(),
            })?;

        if params.len() != args.len() {
            return Err(DesugarError::TypeArityMismatch {
                name: name.to_string(),
                expected: params.len(),
                got: args.len(),
            });
        }

        // Build substitution map: type param → concrete type
        let core_args = args
            .iter()
            .map(|arg| self.desugar_ty(arg))
            .collect::<Result<Vec<_>, _>>()?;
        let subst: HashMap<&SmolStr, &Ty> = params.iter().zip(core_args.iter()).collect();

        // Build right-nested sum from constructor field types
        self.with_expansion(name, home, |this| this.build_sum_type(ctors, &subst))
    }

    /// Run `f` with the named type `name` of the module `home` pushed on
    /// the expansion stack, and with the names of `home` in scope. Fails
    /// with [`DesugarError::RecursiveType`] if the same declaration is
    /// already being expanded, including non-regular recursion with
    /// changing arguments. Arguments are elaborated before entering the
    /// declaration, so finite nested applications remain valid. Errors
    /// propagate after removing this expansion from the stack.
    fn with_expansion<T>(
        &self,
        name: &SmolStr,
        home: &SmolStr,
        f: impl FnOnce(&Self) -> Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        let key = (home.clone(), name.clone());
        {
            let stack = self.expanding.borrow();
            if stack.contains(&key) {
                let mut cycle: Vec<String> = stack.iter().map(|(_, n)| n.to_string()).collect();
                cycle.push(name.to_string());
                return Err(DesugarError::RecursiveType {
                    name: name.to_string(),
                    cycle: cycle.join(" -> "),
                });
            }
        }
        self.expanding.borrow_mut().push(key);
        let result = self.in_scope(home, f);
        self.expanding.borrow_mut().pop();
        result
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
        subst: &HashMap<&SmolStr, &Ty>,
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
        subst: &HashMap<&SmolStr, &Ty>,
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
        subst: &HashMap<&SmolStr, &Ty>,
    ) -> Result<Ty, DesugarError> {
        match ty {
            SurfaceTy::Var(v) => {
                if let Some(replacement) = subst.get(v) {
                    Ok((*replacement).clone())
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
        let info = self.ctor(ctor)?.clone();

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
        let empty_subst: HashMap<&SmolStr, &Ty> = HashMap::new();
        let ctors = self.ctors_of(&info)?;

        // Wrap in inl/inr chain based on index. The types of the other
        // constructors are names of the module that declares the type.
        self.in_scope(&info.home, |this| {
            this.wrap_injection(payload, info.index, &ctors, &empty_subst, span)
        })
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
        subst: &HashMap<&SmolStr, &Ty>,
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

        // Fast path: a single-arm match whose pattern is not a constructor
        // is structural destructuring (typically from a tuple-binder
        // `let (a, b) = e in body` lowered at parse time). Delegate to
        // `bind_single_pattern`, which handles `Pair`, `Wildcard`, `Var`,
        // etc. directly without going through the sum-type case tree.
        if arms.len() == 1
            && !matches!(arms[0].pattern, Pattern::Constructor { .. })
            && arms[0].guard.is_none()
        {
            let body = self.desugar_expr(&arms[0].body)?;
            return self.bind_single_pattern(&core_scrutinee, &arms[0].pattern, body, span);
        }

        // A guard, and no constructor pattern at the top of an arm: the
        // core `match` tries the arms in order and honours each guard.
        let guarded = arms.iter().any(|a| a.guard.is_some());
        if guarded
            && !arms
                .iter()
                .any(|a| matches!(a.pattern, Pattern::Constructor { .. }))
        {
            let patterns = arms.iter().map(|a| a.pattern.clone()).collect();
            return self.guarded_match(core_scrutinee, arms.iter(), patterns, span);
        }

        // Match on a literal-typed scrutinee (`match n of | 0 => a | 1 =>
        // b | _ => c end`). All arms are Literal / Wildcard / Var, no
        // constructor — desugar to nested `if scrutinee == lit then arm
        // else next` ending in the wildcard/var branch.
        let all_literal_or_wildcard = arms.iter().all(|a| {
            matches!(
                a.pattern,
                Pattern::Literal(_) | Pattern::Wildcard | Pattern::Var(_)
            ) && a.guard.is_none()
        });
        if all_literal_or_wildcard {
            // Default: the last Wildcard/Var arm, or unit if none.
            let mut default = Expr::new(ExprKind::Lit(Literal::Unit), span);
            for arm in arms.iter().rev() {
                if matches!(arm.pattern, Pattern::Wildcard | Pattern::Var(_)) {
                    default = self.desugar_expr(&arm.body)?;
                    break;
                }
            }
            // Walk literal arms in reverse, wrapping each in an if.
            let mut acc = default;
            for arm in arms.iter().rev() {
                if let Pattern::Literal(lit) = &arm.pattern {
                    let arm_body = self.desugar_expr(&arm.body)?;
                    let cond = Expr::new(
                        ExprKind::BinOp {
                            op: ephapax_syntax::BinOp::Eq,
                            left: Box::new(core_scrutinee.clone()),
                            right: Box::new(Expr::new(ExprKind::Lit(lit.clone()), span)),
                        },
                        span,
                    );
                    acc = Expr::new(
                        ExprKind::If {
                            cond: Box::new(cond),
                            then_branch: Box::new(arm_body),
                            else_branch: Box::new(acc),
                        },
                        span,
                    );
                }
            }
            return Ok(acc);
        }

        // The data type, from the first constructor pattern.
        let first_ctor = arms
            .iter()
            .find_map(|arm| match &arm.pattern {
                Pattern::Constructor { ctor, .. } => Some(ctor),
                _ => None,
            })
            .ok_or(DesugarError::EmptyMatch)?;
        let ctors = self.ctors_of(self.ctor(first_ctor)?)?;

        // The constructor index of each arm; `None` for an arm that takes
        // every constructor. A literal or a tuple pattern at the top of
        // a match on a data type is taken as a wildcard.
        let mut indexed: Vec<(Option<usize>, &MatchArm)> = Vec::with_capacity(arms.len());
        for arm in arms {
            let index = match &arm.pattern {
                Pattern::Constructor { ctor, .. } => Some(self.ctor(ctor)?.index),
                _ => None,
            };
            indexed.push((index, arm));
        }

        // The arms that can take constructor `i`, in the order to try.
        // With a guard in the match: each arm for `i`, in source order.
        // With no guard, one arm: the last arm for `i`, or else the last
        // arm for every constructor.
        let chains: Vec<Vec<&MatchArm>> = (0..ctors.len())
            .map(|i| {
                if guarded {
                    return indexed
                        .iter()
                        .filter(|(index, _)| index.is_none_or(|n| n == i))
                        .map(|(_, arm)| *arm)
                        .collect();
                }
                let last = |want: Option<usize>| {
                    indexed
                        .iter()
                        .rev()
                        .find(|(index, _)| *index == want)
                        .map(|(_, arm)| *arm)
                };
                last(Some(i)).or_else(|| last(None)).into_iter().collect()
            })
            .collect();

        // Generate the nested case tree
        self.build_case_tree(&core_scrutinee, &ctors, &chains, 0, span)
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
        chains: &[Vec<&MatchArm>],
        base_index: usize,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let chain = &chains[base_index];
        match ctors.len() {
            0 => unreachable!("empty constructor list"),

            // Last (or only) constructor: no case needed, the scrutinee
            // is the payload (no inl/inr wrapper).
            1 => self.build_arm_chain(scrutinee, &ctors[0], chain, span),

            // Two or more constructors — generate case
            _ => {
                // Variable name for the left (inl) payload. More than one
                // arm can read it, so it does not take the name of a
                // variable of one arm: that name would hide an outer
                // variable in the other arms.
                let left_var = match chain[..] {
                    [arm] => self.fresh_var_for_arm(arm, &ctors[0]),
                    _ => format!("__{}", ctors[0].name.to_lowercase()).into(),
                };
                let left_body = self.build_arm_chain(
                    &Expr::new(ExprKind::Var(left_var.clone()), span),
                    &ctors[0],
                    chain,
                    span,
                )?;

                // Variable name for the right (inr) — the "rest" of the sum
                let rest_var: SmolStr = format!("__rest_{}", base_index).into();
                let rest_scrutinee = Expr::new(ExprKind::Var(rest_var.clone()), span);
                let right_body = self.build_case_tree(
                    &rest_scrutinee,
                    &ctors[1..],
                    chains,
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

    /// The code for one constructor: `chain` has the arms to try on its
    /// payload, in order. A chain where each arm has a guard does not
    /// cover the constructor. For a longer chain, the type checker finds
    /// if the patterns cover the payload.
    fn build_arm_chain(
        &self,
        payload: &Expr,
        ctor: &ConstructorDef,
        chain: &[&MatchArm],
        span: Span,
    ) -> Result<Expr, DesugarError> {
        match chain {
            [arm] if arm.guard.is_none() => self.build_arm_body_inner(payload, ctor, arm, span),
            _ if chain.iter().any(|arm| arm.guard.is_none()) => {
                // A pattern on the constructor is a pattern on its
                // payload: `()`, the one field, or a right-nested pair.
                let patterns = chain
                    .iter()
                    .map(|arm| match &arm.pattern {
                        Pattern::Constructor { args, .. } => args
                            .iter()
                            .rev()
                            .cloned()
                            .reduce(|rest, p| Pattern::Pair(Box::new(p), Box::new(rest)))
                            .unwrap_or(Pattern::Unit),
                        Pattern::Var(v) => Pattern::Var(v.clone()),
                        _ => Pattern::Wildcard,
                    })
                    .collect();
                self.guarded_match(payload.clone(), chain.iter().copied(), patterns, span)
            }
            _ => Err(DesugarError::NonExhaustive {
                ctor: ctor.name.to_string(),
            }),
        }
    }

    /// A core `match` with one arm for each of `arms`, on `patterns`
    /// (one for each arm). The core `match` tries the arms in order, and
    /// an arm with a false guard gives the value to the next arm.
    fn guarded_match<'a>(
        &self,
        scrutinee: Expr,
        arms: impl Iterator<Item = &'a MatchArm>,
        patterns: Vec<Pattern>,
        span: Span,
    ) -> Result<Expr, DesugarError> {
        let arms = arms
            .zip(&patterns)
            .map(|(arm, pattern)| {
                Ok(ephapax_syntax::MatchArm {
                    pattern: Self::core_pattern(pattern)?,
                    guard: match &arm.guard {
                        Some(guard) => Some(Box::new(self.desugar_expr(guard)?)),
                        None => None,
                    },
                    body: self.desugar_expr(&arm.body)?,
                })
            })
            .collect::<Result<_, DesugarError>>()?;
        Ok(Expr::new(
            ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            span,
        ))
    }

    /// The core form of a pattern that has no constructor pattern in it.
    fn core_pattern(pattern: &Pattern) -> Result<ephapax_syntax::Pattern, DesugarError> {
        use ephapax_syntax::Pattern as CorePattern;
        let all = |ps: &[Pattern]| ps.iter().map(Self::core_pattern).collect::<Result<_, _>>();
        Ok(match pattern {
            Pattern::Wildcard => CorePattern::Wildcard,
            Pattern::Var(v) => CorePattern::Var(v.clone()),
            Pattern::Unit => CorePattern::Unit,
            Pattern::Literal(lit) => CorePattern::Literal(lit.clone()),
            Pattern::Pair(l, r) => CorePattern::Pair(
                Box::new(Self::core_pattern(l)?),
                Box::new(Self::core_pattern(r)?),
            ),
            Pattern::Tuple(elements) => CorePattern::Tuple(all(elements)?),
            Pattern::Constructor { ctor, .. } => {
                return Err(DesugarError::GuardWithNestedConstructor {
                    ctor: ctor.to_string(),
                })
            }
        })
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
    /// For `Pair(a, b)` with payload `p`: `match p { (a, b) => body }`.
    /// Multiple irrefutable fields destructure a right-nested product in one
    /// match; other field patterns use projections. No patterns returns `body`.
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
            // The payload is a right-nested product: destructure it with
            // one core `match` on the equivalent right-nested pair
            // pattern, so the payload is consumed once (see
            // `bind_single_pattern`).
            _ if patterns.iter().all(Self::is_irrefutable_pair_pattern) => {
                let mut nested = patterns[patterns.len() - 1].clone();
                for p in patterns[..patterns.len() - 1].iter().rev() {
                    nested = Pattern::Pair(Box::new(p.clone()), Box::new(nested));
                }
                self.bind_single_pattern(payload, &nested, body, span)
            }
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

    /// Wrap `body` with bindings extracted from `value` by `pattern`.
    ///
    /// Irrefutable pair patterns use one core match; other pairs and tuples
    /// are destructured recursively. Wildcards, unit, constructors and literals
    /// return `body` without adding bindings or checking the pattern.
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
            // A pair pattern built only from pairs, variables, wildcards
            // and unit lowers to a one-arm core `match`. The core checker
            // then consumes the scrutinee exactly once, binds each
            // component, and rejects a wildcard over a linear component
            // (v2 plan E0). The `fst`/`snd` lowering below reads the
            // scrutinee twice, which a linear pair does not allow.
            Pattern::Pair(..) if Self::is_irrefutable_pair_pattern(pattern) => Ok(Expr::new(
                ExprKind::Match {
                    scrutinee: Box::new(value.clone()),
                    arms: vec![ephapax_syntax::MatchArm {
                        pattern: Self::core_pattern(pattern)?,
                        guard: None,
                        body,
                    }],
                },
                span,
            )),
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

    /// Whether `pattern` is built only from pairs, variables, wildcards
    /// and unit (so it is irrefutable and has a direct core form).
    fn is_irrefutable_pair_pattern(pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Var(_) | Pattern::Wildcard | Pattern::Unit => true,
            Pattern::Pair(l, r) => {
                Self::is_irrefutable_pair_pattern(l) && Self::is_irrefutable_pair_pattern(r)
            }
            Pattern::Tuple(_) | Pattern::Constructor { .. } | Pattern::Literal(_) => false,
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
        SurfaceExpr, SurfaceExprKind, SurfaceExternItem, SurfaceModule, SurfaceTy,
    };

    fn se(kind: SurfaceExprKind) -> SurfaceExpr {
        SurfaceExpr::dummy(kind)
    }

    fn option_decl() -> DataDecl {
        DataDecl {
            name: "Option".into(),
            visibility: Default::default(),
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
            visibility: Default::default(),
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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &color_decl());

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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &color_decl());

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
        ds.registry.register("", &color_decl());

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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &option_decl());

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
        ds.registry.register("", &color_decl());

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
        ds.registry.register("", &color_decl());

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
        ds.registry.register("", &color_decl());

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
            imports: vec![],
            decls: vec![
                SurfaceDecl::Data(option_decl()),
                SurfaceDecl::Fn {
                    name: "unwrap_or".into(),
                    visibility: SurfaceVisibility::Private,
                    type_params: vec![],
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
            imports: vec![],
            decls: vec![
                SurfaceDecl::Data(DataDecl {
                    name: "Option".into(),
                    visibility: Default::default(),
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
                    visibility: SurfaceVisibility::Private,
                    type_params: vec![],
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
            imports: vec![],
            decls: vec![
                SurfaceDecl::Data(DataDecl {
                    name: "Option".into(),
                    visibility: Default::default(),
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
                    visibility: SurfaceVisibility::Private,
                    type_params: vec![],
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

    /// An extern type declared inside `extern "abi" { type Foo }`
    /// becomes a nominal opaque `Ty::Var("Foo")` when referenced from
    /// an extern fn's signature. Two distinct extern types produce
    /// two distinct `Ty::Var` names so the type checker keeps them
    /// apart.
    #[test]
    fn desugar_extern_types_resolve_to_ty_var() {
        let module = SurfaceModule {
            name: "test".into(),
            imports: vec![],
            decls: vec![SurfaceDecl::Extern {
                abi: "gossamer".to_string(),
                items: vec![
                    SurfaceExternItem::Type {
                        name: "Window".into(),
                    },
                    SurfaceExternItem::Type {
                        name: "IpcChannel".into(),
                    },
                    SurfaceExternItem::Fn {
                        name: "open_window".into(),
                        params: vec![],
                        ret_ty: SurfaceTy::Named {
                            name: "Window".into(),
                            args: vec![],
                        },
                    },
                    SurfaceExternItem::Fn {
                        name: "open_ipc".into(),
                        params: vec![],
                        ret_ty: SurfaceTy::Named {
                            name: "IpcChannel".into(),
                            args: vec![],
                        },
                    },
                ],
                span: Span::dummy(),
            }],
        };

        let core = desugar(&module).unwrap();
        assert_eq!(core.decls.len(), 1);
        let Decl::Extern { items, .. } = &core.decls[0] else {
            panic!("expected Decl::Extern");
        };
        // The two fn items end up at indexes 2 and 3 (after the two
        // type items at 0 and 1).
        let ExternItem::Fn {
            ret_ty: window_ret, ..
        } = &items[2]
        else {
            panic!("expected ExternItem::Fn at index 2");
        };
        let ExternItem::Fn {
            ret_ty: ipc_ret, ..
        } = &items[3]
        else {
            panic!("expected ExternItem::Fn at index 3");
        };
        assert_eq!(*window_ret, Ty::Var("Window".into()));
        assert_eq!(*ipc_ret, Ty::Var("IpcChannel".into()));
        assert_ne!(
            window_ret, ipc_ret,
            "distinct nominal types must not be equal"
        );
    }

    /// `SurfaceDecl::Extern` lowers to `Decl::Extern` with item types
    /// converted from `SurfaceTy` to core `Ty`. Phase 2A: the
    /// declaration survives desugar intact; downstream typecheck and
    /// codegen accept it but currently treat it as a no-op (phase 2B
    /// will wire those).
    #[test]
    fn desugar_extern_block() {
        let module = SurfaceModule {
            name: "test".into(),
            imports: vec![],
            decls: vec![SurfaceDecl::Extern {
                abi: "gossamer".to_string(),
                items: vec![
                    SurfaceExternItem::Type {
                        name: "Window".into(),
                    },
                    SurfaceExternItem::Fn {
                        name: "window_open".into(),
                        params: vec![("title".into(), SurfaceTy::String("r".into()))],
                        ret_ty: SurfaceTy::Base(BaseTy::I32),
                    },
                ],
                span: Span::dummy(),
            }],
        };

        let core = desugar(&module).unwrap();
        assert_eq!(core.decls.len(), 1);
        match &core.decls[0] {
            Decl::Extern { abi, items } => {
                assert_eq!(abi, "gossamer");
                assert_eq!(items.len(), 2);
                assert!(matches!(
                    &items[0],
                    ExternItem::Type { name } if name.as_str() == "Window"
                ));
                if let ExternItem::Fn {
                    name,
                    params,
                    ret_ty,
                } = &items[1]
                {
                    assert_eq!(name.as_str(), "window_open");
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0].0.as_str(), "title");
                    assert_eq!(*ret_ty, Ty::Base(BaseTy::I32));
                } else {
                    panic!("expected ExternItem::Fn, got {:?}", items[1]);
                }
            }
            other => panic!("expected Decl::Extern, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod expansion_regressions {
    use super::*;
    fn named(name: &str) -> SurfaceTy {
        SurfaceTy::Named {
            name: name.into(),
            args: vec![],
        }
    }
    #[test]
    fn nested_finite_application_and_nonregular_recursion() {
        let mut registry = DataRegistry::new();
        let data = |name: &str, ctor: &str, field: SurfaceTy| DataDecl {
            name: name.into(),
            visibility: Default::default(),
            params: vec!["a".into()],
            constructors: vec![ConstructorDef {
                name: ctor.into(),
                fields: vec![field],
            }],
            span: Span::dummy(),
        };
        registry.register("", &data("Id", "IdValue", SurfaceTy::Var("a".into())));
        let inner = SurfaceTy::Named {
            name: "Id".into(),
            args: vec![SurfaceTy::Base(BaseTy::I32)],
        };
        let nested = SurfaceTy::Named {
            name: "Id".into(),
            args: vec![inner],
        };
        assert_eq!(
            Desugarer::with_registry(registry.clone())
                .desugar_ty(&nested)
                .unwrap(),
            Ty::Base(BaseTy::I32)
        );
        let grow = SurfaceTy::Named {
            name: "Grow".into(),
            args: vec![SurfaceTy::List(Box::new(SurfaceTy::Var("a".into())))],
        };
        registry.register("", &data("Grow", "More", grow));
        let recursive = SurfaceTy::Named {
            name: "Grow".into(),
            args: vec![SurfaceTy::Base(BaseTy::I32)],
        };
        assert!(matches!(
            Desugarer::with_registry(registry).desugar_ty(&recursive),
            Err(DesugarError::RecursiveType { .. })
        ));
    }
    #[test]
    fn long_finite_alias_chain_and_cycle() {
        let mut registry = DataRegistry::new();
        for i in 0..65 {
            registry.register_type_alias(
                "",
                format!("A{i}").into(),
                if i == 64 {
                    SurfaceTy::Base(BaseTy::I32)
                } else {
                    named(&format!("A{}", i + 1))
                },
            );
        }
        let desugarer = Desugarer::with_registry(registry.clone());
        assert_eq!(
            desugarer.desugar_ty(&named("A0")).unwrap(),
            Ty::Base(BaseTy::I32)
        );
        registry.register_type_alias("", "A64".into(), named("A0"));
        assert!(matches!(
            Desugarer::with_registry(registry).desugar_ty(&named("A0")),
            Err(DesugarError::RecursiveType { .. })
        ));
    }
}
