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

    /// A constructor pattern inside another pattern (`W(Some(x))`). The
    /// lowering has no code for it yet, and it does not take such a
    /// pattern as a wildcard.
    #[error("the constructor pattern `{ctor}` inside another pattern is not supported")]
    NestedConstructorPattern { ctor: String },

    #[error("qualified access `{qualifier}.{member}`: `{qualifier}` is not an imported module (record field access is not yet supported)")]
    QualifiedAccessUnknownModule { qualifier: String, member: String },

    #[error("member access on a non-module expression is not supported (only `Module.member` qualified access)")]
    FieldAccessOnNonModule,

    /// A `type` alias refers to itself, with no `data` type in the cycle.
    /// A recursive type is folded at a constructor, and an alias has none.
    /// (Probe `rec1` used to abort with a stack overflow.)
    #[error("recursive type alias `{name}` is not supported: only a `data` type can refer to itself (expansion cycle: {cycle})")]
    RecursiveAlias { name: String, cycle: String },

    /// The expansion of a named type is too large or too deep. `data`
    /// types that refer to each other become nested recursive types, and
    /// a dense cycle makes them grow fast: 4 types that each refer to
    /// each of the 4 need 3613 bodies, and 5 such types need 8 million.
    #[error("the type `{name}` is too large: its expansion needs more than {MAX_EXPANSIONS} bodies of named types, or nests them more than {MAX_EXPANSION_DEPTH} deep. `data` types that refer to each other in a dense cycle have this effect: use fewer references between them, or 1 `data` type for the cycle")]
    TypeTooLarge { name: String },

    /// A `data` type refers to itself with other type arguments
    /// (`data Grow(a) = More(Grow([a]))`): its expansion does not end.
    #[error("recursive type `{name}` refers to itself with other type arguments, which is not supported (expansion cycle: {cycle})")]
    NonRegularRecursion { name: String, cycle: String },
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

/// A named type as its module declares it.
#[derive(Debug, Clone)]
struct TypeInfo {
    def: TypeDef,
    /// Key of the module that declares the type. The names in `def` are
    /// names in the scope of that module.
    home: SmolStr,
    /// A module that imports `home` can name the type: `pub data`,
    /// `pub type`, and each extern type (as each extern function).
    public: bool,
}

/// What a type name stands for.
#[derive(Debug, Clone)]
enum TypeDef {
    /// `data Foo(a) = A | B(a)`.
    Data {
        params: Vec<SmolStr>,
        ctors: Vec<ConstructorDef>,
    },
    /// `type Foo = T`, with `T` in surface form: `desugar_named_type`
    /// expands it on demand. Record and sum declarations are already
    /// lowered to `Prod`/`Sum`/`Tuple` by `parse_type_decl`.
    Alias(SurfaceTy),
    /// `extern "abi" { type Foo }`: nominal and opaque. It resolves to
    /// `Ty::Var("Foo")`, a rigid type variable that unifies only with
    /// itself, so a `Window` is never an `IpcChannel`.
    Extern,
}

/// The named types and the constructors that one module can name: its
/// own, and the public ones of the modules that it imports.
#[derive(Debug, Clone, Default)]
struct Scope {
    /// Constructor name → info
    constructors: HashMap<SmolStr, ConstructorInfo>,
    /// Type name → declaration. A data type, an alias and an extern
    /// type share the one table: a later declaration of a name shadows
    /// an earlier one of each kind.
    types: HashMap<SmolStr, TypeInfo>,
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
/// names a data type, a `type` alias or an extern type of another module
/// only when it imports that module and the type is public.
#[derive(Debug, Clone, Default)]
pub struct DataRegistry {
    /// Module key → what the module can name. The key is the empty
    /// string for declarations registered with no module.
    scopes: HashMap<SmolStr, Scope>,
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
        let def = TypeDef::Data {
            params: decl.params.clone(),
            ctors: decl.constructors.clone(),
        };
        let public = decl.visibility == SurfaceVisibility::Public;
        self.register_type(home, &decl.name, def, public);
    }

    /// Give the type name `name` its meaning in the module `home`.
    fn register_type(&mut self, home: &str, name: &SmolStr, def: TypeDef, public: bool) {
        let home: SmolStr = home.into();
        let info = TypeInfo {
            def,
            home: home.clone(),
            public,
        };
        let scope = self.scopes.entry(home).or_default();
        scope.types.insert(name.clone(), info);
    }

    /// Bring the public types that the module `from` declares, and the
    /// constructors of its data types, into the scope of the module
    /// `into`. A list of `names` that is not empty limits the import to
    /// the types in it. Returns the names of the imported types.
    fn import(&mut self, into: &str, from: &str, names: &[SmolStr]) -> HashSet<SmolStr> {
        let Some(source) = self.scopes.get(from) else {
            return HashSet::new();
        };
        let mut imported = Scope::default();
        for (name, info) in &source.types {
            if !info.public || info.home != from || !(names.is_empty() || names.contains(name)) {
                continue;
            }
            let TypeDef::Data { ctors, .. } = &info.def else {
                imported.types.insert(name.clone(), info.clone());
                continue;
            };
            for ctor in ctors {
                // A later data type of `from` can have a constructor of
                // the same name: the constructor is then not of `name`.
                let info = source.constructors.get(&ctor.name);
                if let Some(info) = info.filter(|i| i.home == from && i.data_name == *name) {
                    imported
                        .constructors
                        .insert(ctor.name.clone(), info.clone());
                }
            }
            imported.types.insert(name.clone(), info.clone());
        }
        let types = imported.types.keys().cloned().collect();
        let scope = self.scopes.entry(into.into()).or_default();
        scope.constructors.extend(imported.constructors);
        scope.types.extend(imported.types);
        types
    }

    /// Register the opaque type `name` of an extern block of the module
    /// `home`.
    pub fn register_extern_type(&mut self, home: &str, name: &SmolStr) {
        self.register_type(home, name, TypeDef::Extern, true);
    }

    /// Register the alias `type name = ty` of the module `home`. `public`
    /// is `pub type`: a module that imports `home` can name the alias.
    pub fn register_type_alias(&mut self, home: &str, name: SmolStr, ty: SurfaceTy, public: bool) {
        self.register_type(home, &name, TypeDef::Alias(ty), public);
    }

    /// Look up a constructor by its name in the module `scope`.
    fn get_ctor(&self, scope: &str, name: &str) -> Option<&ConstructorInfo> {
        self.scopes.get(scope)?.constructors.get(name)
    }

    /// Look up a type by its name in the module `scope`.
    fn get_type(&self, scope: &str, name: &str) -> Option<&TypeInfo> {
        self.scopes.get(scope)?.types.get(name)
    }
}

// =========================================================================
// Desugarer
// =========================================================================

/// The most bodies of named types that the expansion of 1 type can have
/// ([`DesugarError::TypeTooLarge`]). A cycle of 5 `data` types as in a
/// syntax tree needs fewer than 400.
const MAX_EXPANSIONS: usize = 10_000;

/// The most named types that an expansion can nest. Each one is a level
/// of recursion in this pass and in each later pass over the type: a
/// chain of 700 nested `data` types overflowed the stack.
const MAX_EXPANSION_DEPTH: usize = 256;

/// A named type whose body is being expanded by `desugar_named_type`.
#[derive(Debug, Clone)]
struct Expansion {
    /// Key of the module that declares the type.
    home: SmolStr,
    name: SmolStr,
    /// The type arguments of a `data` type, as core types. `None`: a
    /// `type` alias.
    args: Option<Vec<Ty>>,
    /// The type of each type parameter of a `data` type: the type that a
    /// type variable stands for in its body, at each depth.
    params: HashMap<SmolStr, Ty>,
    /// The body referred to the type itself: the type is recursive.
    recursive: bool,
    /// The type is not a variable for the expansion in progress: a `data`
    /// type that comes before it was entered after it
    /// ([`Desugarer::expand_data`]).
    hidden: bool,
}

/// The variable of the recursive type of the `data` type `name`. A
/// program cannot write this name, so it is not the name of a type
/// parameter or of an extern type.
fn mu_var(name: &str) -> SmolStr {
    format!("#{name}").into()
}

/// `forall p1. .. forall pn. ty`: the annotation `ty` of a constructor,
/// with the type parameters `params` of its `data` type bound. The type
/// checker gives each bound parameter a type that it finds.
fn quantify(ty: Ty, params: &[SmolStr]) -> Ty {
    params.iter().rev().fold(ty, |ty, var| Ty::ForAll {
        var: var.clone(),
        body: Box::new(ty),
    })
}

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
    /// The names of the top-level constants of the module being
    /// desugared. A constant with an upper-case first letter (`let K =
    /// 40`) is read by the parser as a constructor: see `Construct` in
    /// [`Desugarer::desugar_expr`].
    constants: HashSet<SmolStr>,
    /// Named types currently being expanded by `desugar_named_type`,
    /// innermost last. A `data` type that is entered again is a recursive
    /// type (v2 plan rung E9).
    expanding: RefCell<Vec<Expansion>>,
    /// The number of bodies of named types in the expansion in progress,
    /// for [`MAX_EXPANSIONS`].
    expansions: std::cell::Cell<usize>,
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
            constants: HashSet::new(),
            expanding: RefCell::new(Vec::new()),
            expansions: std::cell::Cell::new(0),
            scope: RefCell::default(),
            fn_type_params: Vec::new(),
        }
    }

    /// Create a new desugarer with a pre-populated registry.
    pub fn with_registry(registry: DataRegistry) -> Self {
        Self {
            registry,
            module_qualifiers: HashSet::new(),
            constants: HashSet::new(),
            expanding: RefCell::new(Vec::new()),
            expansions: std::cell::Cell::new(0),
            scope: RefCell::default(),
            fn_type_params: Vec::new(),
        }
    }

    /// The constructor `name` in the current scope. A pattern can name
    /// it as `M.Ctor`: `M` must be an imported module, and the
    /// constructor then resolves as `Ctor` (as `M.Ctor(x)` does in an
    /// expression).
    fn ctor(&self, name: &str) -> Result<&ConstructorInfo, DesugarError> {
        let name = match name.split_once('.') {
            Some((qualifier, member)) if self.module_qualifiers.contains(qualifier) => member,
            Some((qualifier, member)) => {
                return Err(DesugarError::QualifiedAccessUnknownModule {
                    qualifier: qualifier.to_string(),
                    member: member.to_string(),
                })
            }
            None => name,
        };
        self.registry
            .get_ctor(&self.scope.borrow(), name)
            .ok_or_else(|| DesugarError::UnknownConstructor {
                ctor: name.to_string(),
            })
    }

    /// The constructors of the data type of the constructor `info`.
    fn ctors_of(&self, info: &ConstructorInfo) -> Result<Vec<ConstructorDef>, DesugarError> {
        match self.registry.get_type(&info.home, &info.data_name) {
            Some(TypeInfo {
                def: TypeDef::Data { ctors, .. },
                ..
            }) => Ok(ctors.clone()),
            _ => Err(DesugarError::UnknownType {
                name: info.data_name.to_string(),
            }),
        }
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
        self.constants = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                SurfaceDecl::Const { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();

        // The public types of each imported module, in the order of the
        // imports: a later one shadows an earlier one, and a declaration
        // of this module shadows both.
        let key = module_key(&module.name);
        // The imports of the core module: the type checker reads each
        // name in an import list as a function, so the list keeps only
        // the names that are not types. An import that names only types
        // imports no function.
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
                            self.registry.register_extern_type(&key, name);
                        }
                    }
                }
                SurfaceDecl::Type {
                    name,
                    visibility,
                    ty,
                } => {
                    let public = *visibility == SurfaceVisibility::Public;
                    self.registry
                        .register_type_alias(&key, name.clone(), ty.clone(), public);
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
                // A constant keeps its form: the type checker finds its
                // type, and each backend finds its value by its name.
                SurfaceDecl::Const { name, ty, value } => {
                    core_decls.push(Decl::Const {
                        name: name.clone(),
                        ty: ty.as_ref().map(|t| self.desugar_ty(t)).transpose()?,
                        value: self.desugar_expr(value)?,
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
                // The parser reads each name with an upper-case first
                // letter as a constructor. A name that is no constructor
                // in scope, and that is a constant of the module, is that
                // constant, applied to the arguments.
                let scope = self.scope.borrow().clone();
                if self.constants.contains(ctor) && self.registry.get_ctor(&scope, ctor).is_none() {
                    let constant = Expr::new(ExprKind::Var(ctor.clone()), span);
                    return args.iter().try_fold(constant, |func, arg| {
                        let app = ExprKind::App {
                            func: Box::new(func),
                            arg: Box::new(self.desugar_expr(arg)?),
                        };
                        Ok(Expr::new(app, span))
                    });
                }
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
            // In the body of a `data` type, a type parameter of that type
            // stands for its type argument. (Only a parameter that was a
            // whole field got its argument: `Box((a, a))` kept `a`.)
            SurfaceTy::Var(v) => Ok(self
                .expanding
                .borrow()
                .last()
                .and_then(|e| e.params.get(v).cloned())
                .unwrap_or_else(|| Ty::Var(v.clone()))),
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

        let info = self
            .registry
            .get_type(&self.scope.borrow(), name.as_str())
            .ok_or_else(|| DesugarError::UnknownType {
                name: name.to_string(),
            })?;
        let home = &info.home;
        let (params, ctors) = match &info.def {
            TypeDef::Extern => return Ok(Ty::Var(name.clone())),
            // Aliases are monomorphic here (parameterised aliases would
            // carry their args via the body).
            TypeDef::Alias(aliased) => {
                if !args.is_empty() {
                    return Err(DesugarError::TypeArityMismatch {
                        name: name.to_string(),
                        expected: 0,
                        got: args.len(),
                    });
                }
                return self.expand_alias(name, home, |this| this.desugar_ty(aliased));
            }
            TypeDef::Data { params, ctors } => (params, ctors),
        };

        if params.len() != args.len() {
            return Err(DesugarError::TypeArityMismatch {
                name: name.to_string(),
                expected: params.len(),
                got: args.len(),
            });
        }

        // The arguments are elaborated before the declaration is entered,
        // so a finite nested application (`List(List(I32))`) is valid.
        let core_args = args
            .iter()
            .map(|arg| self.desugar_ty(arg))
            .collect::<Result<Vec<_>, _>>()?;

        // Build right-nested sum from constructor field types
        let expanded = self.expand_data(name, home, params, core_args, |this| {
            this.build_sum_type(ctors)
        });
        expanded.map(|(ty, _)| ty)
    }

    /// The names of the expansions from `start`, then `name`: the cycle
    /// that an error shows.
    fn cycle(stack: &[Expansion], start: usize, name: &str) -> String {
        let mut names: Vec<&str> = stack[start..].iter().map(|e| e.name.as_str()).collect();
        names.push(name);
        names.join(" -> ")
    }

    /// Count one more body of a named type in the expansion in progress,
    /// which starts when `stack` is empty. An expansion that is too large
    /// or too deep is an error by name, not a compiler that does not end
    /// or that overflows its stack.
    fn count_expansion(&self, stack: &[Expansion], name: &SmolStr) -> Result<(), DesugarError> {
        let count = match stack {
            [] => 1,
            _ => self.expansions.get() + 1,
        };
        self.expansions.set(count);
        if count > MAX_EXPANSIONS || stack.len() >= MAX_EXPANSION_DEPTH {
            let name = stack.first().map_or(name, |e| &e.name).to_string();
            return Err(DesugarError::TypeTooLarge { name });
        }
        Ok(())
    }

    /// Run `f`, which expands the body of the alias `name` of the module
    /// `home`, with the names of `home` in scope. An alias that refers to
    /// itself with no `data` type between is an error: only a `data` type
    /// is recursive. With a `data` type between, the alias is expanded
    /// again: the recursion is that of the `data` type, which ends it.
    fn expand_alias(
        &self,
        name: &SmolStr,
        home: &SmolStr,
        f: impl FnOnce(&Self) -> Result<Ty, DesugarError>,
    ) -> Result<Ty, DesugarError> {
        {
            let stack = self.expanding.borrow();
            let seen = stack
                .iter()
                .rposition(|e| e.args.is_none() && e.home == *home && e.name == *name);
            if let Some(seen) = seen.filter(|&i| stack[i..].iter().all(|e| e.args.is_none())) {
                return Err(DesugarError::RecursiveAlias {
                    name: name.to_string(),
                    cycle: Self::cycle(&stack, seen, name),
                });
            }
            self.count_expansion(&stack, name)?;
        }
        self.expanding.borrow_mut().push(Expansion {
            home: home.clone(),
            name: name.clone(),
            args: None,
            params: HashMap::new(),
            recursive: false,
            hidden: false,
        });
        let result = self.in_scope(home, f);
        self.expanding.borrow_mut().pop();
        result
    }

    /// The type of the `data` type `name` of the module `home`, with the
    /// type parameters `params`, at the type arguments `args`. `f` builds
    /// the sum of its constructors, with the names of `home` in scope and
    /// each type parameter as its argument. The result also says if the
    /// type is folded: a value of it is made by `fold` and read by `unfold`.
    ///
    /// A reference to the type inside its own body, with the same
    /// arguments, is the variable of a recursive type. The result is then
    /// `mu var. body`, and the type is folded (v2 plan decision D7:
    /// iso-recursive).
    ///
    /// `data` types that refer to each other become nested recursive
    /// types (Bekic's construction), in the order of their names. A
    /// `data` type that is entered hides, for its body, each `data` type
    /// in progress that comes after it: in that body, such a type is not
    /// a variable, and it is expanded again. For `Forest` before `Tree`:
    ///
    /// ```text
    /// Forest = mu F. () + ((() + F) * F)     -- Tree is expanded in it
    /// Tree   = () + Forest                   -- not folded
    /// ```
    ///
    /// So the unfolding of `Forest` has `Tree` and `Forest` themselves in
    /// it, and not types that are only equal to them after more unfolds:
    /// a field of a constructor has the type that its declaration names.
    ///
    /// Not supported, with its own error: a reference with other
    /// arguments.
    // snip: nested recursive types; a cycle of n `data` types can make
    // types of a size up to 2^n bodies. Upgrade to a recursive type of n
    // variables (as the `rec` groups of WasmGC) if a large cycle is slow.
    fn expand_data(
        &self,
        name: &SmolStr,
        home: &SmolStr,
        params: &[SmolStr],
        args: Vec<Ty>,
        f: impl FnOnce(&Self) -> Result<Ty, DesugarError>,
    ) -> Result<(Ty, bool), DesugarError> {
        let hidden: Vec<usize>;
        {
            let mut stack = self.expanding.borrow_mut();
            let same = |e: &Expansion| e.args.is_some() && e.home == *home && e.name == *name;
            // In progress with other arguments, as a variable or not.
            if let Some(entered) = stack
                .iter()
                .position(|e| same(e) && e.args.as_ref() != Some(&args))
            {
                return Err(DesugarError::NonRegularRecursion {
                    name: name.to_string(),
                    cycle: Self::cycle(&stack, entered, name),
                });
            }
            if let Some(entered) = stack.iter_mut().find(|e| same(e) && !e.hidden) {
                entered.recursive = true;
                return Ok((Ty::Var(mu_var(name)), false));
            }
            self.count_expansion(&stack, name)?;
            hidden = stack
                .iter()
                .enumerate()
                .filter(|(_, e)| e.args.is_some() && !e.hidden && (&e.home, &e.name) > (home, name))
                .map(|(i, _)| i)
                .collect();
            for &i in &hidden {
                stack[i].hidden = true;
            }
            stack.push(Expansion {
                home: home.clone(),
                name: name.clone(),
                params: params.iter().cloned().zip(args.iter().cloned()).collect(),
                args: Some(args),
                recursive: false,
                hidden: false,
            });
        }
        let body = self.in_scope(home, f);
        let recursive = {
            let mut stack = self.expanding.borrow_mut();
            let recursive = stack.pop().is_some_and(|e| e.recursive);
            for &i in &hidden {
                stack[i].hidden = false;
            }
            recursive
        };
        let body = body?;
        Ok(if recursive {
            let var = mu_var(name);
            let body = Box::new(body);
            (Ty::Mu { var, body }, true)
        } else {
            (body, false)
        })
    }

    /// For the `data` type of the constructor `info`: its type parameters,
    /// its type with them as type variables, and if the type is folded
    /// ([`Self::expand_data`]).
    fn data_ty(&self, info: &ConstructorInfo) -> Result<(Vec<SmolStr>, Ty, bool), DesugarError> {
        let Some(TypeInfo {
            def: TypeDef::Data { params, ctors },
            ..
        }) = self.registry.get_type(&info.home, &info.data_name)
        else {
            return Err(DesugarError::UnknownType {
                name: info.data_name.to_string(),
            });
        };
        let args = params.iter().cloned().map(Ty::Var).collect();
        let (ty, folded) = self.expand_data(&info.data_name, &info.home, params, args, |this| {
            this.build_sum_type(ctors)
        })?;
        Ok((params.clone(), ty, folded))
    }

    /// Build the right-nested binary sum type for a list of constructors.
    ///
    /// `[A, B, C]` → `A + (B + C)`
    /// Each constructor's payload becomes its summand:
    /// - Nullary: `()`
    /// - Single field: the field type
    /// - Multiple fields: product of field types
    fn build_sum_type(&self, ctors: &[ConstructorDef]) -> Result<Ty, DesugarError> {
        assert!(
            !ctors.is_empty(),
            "data type must have at least one constructor"
        );

        if ctors.len() == 1 {
            return self.build_payload_type(&ctors[0].fields);
        }

        let left = self.build_payload_type(&ctors[0].fields)?;
        let right = self.build_sum_type(&ctors[1..])?;

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
    fn build_payload_type(&self, fields: &[SurfaceTy]) -> Result<Ty, DesugarError> {
        match fields {
            [] => Ok(Ty::Base(BaseTy::Unit)),
            [field] => self.desugar_ty(field),
            [first, rest @ ..] => Ok(Ty::Prod {
                left: Box::new(self.desugar_ty(first)?),
                right: Box::new(self.build_payload_type(rest)?),
            }),
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

        let ctors = self.ctors_of(&info)?;

        // The type parameters of the `data` type are bound in each
        // annotation: the type checker finds a type for each one from the
        // use of the value. (An annotation had the parameter itself, which
        // is no type at the constructor: `None` was not an `Option(I32)`.)
        let (params, ty, folded) = self.data_ty(&info)?;

        // Wrap in inl/inr chain based on index. The types of the other
        // constructors are names of the module that declares the type.
        let value = self.in_scope(&info.home, |this| {
            this.wrap_injection(payload, info.index, &ctors, &params, span)
        })?;
        // A value of a recursive type is folded (v2 plan rung E9). The
        // fold makes the annotations of the injections agree.
        Ok(if folded {
            Expr::new(
                ExprKind::Fold {
                    ty: quantify(ty, &params),
                    value: Box::new(value),
                },
                span,
            )
        } else {
            // snip: an annotated `let` carries the check, because the core
            // has no type ascription; upgrade to that core form when the
            // calculus gets it (plan decision D14).
            // The annotation is the declared type, so the type checker
            // compares the arguments with the declaration. The binder
            // names the constructor for the text of the error.
            let name = SmolStr::new(format!("#{ctor}"));
            Expr::new(
                ExprKind::Let {
                    name: name.clone(),
                    ty: Some(quantify(ty, &params)),
                    value: Box::new(value),
                    body: Box::new(Expr::new(ExprKind::Var(name), span)),
                },
                span,
            )
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

    /// Wrap a payload in the appropriate chain of inl/inr. Each annotation
    /// binds the type parameters `params` ([`quantify`]).
    fn wrap_injection(
        &self,
        payload: Expr,
        index: usize,
        ctors: &[ConstructorDef],
        params: &[SmolStr],
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
            let right_ty = self.build_sum_type(&ctors[1..])?;
            Ok(Expr::new(
                ExprKind::Inl {
                    ty: quantify(right_ty, params),
                    value: Box::new(payload),
                },
                span,
            ))
        } else if index == total - 1 {
            // Last constructor: inr(inr(...inr(payload)...))
            // Need (total - 1) layers of inr, but we do it recursively
            let left_ty = self.build_payload_type(&ctors[0].fields)?;
            let inner = self.wrap_injection(payload, index - 1, &ctors[1..], params, span)?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty: quantify(left_ty, params),
                    value: Box::new(inner),
                },
                span,
            ))
        } else {
            // Middle constructor: inr(... inl(payload) ...)
            let left_ty = self.build_payload_type(&ctors[0].fields)?;
            let inner = self.wrap_injection(payload, index - 1, &ctors[1..], params, span)?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty: quantify(left_ty, params),
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
        let info = self.ctor(first_ctor)?;
        let ctors = self.ctors_of(info)?;
        // A value of a recursive type is unfolded before its sum is read
        // (v2 plan rung E9).
        let core_scrutinee = if self.data_ty(info)?.2 {
            Expr::new(ExprKind::Unfold(Box::new(core_scrutinee)), span)
        } else {
            core_scrutinee
        };

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

        // An arm can refuse a value of its constructor: with a guard, or
        // with a literal or a constructor inside its pattern. The arms
        // are then tried in source order.
        let ordered = guarded || arms.iter().any(|a| Self::can_refuse_payload(&a.pattern));

        // The arms that can take constructor `i`, in the order to try.
        // When an arm can refuse a value: each arm for `i`, in source
        // order. If not, one arm: the last arm for `i`, or else the last
        // arm for every constructor.
        let chains: Vec<Vec<&MatchArm>> = (0..ctors.len())
            .map(|i| {
                if ordered {
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

    /// If a constructor pattern has a literal or a constructor inside it:
    /// the arm can then refuse a value of its own constructor.
    fn can_refuse_payload(pattern: &Pattern) -> bool {
        fn can_refuse(pattern: &Pattern) -> bool {
            match pattern {
                Pattern::Literal(_) | Pattern::Constructor { .. } => true,
                Pattern::Pair(left, right) => can_refuse(left) || can_refuse(right),
                Pattern::Tuple(parts) => parts.iter().any(can_refuse),
                Pattern::Var(_) | Pattern::Wildcard | Pattern::Unit => false,
            }
        }
        matches!(pattern, Pattern::Constructor { args, .. } if args.iter().any(can_refuse))
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
            [arm] if arm.guard.is_none() && !Self::can_refuse_payload(&arm.pattern) => {
                self.build_arm_body_inner(payload, ctor, arm, span)
            }
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
                return Err(DesugarError::NestedConstructorPattern {
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
            // A tuple pattern of variables, wildcards and pairs of them
            // lowers to a one-arm core `match` on a tuple pattern, as a
            // pair pattern does: the scrutinee is consumed one time.
            Pattern::Tuple(elements) if elements.iter().all(Self::is_irrefutable_pair_pattern) => {
                Ok(Expr::new(
                    ExprKind::Match {
                        scrutinee: Box::new(value.clone()),
                        arms: vec![ephapax_syntax::MatchArm {
                            pattern: Self::core_pattern(pattern)?,
                            guard: None,
                            body,
                        }],
                    },
                    span,
                ))
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

    /// The injections of the constructor `ctor`: the value of the `let`
    /// that carries the declared type ([`Desugarer::desugar_construct`]).
    fn injections<'a>(core: &'a Expr, ctor: &str) -> &'a ExprKind {
        let ExprKind::Let {
            name,
            ty: Some(_),
            value,
            ..
        } = &core.kind
        else {
            panic!("expected a `let` with a type, got {:?}", core.kind);
        };
        assert_eq!(name.as_str(), format!("#{ctor}"));
        &value.kind
    }

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
        assert!(matches!(injections(&core, "None"), ExprKind::Inl { .. }));
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
        assert!(matches!(injections(&core, "Some"), ExprKind::Inr { .. }));
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
        if let ExprKind::Inr { value, .. } = injections(&core, "Green") {
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
        if let ExprKind::Inr { value, .. } = injections(&core, "Blue") {
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
            Err(DesugarError::NonRegularRecursion { .. })
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
                false,
            );
        }
        let desugarer = Desugarer::with_registry(registry.clone());
        assert_eq!(
            desugarer.desugar_ty(&named("A0")).unwrap(),
            Ty::Base(BaseTy::I32)
        );
        registry.register_type_alias("", "A64".into(), named("A0"), false);
        assert!(matches!(
            Desugarer::with_registry(registry).desugar_ty(&named("A0")),
            Err(DesugarError::RecursiveAlias { .. })
        ));
    }
}
