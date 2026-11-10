// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! Monomorphisation of generic functions (v2 plan rung E7, step S2b).
//!
//! The checker checks a generic function one time, with its type
//! parameters as opaque types, and records the type arguments of every
//! use ([`TypeArgs`]). [`monomorphise`] then makes one copy of the
//! function for each set of type arguments and removes the generic
//! definition. Code generation and the interpreter see monomorphic
//! functions only.

use std::collections::{HashMap, HashSet};

use ephapax_syntax::{Decl, Expr, ExprKind, Module, Ty, Var};
use smol_str::SmolStr;

use crate::{module_types_and_args, subst_tys, ModuleRegistry, SpannedTypeError, TypeArgs};

/// Type variable → type.
type Subst = HashMap<SmolStr, Ty>;

/// Replace type variables in the signature of the function `decl` and in
/// the type annotations of its body.
pub(crate) fn substitute_fn(decl: &mut Decl, subst: &Subst) {
    let Decl::Fn {
        params,
        ret_ty,
        body,
        ..
    } = decl
    else {
        return;
    };
    for (_, ty) in params.iter_mut() {
        *ty = subst_tys(ty, subst);
    }
    *ret_ty = subst_tys(ret_ty, subst);
    substitute_expr(body, subst);
}

/// Replace type variables in the type annotations of `expr` and of each
/// expression in it.
fn substitute_expr(expr: &mut Expr, subst: &Subst) {
    substitute_node(expr, subst);
    for child in expr.children_mut() {
        substitute_expr(child, subst);
    }
}

/// The type annotations of one node.
fn substitute_node(expr: &mut Expr, subst: &Subst) {
    match &mut expr.kind {
        ExprKind::Let { ty: Some(ty), .. }
        | ExprKind::LetLin { ty: Some(ty), .. }
        | ExprKind::Lambda { param_ty: ty, .. }
        | ExprKind::Inl { ty, .. }
        | ExprKind::Inr { ty, .. }
        | ExprKind::Fold { ty, .. } => *ty = subst_tys(ty, subst),
        ExprKind::TypeApp { type_args, .. } => {
            for ty in type_args {
                *ty = subst_tys(ty, subst);
            }
        }
        _ => {}
    }
}

/// `module` with one monomorphic copy of each generic function for each
/// set of type arguments it is used with, and no generic function.
///
/// `module` must be a whole program (the imports already merged in): it
/// is checked on its own. A program with no generic function is returned
/// as it is, without a check.
pub fn monomorphise(module: &Module) -> Result<Module, SpannedTypeError> {
    let generic: HashMap<&Var, &Decl> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Fn {
                name, type_params, ..
            } if !type_params.is_empty() => Some((name, decl)),
            _ => None,
        })
        .collect();
    if generic.is_empty() {
        return Ok(module.clone());
    }
    let (_, type_args) = module_types_and_args(module, &mut ModuleRegistry::new())?;
    let mut mono = Mono {
        generic,
        type_args,
        made: HashSet::new(),
        instances: Vec::new(),
    };

    let mut decls = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Fn { type_params, .. } if !type_params.is_empty() => {}
            // The value of a constant can use a generic function too.
            Decl::Fn { .. } | Decl::Const { .. } => {
                let mut decl = decl.clone();
                if let Decl::Fn { body, .. } | Decl::Const { value: body, .. } = &mut decl {
                    mono.rewrite(body, &Subst::new());
                }
                decls.push(decl);
            }
            other => decls.push(other.clone()),
        }
    }
    decls.extend(mono.instances);
    Ok(Module {
        name: module.name.clone(),
        imports: module.imports.clone(),
        decls,
    })
}

/// The state of one monomorphisation: the generic functions, the type
/// arguments of each use, and the copies made so far.
struct Mono<'a> {
    generic: HashMap<&'a Var, &'a Decl>,
    type_args: TypeArgs,
    /// Names of the copies made (or in work) so far.
    made: HashSet<Var>,
    instances: Vec<Decl>,
}

impl Mono<'_> {
    /// Point each use of a generic function in `expr` at the copy for its
    /// type arguments. `subst` is not empty when `expr` is the body of
    /// such a copy: it gives the type parameters of the copied function.
    fn rewrite(&mut self, expr: &mut Expr, subst: &Subst) {
        // The table has the id that the node had when it was checked.
        let args = self.type_args.get(&expr.id).cloned();
        if let (ExprKind::Var(name) | ExprKind::TypeApp { name, .. }, Some(args)) =
            (&expr.kind, args)
        {
            let args = args.iter().map(|t| subst_tys(t, subst)).collect();
            // The copy has no type parameter: explicit type arguments end here.
            expr.kind = ExprKind::Var(self.instance(name, args));
        }
        if !subst.is_empty() {
            substitute_node(expr, subst);
            // The copy gets its own entries in the next type table.
            expr.renew_id();
        }
        for child in expr.children_mut() {
            self.rewrite(child, subst);
        }
    }

    /// The name of the copy of the generic function `name` for `args`;
    /// the copy is made at the first request.
    fn instance(&mut self, name: &Var, args: Vec<Ty>) -> Var {
        let Some(&generic) = self.generic.get(name) else {
            return name.clone();
        };
        let rendered: Vec<String> = args.iter().map(ty_name).collect();
        let copy_name: Var = format!("{name}<{}>", rendered.join(", ")).into();
        // Recorded before the body is rewritten, so a recursive call
        // finds the copy in work.
        if !self.made.insert(copy_name.clone()) {
            return copy_name;
        }
        let mut copy = generic.clone();
        if let Decl::Fn {
            name,
            type_params,
            params,
            ret_ty,
            body,
            ..
        } = &mut copy
        {
            let subst: Subst = std::mem::take(type_params).into_iter().zip(args).collect();
            *name = copy_name.clone();
            for (_, ty) in params.iter_mut() {
                *ty = subst_tys(ty, &subst);
            }
            *ret_ty = subst_tys(ret_ty, &subst);
            self.rewrite(body, &subst);
        }
        self.instances.push(copy);
        copy_name
    }
}

/// A short name of a type, for the name of a copy. Two types have the
/// same name only when they are equal.
fn ty_name(ty: &Ty) -> String {
    let list = |tys: &[Ty]| tys.iter().map(ty_name).collect::<Vec<_>>().join(", ");
    match ty {
        Ty::Base(base) => format!("{base:?}"),
        Ty::String(region) => format!("String@{region}"),
        Ty::Var(name) => name.to_string(),
        Ty::Prod { left, right } => format!("({} * {})", ty_name(left), ty_name(right)),
        Ty::Sum { left, right } => format!("({} + {})", ty_name(left), ty_name(right)),
        Ty::Tuple(elems) => format!("({})", list(elems)),
        Ty::List(elem) => format!("[{}]", ty_name(elem)),
        Ty::Mu { var, body } => format!("(mu {var}. {})", ty_name(body)),
        other => format!("{other:?}"),
    }
}
