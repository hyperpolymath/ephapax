// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! Module-qualified function names for the merge.
//!
//! A program becomes one wasm module with one flat function namespace
//! (`Program::into_merged`), but each module was type-checked in its own
//! scope. When two modules declare a function of the same name, one of
//! them gets the name `<module>::<function>` here, and every reference
//! follows the function that the type checker resolved it to.
//!
//! An extern function is never renamed: its name is the name of the host
//! import. `check_program` refuses a name collision that involves one.

use std::collections::HashMap;

use ephapax_syntax::{Decl, Expr, ExprKind, ExternItem, Module, Pattern, Var, Visibility};

use crate::LoadedModule;

/// For one module: a name as written → its name in the merged program.
/// Only the names that change are in the map.
type Renames = HashMap<Var, Var>;

/// The callable names a module declares, as `(name, public, function)`.
/// `function` is false for an extern function.
fn callables(module: &Module) -> Vec<(&Var, bool, bool)> {
    let mut out = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Fn {
                name, visibility, ..
            } => out.push((name, *visibility == Visibility::Public, true)),
            Decl::Extern { items, .. } => out.extend(items.iter().filter_map(|item| match item {
                ExternItem::Fn { name, .. } => Some((name, true, false)),
                ExternItem::Type { .. } => None,
            })),
            _ => {}
        }
    }
    out
}

/// The key the type checker's module registry uses for a module name.
fn module_key(name: &str) -> String {
    name.replace('.', "/")
}

/// Give each function a name that no other module of the program uses.
/// `modules` has the dependencies first and the root last. The root keeps
/// its names (they are the entry points of the program); after it, the
/// first module that declares a name keeps it.
pub(crate) fn qualify_functions(modules: &mut [LoadedModule]) {
    let qualified = qualified_names(modules);
    if qualified.iter().all(Renames::is_empty) {
        return;
    }
    let scopes = scopes(modules, &qualified);
    for (m, scope) in modules.iter_mut().zip(&scopes) {
        if !scope.is_empty() {
            m.core.decls.iter_mut().for_each(|d| rename_decl(d, scope));
        }
    }
}

/// For each module, the new name of each of its functions that must
/// change: `<module>::<function>`.
fn qualified_names(modules: &[LoadedModule]) -> Vec<Renames> {
    let root = modules.len().saturating_sub(1);
    let mut owner = HashMap::new();
    let mut qualified = vec![Renames::new(); modules.len()];
    for i in std::iter::once(root).chain(0..root) {
        let Some(m) = modules.get(i) else { break };
        for (name, _, function) in callables(&m.core) {
            if function && *owner.entry(name).or_insert(i) != i {
                let new = format!("{}::{name}", m.logical_path);
                qualified[i].insert(name.clone(), new.into());
            }
        }
    }
    qualified
}

/// For each module, what each renamed name means there, in the order the
/// type checker brings names into scope: the imports in order (a later
/// one shadows an earlier one), then the declarations of the module.
fn scopes(modules: &[LoadedModule], qualified: &[Renames]) -> Vec<Renames> {
    let index: HashMap<String, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (module_key(&m.core.name), i))
        .collect();
    modules
        .iter()
        .enumerate()
        .map(|(i, m)| {
            let mut scope = Renames::new();
            let mut bind = |from: usize, name: &Var, function: bool| {
                match qualified[from].get(name).filter(|_| function) {
                    Some(new) => scope.insert(name.clone(), new.clone()),
                    None => scope.remove(name),
                };
            };
            for import in &m.core.imports {
                let Some(&dep) = index.get(&module_key(&import.module)) else {
                    continue;
                };
                for (name, public, function) in callables(&modules[dep].core) {
                    if public && (import.names.is_empty() || import.names.contains(name)) {
                        bind(dep, name, function);
                    }
                }
            }
            for (name, _, function) in callables(&m.core) {
                bind(i, name, function);
            }
            scope
        })
        .collect()
}

fn rename_decl(decl: &mut Decl, scope: &Renames) {
    match decl {
        Decl::Fn {
            name, params, body, ..
        } => {
            rename(name, scope);
            params.iter_mut().for_each(|(p, _)| rename(p, scope));
            rename_expr(body, scope);
        }
        Decl::Const { value, .. } => rename_expr(value, scope),
        Decl::Type { .. } | Decl::Extern { .. } | Decl::Data { .. } => {}
    }
}

fn rename(name: &mut Var, scope: &Renames) {
    if let Some(new) = scope.get(name) {
        *name = new.clone();
    }
}

/// Rename every occurrence of a name in `scope`, binders included. A
/// local `let helper = ...` is renamed together with its uses, so it
/// shadows the renamed function as it shadowed the function before.
fn rename_expr(expr: &mut Expr, scope: &Renames) {
    // The names of this node: a use or a binder. No `_` arm: a new
    // expression form must say if it has a name.
    match &mut expr.kind {
        ExprKind::Var(name)
        | ExprKind::Let { name, .. }
        | ExprKind::LetLin { name, .. }
        | ExprKind::Lambda { param: name, .. } => rename(name, scope),
        ExprKind::Case {
            left_var,
            right_var,
            ..
        } => {
            rename(left_var, scope);
            rename(right_var, scope);
        }
        ExprKind::Match { arms, .. } => {
            for arm in arms {
                rename_pattern(&mut arm.pattern, scope);
            }
        }
        ExprKind::Handle { clauses, .. } => {
            for clause in clauses {
                clause.params.iter_mut().for_each(|p| rename(p, scope));
            }
        }
        ExprKind::Lit(_)
        | ExprKind::StringNew { .. }
        | ExprKind::StringConcat { .. }
        | ExprKind::StringLen(_)
        | ExprKind::App { .. }
        | ExprKind::Pair { .. }
        | ExprKind::Fst(_)
        | ExprKind::Snd(_)
        | ExprKind::Inl { .. }
        | ExprKind::Inr { .. }
        | ExprKind::If { .. }
        | ExprKind::Region { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::Deref(_)
        | ExprKind::Drop(_)
        | ExprKind::Copy(_)
        | ExprKind::Block(_)
        | ExprKind::FFI { .. }
        | ExprKind::Perform { .. }
        | ExprKind::BinOp { .. }
        | ExprKind::UnaryOp { .. }
        | ExprKind::ListLit(_)
        | ExprKind::ListIndex { .. }
        | ExprKind::TupleLit(_)
        | ExprKind::TupleIndex { .. } => {}
    }
    for child in expr.children_mut() {
        rename_expr(child, scope);
    }
}

fn rename_pattern(pattern: &mut Pattern, scope: &Renames) {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) | Pattern::Unit => {}
        Pattern::Var(name) => rename(name, scope),
        Pattern::Pair(left, right) => {
            rename_pattern(left, scope);
            rename_pattern(right, scope);
        }
        Pattern::Tuple(patterns) | Pattern::Constructor { args: patterns, .. } => {
            patterns.iter_mut().for_each(|p| rename_pattern(p, scope));
        }
    }
}
