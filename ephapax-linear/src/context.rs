// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Shared variable tracking context for both discipline checkers.
//!
//! Tracks binding usage (consumed/unconsumed), binding form (`let` vs `let!`),
//! type linearity, and region association. Both the linear and affine checkers
//! use this context but apply different rules to the usage state.

use ephapax_syntax::{RegionName, Ty, Var};
use std::collections::HashMap;

/// How a binding was introduced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingForm {
    /// `let x = ...` — affine binding form
    Let,
    /// `let! x = ...` — linear binding form
    LetBang,
    /// Function parameter
    Param,
}

/// A tracked binding in the discipline context.
#[derive(Debug, Clone)]
pub struct Binding {
    /// How the binding was introduced
    pub form: BindingForm,
    /// The type of the binding (if known)
    pub ty: Option<Ty>,
    /// Whether the binding has been consumed (used)
    pub consumed: bool,
    /// The region this binding is associated with (if any)
    pub region: Option<RegionName>,
}

impl Binding {
    /// Whether this binding's type is linear (must be consumed).
    pub fn is_linear_type(&self) -> bool {
        self.ty.as_ref().is_some_and(|t| t.is_linear())
    }

    /// Whether this binding was introduced with `let!` (linear form).
    pub fn is_linear_form(&self) -> bool {
        self.form == BindingForm::LetBang
    }
}

/// Variable tracking context with scope support.
///
/// Supports nested scopes (regions, branches, function bodies) via
/// snapshot/restore. Both checkers share this structure but apply
/// different rules to the tracked state.
#[derive(Debug, Clone)]
pub struct Context {
    /// All bindings in scope, keyed by variable name.
    /// Inner Vec allows shadowing — most recent binding is last.
    bindings: HashMap<Var, Vec<Binding>>,

    /// Stack of active regions (innermost last).
    region_stack: Vec<RegionName>,
}

impl Context {
    /// Create an empty context.
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            region_stack: Vec::new(),
        }
    }

    /// Introduce a new binding into the context.
    pub fn bind(&mut self, name: Var, form: BindingForm, ty: Option<Ty>) {
        let region = self.region_stack.last().cloned();
        let binding = Binding {
            form,
            ty,
            consumed: false,
            region,
        };
        self.bindings.entry(name).or_default().push(binding);
    }

    /// Mark a binding as consumed. Returns `false` if already consumed
    /// (contraction) or not in scope.
    pub fn consume(&mut self, name: &Var) -> ConsumeResult {
        match self.bindings.get_mut(name) {
            None => ConsumeResult::NotInScope,
            Some(stack) => match stack.last_mut() {
                None => ConsumeResult::NotInScope,
                Some(binding) if binding.consumed => ConsumeResult::AlreadyConsumed,
                Some(binding) => {
                    binding.consumed = true;
                    ConsumeResult::Ok
                }
            },
        }
    }

    /// Get the current binding for a variable (if any).
    pub fn get(&self, name: &Var) -> Option<&Binding> {
        self.bindings.get(name).and_then(|stack| stack.last())
    }

    /// Get all bindings (for scope-exit checks).
    #[allow(dead_code)]
    pub fn all_bindings(&self) -> impl Iterator<Item = (&Var, &Binding)> {
        self.bindings
            .iter()
            .filter_map(|(name, stack)| stack.last().map(|b| (name, b)))
    }

    /// Get all bindings associated with a specific region.
    pub fn region_bindings(&self, region: &RegionName) -> Vec<(Var, Binding)> {
        self.bindings
            .iter()
            .filter_map(|(name, stack)| {
                stack.last().and_then(|b| {
                    if b.region.as_ref() == Some(region) {
                        Some((name.clone(), b.clone()))
                    } else {
                        None
                    }
                })
            })
            .collect()
    }

    /// Enter a new region scope.
    pub fn enter_region(&mut self, name: RegionName) {
        self.region_stack.push(name);
    }

    /// Exit the current region scope. Returns the region name.
    pub fn exit_region(&mut self) -> Option<RegionName> {
        self.region_stack.pop()
    }

    /// Take a snapshot of the current consumption state.
    /// Used for branch analysis — snapshot before, check each branch,
    /// then compare snapshots.
    pub fn snapshot_consumption(&self) -> HashMap<Var, bool> {
        self.bindings
            .iter()
            .filter_map(|(name, stack)| stack.last().map(|b| (name.clone(), b.consumed)))
            .collect()
    }

    /// Restore consumption state from a snapshot.
    pub fn restore_consumption(&mut self, snapshot: &HashMap<Var, bool>) {
        for (name, stack) in &mut self.bindings {
            if let Some(binding) = stack.last_mut() {
                if let Some(&was_consumed) = snapshot.get(name) {
                    binding.consumed = was_consumed;
                }
            }
        }
    }

    /// Remove a binding (for scope exit). Returns the binding if it existed.
    pub fn unbind(&mut self, name: &Var) -> Option<Binding> {
        self.bindings.get_mut(name).and_then(|stack| stack.pop())
    }
}

/// Result of attempting to consume a binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsumeResult {
    /// Successfully consumed.
    Ok,
    /// Variable not in scope.
    NotInScope,
    /// Variable already consumed (contraction violation).
    AlreadyConsumed,
}
