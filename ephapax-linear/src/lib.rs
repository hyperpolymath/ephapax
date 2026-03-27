#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Standalone Linear/Affine Discipline Checker for Ephapax
//!
//! This crate implements **dual substructural grammars** — two focused views
//! of the ephapax syntax, each enforcing a different structural discipline:
//!
//! - [`linear`] — **Linear discipline**: no weakening, no contraction.
//!   Every `let!` binding must be consumed exactly once. `drop` is forbidden.
//!   Branches must agree on which linear variables are consumed.
//!
//! - [`affine`] — **Affine discipline**: weakening allowed, no contraction.
//!   `let` bindings of any type may be implicitly dropped. `drop(e)` is valid.
//!   Branches may disagree on consumption.
//!
//! Both grammars share the same AST ([`ephapax_syntax`]) but apply different
//! structural rules. This is the substructural logic concept of **focusing**:
//! restricting proof rules to a discipline.
//!
//! # Dyadic Design
//!
//! Ephapax is a **dyadic** language — both disciplines coexist per-program.
//! `let!` always means linear (exactly-once), `let` always means affine
//! (at-most-once). There is no global mode switch. This crate provides
//! standalone checkers for each discipline, suitable for:
//!
//! - Linting tools that want to verify discipline without the full compiler
//! - Editor integrations that highlight discipline violations
//! - Formal verification tooling that needs isolated discipline checks
//! - Teaching substructural type systems (run the same program through both
//!   checkers to see what each discipline rejects)

pub mod affine;
pub mod linear;

mod context;

pub use affine::AffineChecker;
pub use linear::LinearChecker;

/// Discipline selection for unified entry points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Discipline {
    /// Linear: exactly-once consumption, no weakening, no contraction.
    Linear,
    /// Affine: at-most-once consumption, weakening allowed, no contraction.
    Affine,
}

/// Check an expression under a chosen discipline.
///
/// This is a convenience function — for more control, use [`LinearChecker`]
/// or [`AffineChecker`] directly.
pub fn check_expr(
    expr: &ephapax_syntax::Expr,
    discipline: Discipline,
) -> Result<(), Vec<DisciplineViolation>> {
    match discipline {
        Discipline::Linear => {
            let mut checker = LinearChecker::new();
            checker.check(expr)?;
            Ok(())
        }
        Discipline::Affine => {
            let mut checker = AffineChecker::new();
            checker.check(expr)?;
            Ok(())
        }
    }
}

/// Check a module under a chosen discipline.
pub fn check_module(
    module: &ephapax_syntax::Module,
    discipline: Discipline,
) -> Result<(), Vec<DisciplineViolation>> {
    match discipline {
        Discipline::Linear => {
            let mut checker = LinearChecker::new();
            checker.check_module(module)
        }
        Discipline::Affine => {
            let mut checker = AffineChecker::new();
            checker.check_module(module)
        }
    }
}

/// A violation of the substructural discipline.
///
/// Both checkers produce the same violation type, but the set of possible
/// violations differs per discipline (e.g. `DropForbidden` only appears
/// in the linear checker, `ImplicitDropWarning` only in the affine checker).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DisciplineViolation {
    // === Shared (both disciplines) ===
    /// A linear/affine variable was used more than once (contraction).
    #[error("variable `{name}` used more than once (contraction forbidden)")]
    Contraction { name: String },

    /// A variable was referenced but not in scope.
    #[error("variable `{name}` not in scope")]
    NotInScope { name: String },

    // === Linear-only violations ===
    /// A `let!` binding was not consumed (weakening forbidden in linear).
    #[error("linear binding `{name}` not consumed (weakening forbidden)")]
    WeakeningForbidden { name: String },

    /// `drop(e)` was used in a linear context (explicit weakening forbidden).
    #[error("`drop` is forbidden in the linear grammar")]
    DropForbidden,

    /// Branches disagree on which linear variables are consumed.
    #[error("branches disagree on consumption of linear variable `{name}`")]
    BranchDisagreement { name: String },

    /// A region-bound linear value was not consumed before region exit.
    #[error("region `{region}`: linear binding `{name}` not consumed before region exit")]
    RegionLeakLinear { region: String, name: String },

    /// A `let` binding was given a linear-typed value in linear grammar
    /// (must use `let!` for linear types in linear discipline).
    #[error("`let` used for linear type — use `let!` in linear discipline (binding `{name}`)")]
    LetForLinearType { name: String },

    // === Affine-only violations ===
    /// A region-bound value was implicitly dropped (warning, not error).
    /// This is valid in affine grammar but may indicate a resource leak
    /// for non-memory resources (file handles, locks, connections).
    #[error("region `{region}`: binding `{name}` implicitly dropped (potential non-memory resource leak)")]
    ImplicitDropWarning { region: String, name: String },
}

impl DisciplineViolation {
    /// Whether this violation is a hard error (vs a lint warning).
    pub fn is_error(&self) -> bool {
        !matches!(self, DisciplineViolation::ImplicitDropWarning { .. })
    }

    /// Whether this violation is a warning (not a hard error).
    pub fn is_warning(&self) -> bool {
        matches!(self, DisciplineViolation::ImplicitDropWarning { .. })
    }
}

#[cfg(test)]
mod tests;
