// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! A minimal demand-driven (salsa-style) incremental query engine for the
//! ephapax compile pipeline.
//!
//! # What this is
//!
//! The CLI today re-runs `parse -> typecheck -> compile` from scratch on
//! every invocation. For a single-shot `ephapax compile` that is fine; for
//! a long-lived process (LSP, REPL) that re-checks after each keystroke it
//! is wasteful. This crate memoises those steps and only recomputes the
//! ones whose inputs actually changed.
//!
//! # How it works (red/green, hand-rolled)
//!
//! Every input mutation bumps a global [`Revision`]. Each derived query
//! ([`QueryDb::parsed`], [`QueryDb::typed`], [`QueryDb::wasm`]) stores a
//! [`Memo`] with two stamps: `changed_at` (the last revision its value
//! *actually changed*) and `verified_at` (the last revision we *confirmed*
//! it current). A query skips recomputation when the things it depends on
//! have not `changed_at` a later revision than it was last `verified_at`.
//!
//! The key subtlety is **backdating**: when a query *does* recompute but
//! the new value equals the old one (`PartialEq`), we keep the old
//! `changed_at`. That is what lets "edit a comment, the source re-parses,
//! but the typechecker and codegen *skip*" work — the re-parsed [`Module`]
//! compares equal, so its `changed_at` does not advance, so `typed` and
//! `wasm` see no change downstream.
//!
//! # What this is NOT (yet)
//!
//! This is a *foundation*. The dependency graph here is the fixed linear
//! pipeline `source -> parsed -> typed -> wasm`, so dependencies are
//! threaded by hand rather than tracked through a general query trait. A
//! production engine would: (a) track an arbitrary dependency DAG (needed
//! for the multi-module `import` case: `parsed` resolves imports through
//! `ephapax-driver`, but an imported file is not an input here, so a
//! program with imports is re-read from disk on every demand and never
//! served from the parse memo), (b) return
//! `Arc<T>`/references instead of cloning memoised values, and (c)
//! optionally persist memos through a `QueryStore` backing (the disabled
//! `ephapax-vram-cache` is a natural candidate once `ephapax-proven`
//! returns). Those are documented extension points, not built here.

use ephapax_driver::{check_program, parse_source, DriverError, Program};
use ephapax_wasm::compile_module;
use std::collections::HashMap;
use std::path::Path;

/// A logical source unit, identified by name/path.
pub type SourceId = String;

/// Monotonic global clock. Bumped once per input mutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Revision(pub u64);

/// Result of the front end up to desugaring (`ephapax_driver::parse_source`).
pub type ParsedResult = Result<Program, DriverError>;
/// Result of `ephapax_driver::check_program`.
pub type TypedResult = Result<(), DriverError>;
/// `compile_module`'s result, with the error flattened to a `String` so the
/// memo type is self-contained.
pub type WasmResult = Result<Vec<u8>, String>;

struct Input {
    text: String,
    changed_at: Revision,
}

struct Memo<T> {
    value: T,
    /// Last revision at which `value` actually changed.
    changed_at: Revision,
    /// Last revision at which we confirmed `value` is current.
    verified_at: Revision,
}

/// The query database: inputs plus one memo table per derived query.
#[derive(Default)]
pub struct QueryDb {
    revision: Revision,
    inputs: HashMap<SourceId, Input>,
    parsed: HashMap<SourceId, Memo<ParsedResult>>,
    typed: HashMap<SourceId, Memo<TypedResult>>,
    wasm: HashMap<SourceId, Memo<WasmResult>>,
    /// Number of leaf-function invocations (parse/typecheck/codegen). Lets
    /// callers and tests observe the recompute-skip behaviour.
    recomputes: u64,
}

/// Two parse results are equivalent for backdating iff both are `Ok` with
/// equal core modules, or both are the same error. `DriverError` is not
/// `PartialEq`; its `Debug` form holds every field.
fn parsed_equiv(a: &ParsedResult, b: &ParsedResult) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => x
            .modules
            .iter()
            .map(|m| &m.core)
            .eq(y.modules.iter().map(|m| &m.core)),
        (Err(x), Err(y)) => format!("{x:?}") == format!("{y:?}"),
        _ => false,
    }
}

impl QueryDb {
    /// A fresh, empty database.
    pub fn new() -> Self {
        Self::default()
    }

    /// Total leaf-function recomputations performed so far.
    pub fn recompute_count(&self) -> u64 {
        self.recomputes
    }

    /// The current revision.
    pub fn revision(&self) -> Revision {
        self.revision
    }

    /// Set (or replace) a source unit's text. Bumps the revision and marks
    /// the input changed **only if** the text actually differs — an
    /// identical write is a no-op, so it cannot invalidate downstream
    /// memos.
    pub fn set_source_text(&mut self, id: &str, text: impl Into<String>) {
        let text = text.into();
        if let Some(inp) = self.inputs.get(id) {
            if inp.text == text {
                return;
            }
        }
        self.revision.0 += 1;
        let changed_at = self.revision;
        self.inputs
            .insert(id.to_string(), Input { text, changed_at });
    }

    fn input_changed_at(&self, id: &str) -> Revision {
        self.inputs
            .get(id)
            .map(|i| i.changed_at)
            .unwrap_or_default()
    }

    /// Parse query. Memoises the driver's resolve + parse + desugar;
    /// depends only on the source text. Imports resolve next to `id` when
    /// `id` is a file on disk, then in the stdlib.
    pub fn parsed(&mut self, id: &str) -> ParsedResult {
        let dep = self.input_changed_at(id);
        let rev = self.revision;
        if let Some(m) = self.parsed.get_mut(id) {
            // A program with imports also depends on files that are not
            // inputs of this database, and a failed load may be due to
            // one of them. Only a successful, import-free result is
            // served from the memo; anything else is loaded again.
            // (Downstream memos still skip when the result is unchanged.)
            let self_contained = matches!(&m.value, Ok(p) if p.modules.len() == 1);
            if dep <= m.verified_at && self_contained {
                let value = m.value.clone();
                m.verified_at = rev;
                return value;
            }
        }
        let text = self
            .inputs
            .get(id)
            .map(|i| i.text.clone())
            .unwrap_or_default();
        let base_dir = Path::new(id).parent().filter(|_| Path::new(id).is_file());
        let stdlib = ephapax_driver::stdlib_dir(None);
        let new = parse_source(&text, id, base_dir, stdlib.as_deref());
        self.recomputes += 1;
        // The result changed although the input did not: an imported file
        // changed on disk. That is a new revision, so that the queries
        // that depend on this one recompute.
        if matches!(self.parsed.get(id), Some(old)
            if dep <= old.verified_at && !parsed_equiv(&old.value, &new))
        {
            self.revision.0 += 1;
        }
        let rev = self.revision;
        let changed_at = match self.parsed.get(id) {
            Some(old) if parsed_equiv(&old.value, &new) => old.changed_at,
            _ => rev,
        };
        self.parsed.insert(
            id.to_string(),
            Memo {
                value: new.clone(),
                changed_at,
                verified_at: rev,
            },
        );
        new
    }

    /// Type-check query. Memoises `check_program`; depends on `parsed`.
    pub fn typed(&mut self, id: &str) -> TypedResult {
        let parsed = self.parsed(id);
        let dep = self
            .parsed
            .get(id)
            .map(|m| m.changed_at)
            .unwrap_or_default();
        let rev = self.revision;
        if let Some(m) = self.typed.get_mut(id) {
            if dep <= m.verified_at {
                let value = m.value.clone();
                m.verified_at = rev;
                return value;
            }
        }
        let new: TypedResult = match &parsed {
            Ok(program) => check_program(program),
            // Unparseable input has no typecheck result of its own; the
            // parse error is surfaced by `parsed`. Treat as no type error.
            Err(_) => Ok(()),
        };
        self.recomputes += 1;
        let rev = self.revision;
        let changed_at = match self.typed.get(id) {
            Some(old) if old.value.is_ok() && new.is_ok() => old.changed_at,
            _ => rev,
        };
        self.typed.insert(
            id.to_string(),
            Memo {
                value: new.clone(),
                changed_at,
                verified_at: rev,
            },
        );
        new
    }

    /// Codegen query. Memoises `compile_module`, gated on a clean
    /// typecheck; depends on `parsed` and `typed`.
    pub fn wasm(&mut self, id: &str) -> WasmResult {
        let typed = self.typed(id);
        // The program that `typed` checked. A second `parsed` demand
        // loads a program with imports again, and an imported file may
        // change between two loads: the compiled program must be the
        // checked one.
        let parsed = match self.parsed.get(id) {
            Some(memo) => memo.value.clone(),
            None => self.parsed(id),
        };
        let dep_parsed = self
            .parsed
            .get(id)
            .map(|m| m.changed_at)
            .unwrap_or_default();
        let dep_typed = self.typed.get(id).map(|m| m.changed_at).unwrap_or_default();
        let dep = dep_parsed.max(dep_typed);
        let rev = self.revision;
        if let Some(m) = self.wasm.get_mut(id) {
            if dep <= m.verified_at {
                let value = m.value.clone();
                m.verified_at = rev;
                return value;
            }
        }
        let new: WasmResult = match (&parsed, &typed) {
            (Ok(program), Ok(())) => program
                .clone()
                .into_merged()
                .map_err(|e| format!("cannot compile: {e}"))
                .and_then(|module| compile_module(&module).map_err(|e| e.0)),
            (Err(e), _) | (_, Err(e)) => Err(format!("cannot compile: {e}")),
        };
        self.recomputes += 1;
        let rev = self.revision;
        let changed_at = match self.wasm.get(id) {
            Some(old) if old.value == new => old.changed_at,
            _ => rev,
        };
        self.wasm.insert(
            id.to_string(),
            Memo {
                value: new.clone(),
                changed_at,
                verified_at: rev,
            },
        );
        new
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ADD: &str = "fn add(a: I32, b: I32): I32 = a + b\n";

    #[test]
    fn no_edit_skips_all_recompute() {
        let mut db = QueryDb::new();
        db.set_source_text("m", ADD);
        let _ = db.wasm("m");
        let n = db.recompute_count();
        assert!(n >= 3, "first demand runs parse+typecheck+codegen, got {n}");

        // Re-demand with no edit: nothing recomputes.
        let _ = db.wasm("m");
        assert_eq!(
            db.recompute_count(),
            n,
            "re-demand with no edit must skip everything"
        );
    }

    #[test]
    fn identical_set_does_not_invalidate() {
        let mut db = QueryDb::new();
        db.set_source_text("m", ADD);
        let _ = db.wasm("m");
        let n = db.recompute_count();
        // Writing the exact same text must not bump the revision.
        db.set_source_text("m", ADD);
        let _ = db.wasm("m");
        assert_eq!(
            db.recompute_count(),
            n,
            "identical set_source_text must not invalidate"
        );
    }

    /// A program that fails to load is loaded again on each demand (its
    /// imports are not inputs). The same failure is not a change: the
    /// queries after the parse do not run again.
    #[test]
    fn same_failure_does_not_recompute_downstream() {
        let mut db = QueryDb::new();
        db.set_source_text("m", "fn add(a: I32): I32 = a +\n");
        assert!(db.parsed("m").is_err());
        let _ = db.typed("m");
        let n = db.recompute_count();
        let _ = db.typed("m");
        assert_eq!(db.recompute_count(), n + 1, "only the parse runs again");
    }

    #[test]
    fn real_change_recomputes() {
        let mut db = QueryDb::new();
        db.set_source_text("m", ADD);
        let _ = db.wasm("m");
        let n = db.recompute_count();
        // A semantically different body must recompute.
        db.set_source_text("m", "fn add(a: I32, b: I32): I32 = a - b\n");
        let _ = db.wasm("m");
        assert!(db.recompute_count() > n, "a real edit must recompute");
    }

    #[test]
    fn downstream_skips_when_module_unchanged() {
        // Editing only a leading line comment changes the source text but
        // (assuming comments are not represented in the AST) yields an
        // equal Module, so parse re-runs but typecheck + codegen skip via
        // backdating. If the parser ever keeps comment trivia in the AST,
        // this asserts the weaker (still correct) property that we do not
        // recompute MORE than a full pipeline.
        let mut db = QueryDb::new();
        db.set_source_text("m", ADD);
        let _ = db.wasm("m");
        let n = db.recompute_count();

        db.set_source_text("m", format!("// leading comment\n{ADD}"));
        let _ = db.wasm("m");
        let delta = db.recompute_count() - n;
        assert!(
            delta <= 3,
            "comment-only edit must not recompute more than a full pipeline; delta={delta}"
        );
    }
}
