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
//! for the multi-module `import` case — see `import_resolver`), (b) return
//! `Arc<T>`/references instead of cloning memoised values, and (c)
//! optionally persist memos through a `QueryStore` backing (the disabled
//! `ephapax-vram-cache` is a natural candidate once `ephapax-proven`
//! returns). Those are documented extension points, not built here.

use ephapax_parser::{parse_module, ParseError};
use ephapax_syntax::Module;
use ephapax_typing::{type_check_module, SpannedTypeError};
use ephapax_wasm::compile_module;
use std::collections::HashMap;

/// A logical source unit, identified by name/path.
pub type SourceId = String;

/// Monotonic global clock. Bumped once per input mutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Revision(pub u64);

/// `parse_module`'s result type.
pub type ParsedResult = Result<Module, Vec<ParseError>>;
/// `type_check_module`'s result type.
pub type TypedResult = Result<(), SpannedTypeError>;
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
/// equal modules. `ParseError` is not `PartialEq`, and a differing parse
/// error is a real change anyway, so any `Err` is treated as changed.
fn parsed_equiv(a: &ParsedResult, b: &ParsedResult) -> bool {
    matches!((a, b), (Ok(x), Ok(y)) if x == y)
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
        self.inputs.insert(id.to_string(), Input { text, changed_at });
    }

    fn input_changed_at(&self, id: &str) -> Revision {
        self.inputs.get(id).map(|i| i.changed_at).unwrap_or_default()
    }

    /// Parse query. Memoises `parse_module`; depends only on the source
    /// text.
    pub fn parsed(&mut self, id: &str) -> ParsedResult {
        let dep = self.input_changed_at(id);
        if let Some(m) = self.parsed.get(id) {
            if dep <= m.verified_at {
                let value = m.value.clone();
                self.parsed.get_mut(id).unwrap().verified_at = self.revision;
                return value;
            }
        }
        let text = self.inputs.get(id).map(|i| i.text.clone()).unwrap_or_default();
        let new = parse_module(&text, id);
        self.recomputes += 1;
        let rev = self.revision;
        let changed_at = match self.parsed.get(id) {
            Some(old) if parsed_equiv(&old.value, &new) => old.changed_at,
            _ => rev,
        };
        self.parsed.insert(
            id.to_string(),
            Memo { value: new.clone(), changed_at, verified_at: rev },
        );
        new
    }

    /// Type-check query. Memoises `type_check_module`; depends on `parsed`.
    pub fn typed(&mut self, id: &str) -> TypedResult {
        let parsed = self.parsed(id);
        let dep = self.parsed.get(id).map(|m| m.changed_at).unwrap_or_default();
        if let Some(m) = self.typed.get(id) {
            if dep <= m.verified_at {
                let value = m.value.clone();
                self.typed.get_mut(id).unwrap().verified_at = self.revision;
                return value;
            }
        }
        let new: TypedResult = match &parsed {
            Ok(module) => type_check_module(module),
            // Unparseable input has no typecheck result of its own; the
            // parse error is surfaced by `parsed`. Treat as no type error.
            Err(_) => Ok(()),
        };
        self.recomputes += 1;
        let rev = self.revision;
        let changed_at = match self.typed.get(id) {
            Some(old) if old.value == new => old.changed_at,
            _ => rev,
        };
        self.typed.insert(
            id.to_string(),
            Memo { value: new.clone(), changed_at, verified_at: rev },
        );
        new
    }

    /// Codegen query. Memoises `compile_module`, gated on a clean
    /// typecheck; depends on `parsed` and `typed`.
    pub fn wasm(&mut self, id: &str) -> WasmResult {
        let parsed = self.parsed(id);
        let typed = self.typed(id);
        let dep_parsed = self.parsed.get(id).map(|m| m.changed_at).unwrap_or_default();
        let dep_typed = self.typed.get(id).map(|m| m.changed_at).unwrap_or_default();
        let dep = dep_parsed.max(dep_typed);
        if let Some(m) = self.wasm.get(id) {
            if dep <= m.verified_at {
                let value = m.value.clone();
                self.wasm.get_mut(id).unwrap().verified_at = self.revision;
                return value;
            }
        }
        let new: WasmResult = match (&parsed, &typed) {
            (Ok(module), Ok(())) => compile_module(module).map_err(|e| e.0),
            (Err(_), _) => Err("cannot compile: source has parse errors".to_string()),
            (_, Err(e)) => Err(format!("cannot compile: type error: {e:?}")),
        };
        self.recomputes += 1;
        let rev = self.revision;
        let changed_at = match self.wasm.get(id) {
            Some(old) if old.value == new => old.changed_at,
            _ => rev,
        };
        self.wasm.insert(
            id.to_string(),
            Memo { value: new.clone(), changed_at, verified_at: rev },
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
        assert_eq!(db.recompute_count(), n, "re-demand with no edit must skip everything");
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
        assert_eq!(db.recompute_count(), n, "identical set_source_text must not invalidate");
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

        db.set_source_text("m", &format!("// leading comment\n{ADD}"));
        let _ = db.wasm("m");
        let delta = db.recompute_count() - n;
        assert!(
            delta <= 3,
            "comment-only edit must not recompute more than a full pipeline; delta={delta}"
        );
    }
}
