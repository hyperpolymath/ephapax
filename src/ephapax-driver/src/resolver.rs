// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! Multi-file module loader.
//!
//! Resolves `import a/b/c` declarations by reading the matching file
//! `<base_dir>/a/b/c.eph` relative to the root module. Walks the import
//! graph transitively, detects cycles, and returns the modules in
//! topological order (dependencies before dependents) so the rest of the
//! pipeline (desugar → typecheck → codegen) sees each module after its
//! dependencies have already populated the registries.
//!
//! Scope today is deliberately small: file-system resolution against a
//! single base directory, no package-manifest support yet, no version
//! ranges. Both the dot-form (`Foo.Bar.Baz`) and slash-form
//! (`hyperpolymath/ephapax/test`) are recognised, they map to the same
//! file path with the separator normalised to `/`.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use ephapax_parser::{parse_module, parse_surface_module};
use ephapax_surface::SurfaceModule;
use ephapax_syntax::{Import, Module};

use crate::DriverError;

/// A module as the parser produced it.
pub(crate) enum Parsed {
    /// The v2 surface grammar (needs desugaring).
    Surface(SurfaceModule),
    /// Legacy fallback: the surface parser rejected the file and the core
    /// parser accepted it. Already a core module.
    Core(Module),
}

impl Parsed {
    fn imports(&self) -> &[Import] {
        match self {
            Parsed::Surface(m) => &m.imports,
            Parsed::Core(m) => &m.imports,
        }
    }
}

pub(crate) struct ResolvedModule {
    /// Module path as written in the source (e.g. `hypatia/ui/gui`).
    pub logical_path: String,
    /// File the module was read from (the given name for an in-memory root).
    pub file_path: PathBuf,
    pub source: String,
    pub parsed: Parsed,
}

/// Walk the import graph rooted at `root_source` and return all modules in
/// topological order, dependencies first, root last. Imports are searched
/// under `base_dir` (the directory of the root file; `None` for a source
/// that has no file), then under `stdlib_dir`, this is what lets a
/// program anywhere on disk say `import Argv` and reach the shipped stdlib.
pub(crate) fn resolve(
    root_source: String,
    root_file: PathBuf,
    base_dir: Option<&Path>,
    stdlib_dir: Option<&Path>,
) -> Result<Vec<ResolvedModule>, DriverError> {
    let mut r = Resolver {
        base_dir,
        stdlib_dir,
        mod_index: None,
        loaded: HashMap::new(),
        order: Vec::new(),
        visiting: HashSet::new(),
        stack: Vec::new(),
    };
    let root_logical = first_module_declaration(&root_source).unwrap_or_else(|| {
        // No explicit `module` header, synthesise a logical path from the
        // filename stem.
        root_file
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("root")
            .to_string()
    });
    r.visit(&root_logical, Some((root_file, root_source)))?;
    // Re-arrange into the visit (post-order) order: dependencies first.
    let Resolver {
        mut loaded, order, ..
    } = r;
    Ok(order
        .into_iter()
        .filter_map(|name| loaded.remove(&name))
        .collect())
}

struct Resolver<'a> {
    base_dir: Option<&'a Path>,
    stdlib_dir: Option<&'a Path>,
    /// `declared module name → file path`, built on the first import that
    /// misses its literal path (so a program with no such import never
    /// pays for the directory walk).
    mod_index: Option<HashMap<String, PathBuf>>,
    loaded: HashMap<String, ResolvedModule>,
    order: Vec<String>,
    visiting: HashSet<String>,
    stack: Vec<String>,
}

impl Resolver<'_> {
    /// Where the import `logical` lives on disk.
    ///
    /// 1. Literal path under base_dir (`a/b/c` → `<base>/a/b/c.eph`).
    /// 2. The module-declaration index: files anywhere under base_dir that
    ///    declare `module a/b/c`, which matches existing corpora like
    ///    hypatia/src/ui/gossamer/, then the same under the stdlib
    ///    directory. Local files always shadow stdlib modules of the same
    ///    name.
    ///
    /// On a miss, the literal path is returned so the IO error names a
    /// useful location.
    fn locate(&mut self, logical: &str) -> PathBuf {
        let direct = logical_to_file_path(logical, self.base_dir.unwrap_or(Path::new("")));
        if self.base_dir.is_some() && direct.exists() {
            return direct;
        }
        let (base_dir, stdlib_dir) = (self.base_dir, self.stdlib_dir);
        let index = self.mod_index.get_or_insert_with(|| {
            let mut idx = base_dir.map(scan_module_index).unwrap_or_default();
            if let Some(sd) = stdlib_dir {
                for (name, path) in scan_module_index(sd) {
                    idx.entry(name).or_insert(path);
                }
            }
            idx
        });
        index.get(logical).cloned().unwrap_or(direct)
    }

    /// `root` is the root module's `(file, source)`; imports pass `None`
    /// and are located and read from disk.
    fn visit(&mut self, logical: &str, root: Option<(PathBuf, String)>) -> Result<(), DriverError> {
        if self.loaded.contains_key(logical) {
            return Ok(());
        }
        if self.visiting.contains(logical) {
            let mut cycle = self.stack.clone();
            cycle.push(logical.to_string());
            return Err(DriverError::Cycle { path: cycle });
        }
        self.visiting.insert(logical.to_string());
        self.stack.push(logical.to_string());

        let (file_path, source) = match root {
            Some(r) => r,
            None => {
                let file_path = self.locate(logical);
                let source = std::fs::read_to_string(&file_path).map_err(|e| DriverError::Io {
                    path: file_path.clone(),
                    message: e.to_string(),
                })?;
                (file_path, source)
            }
        };

        // Surface grammar first. A file it rejects may still be a
        // core-syntax file, so fall back to the core parser. If both
        // fail, report the surface parser's errors: the surface grammar
        // is the language, and the core parser's complaint about a
        // surface-only construct would hide the real error.
        let parsed = match parse_surface_module(&source, logical) {
            Ok(m) => Parsed::Surface(m),
            Err(errors) => match parse_module(&source, logical) {
                Ok(m) => Parsed::Core(m),
                Err(_) => {
                    return Err(DriverError::Parse {
                        path: file_path,
                        errors,
                    })
                }
            },
        };

        // Recurse into imports BEFORE inserting this module so that the
        // post-order visit places dependencies before this module.
        let deps: Vec<String> = parsed
            .imports()
            .iter()
            .map(|i| normalise_path(i.module.as_str()))
            .collect();
        for dep in &deps {
            self.visit(dep, None)?;
        }

        self.loaded.insert(
            logical.to_string(),
            ResolvedModule {
                logical_path: logical.to_string(),
                file_path,
                source,
                parsed,
            },
        );
        self.order.push(logical.to_string());
        self.stack.pop();
        self.visiting.remove(logical);
        Ok(())
    }
}

/// Walk `base_dir` recursively, reading the first `module a/b/c` line of
/// every `.eph` file we find, and return a map from declared module name
/// to file path. Files without a `module` header are skipped.
fn scan_module_index(base_dir: &Path) -> HashMap<String, PathBuf> {
    let mut idx = HashMap::new();
    let mut stack = vec![base_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().and_then(|s| s.to_str()) != Some("eph") {
                continue;
            }
            let Ok(source) = std::fs::read_to_string(&path) else {
                continue;
            };
            if let Some(name) = first_module_declaration(&source) {
                idx.entry(name).or_insert(path);
            }
        }
    }
    idx
}

fn first_module_declaration(source: &str) -> Option<String> {
    for line in source.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("module") {
            let rest = rest.trim();
            // Take everything up to a whitespace, comma, or comment marker.
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '/'))
                .unwrap_or(rest.len());
            let name = &rest[..end];
            if !name.is_empty() {
                return Some(normalise_path(name));
            }
        }
    }
    None
}

fn normalise_path(raw: &str) -> String {
    raw.replace('.', "/")
}

fn logical_to_file_path(logical: &str, base_dir: &Path) -> PathBuf {
    let mut p = base_dir.to_path_buf();
    for seg in logical.split('/') {
        p.push(seg);
    }
    p.set_extension("eph");
    p
}
