// SPDX-License-Identifier: PMPL-1.0-or-later
//
//! Multi-file module loader for `compile-eph`.
//!
//! Resolves `import a/b/c` declarations by reading the matching file
//! `<base_dir>/a/b/c.eph` relative to the root module. Walks the import
//! graph transitively, detects cycles, and returns the modules in
//! topological order (dependencies before dependents) so the compiler
//! pipeline (desugar → typecheck → codegen) sees each module after its
//! dependencies have already populated the registries.
//!
//! Scope today is deliberately small: file-system resolution against a
//! single base directory, no package-manifest support yet, no version
//! ranges. Both the dot-form (`Foo.Bar.Baz`) and slash-form
//! (`hyperpolymath/ephapax/test`) are recognised — they map to the same
//! file path with the separator normalised to `/`.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use ephapax_parser::parse_surface_module;
use ephapax_surface::SurfaceModule;

#[derive(Debug)]
pub struct LoadedModule {
    /// Module path as written in the source (e.g. `hypatia/ui/gui`).
    #[allow(dead_code)]
    pub logical_path: String,
    /// Resolved file path on disk.
    pub file_path: PathBuf,
    /// Source contents (kept for error reporting).
    #[allow(dead_code)]
    pub source: String,
    /// Parsed surface module.
    pub surface: SurfaceModule,
}

#[derive(Debug)]
pub enum ResolveError {
    Io { path: PathBuf, message: String },
    Parse { path: PathBuf, message: String },
    Cycle { path: Vec<String> },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolveError::Io { path, message } => {
                write!(f, "cannot read {}: {}", path.display(), message)
            }
            ResolveError::Parse { path, message } => {
                write!(f, "{}: parse error: {}", path.display(), message)
            }
            ResolveError::Cycle { path } => {
                write!(f, "import cycle: {}", path.join(" -> "))
            }
        }
    }
}

impl std::error::Error for ResolveError {}

/// Walk the import graph rooted at `root_path` and return all loaded
/// modules in topological order — dependencies first, root last. Search
/// for imports under `base_dir` (typically the directory containing the
/// root file).
pub fn load_program(
    root_path: &Path,
    base_dir: &Path,
) -> Result<Vec<LoadedModule>, ResolveError> {
    let mut loaded: HashMap<String, LoadedModule> = HashMap::new();
    let mut order: Vec<String> = Vec::new();
    let mut visiting: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = Vec::new();

    // Build a `declared module name → file path` index by scanning the
    // base directory for .eph files. Imports try the literal path first
    // (`a/b/c.eph` under base_dir); if that misses, they fall back to
    // this map. This lets files live anywhere in the tree as long as
    // they declare their module name in a `module a/b/c` header — which
    // matches existing corpora like hypatia/src/ui/gossamer/.
    let mod_index = scan_module_index(base_dir);

    let root_module_path = root_module_path_from_source(root_path)?;
    visit(
        &root_module_path,
        Some(root_path),
        base_dir,
        &mod_index,
        &mut loaded,
        &mut order,
        &mut visiting,
        &mut stack,
    )?;
    // Re-arrange into the visit (post-order) order: dependencies first.
    let mut result = Vec::with_capacity(order.len());
    for name in order {
        if let Some(m) = loaded.remove(&name) {
            result.push(m);
        }
    }
    Ok(result)
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
                .find(|c: char| {
                    !(c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '/')
                })
                .unwrap_or(rest.len());
            let name = &rest[..end];
            if !name.is_empty() {
                return Some(normalise_path(name));
            }
        }
    }
    None
}

fn visit(
    logical: &str,
    explicit_file: Option<&Path>,
    base_dir: &Path,
    mod_index: &HashMap<String, PathBuf>,
    loaded: &mut HashMap<String, LoadedModule>,
    order: &mut Vec<String>,
    visiting: &mut HashSet<String>,
    stack: &mut Vec<String>,
) -> Result<(), ResolveError> {
    if loaded.contains_key(logical) {
        return Ok(());
    }
    if visiting.contains(logical) {
        let mut cycle = stack.clone();
        cycle.push(logical.to_string());
        return Err(ResolveError::Cycle { path: cycle });
    }
    visiting.insert(logical.to_string());
    stack.push(logical.to_string());

    let file_path = match explicit_file {
        Some(p) => p.to_path_buf(),
        None => {
            // 1) Literal path under base_dir (`a/b/c` → `<base>/a/b/c.eph`).
            let direct = logical_to_file_path(logical, base_dir);
            if direct.exists() {
                direct
            } else if let Some(p) = mod_index.get(logical) {
                // 2) Module-declaration index built by walking base_dir.
                p.clone()
            } else {
                // Fall back to the literal path so the IO error names a
                // useful location.
                direct
            }
        }
    };

    let source = std::fs::read_to_string(&file_path).map_err(|e| ResolveError::Io {
        path: file_path.clone(),
        message: e.to_string(),
    })?;

    let surface =
        parse_surface_module(&source, logical).map_err(|errs| ResolveError::Parse {
            path: file_path.clone(),
            message: errs
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
                .join("; "),
        })?;

    // Recurse into imports BEFORE inserting this module so that the
    // post-order visit places dependencies before this module.
    let deps: Vec<String> = surface
        .imports
        .iter()
        .map(|i| normalise_path(i.module.as_str()))
        .collect();
    for dep in &deps {
        visit(dep, None, base_dir, mod_index, loaded, order, visiting, stack)?;
    }

    loaded.insert(
        logical.to_string(),
        LoadedModule {
            logical_path: logical.to_string(),
            file_path,
            source,
            surface,
        },
    );
    order.push(logical.to_string());
    stack.pop();
    visiting.remove(logical);
    Ok(())
}

fn root_module_path_from_source(root_path: &Path) -> Result<String, ResolveError> {
    let source = std::fs::read_to_string(root_path).map_err(|e| ResolveError::Io {
        path: root_path.to_path_buf(),
        message: e.to_string(),
    })?;
    for line in source.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("module") {
            let rest = rest.trim();
            if let Some(end) = rest.find(|c: char| {
                !(c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '/')
            }) {
                return Ok(normalise_path(&rest[..end]));
            } else if !rest.is_empty() {
                return Ok(normalise_path(rest));
            }
        }
    }
    // No explicit `module` header — synthesise a logical path from the
    // filename stem.
    Ok(root_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("root")
        .to_string())
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
