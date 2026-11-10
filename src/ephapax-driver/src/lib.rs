#![forbid(unsafe_code)]
// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! The one front end for every Ephapax tool (v2 plan rung E3).
//!
//! `check`, `compile`, `run`, the REPL, the LSP and the query engine all
//! load a program through this crate, so they accept and reject the same
//! programs:
//!
//! ```text
//! resolve imports → parse (surface, core fallback) → desugar
//!                 → type-check → reject constructs codegen cannot lower
//! ```
//!
//! [`parse_program`] / [`parse_source`] run the first three steps and
//! [`check_program`] the last two; [`load_program`] / [`load_source`] run
//! all five.

mod resolver;

use std::path::{Path, PathBuf};

use ephapax_desugar::{DataRegistry, DesugarError, Desugarer};
use ephapax_parser::ParseError;
use ephapax_syntax::{Decl, Module};
use ephapax_typing::{type_check_module_with_registry, ModuleRegistry, SpannedTypeError};
use ephapax_wasm::CodegenError;

/// One module of a loaded program, desugared to core.
#[derive(Debug, Clone)]
pub struct LoadedModule {
    /// Module path as written in the source (e.g. `hypatia/ui/gui`).
    pub logical_path: String,
    /// File the module was read from (the given name for an in-memory root).
    pub file_path: PathBuf,
    /// Source text; spans in `core` index into it.
    pub source: String,
    pub core: Module,
}

/// A program: the root module and everything it imports, dependencies
/// first, root last.
#[derive(Debug, Clone)]
pub struct Program {
    pub modules: Vec<LoadedModule>,
}

impl Program {
    /// The module the program was loaded from.
    pub fn root(&self) -> &LoadedModule {
        self.modules
            .last()
            .expect("a program has at least its root module")
    }

    /// Merge every imported module into the root, for codegen and the
    /// interpreter. Wasm produces a single binary; each imported module's
    /// `Fn` declarations become part of the same wasm module. Duplicate
    /// fn / extern-block names across modules are dropped (first-seen
    /// wins, the root first).
    pub fn into_merged(self) -> Module {
        // Dedup keys: `fn:<name>` for functions, `extern:<abi>` for whole
        // extern blocks (an extern block emits one wasm import per fn item;
        // re-emitting the same ABI block from another module would produce
        // duplicate imports).
        fn dedup_key(d: &Decl) -> Option<String> {
            match d {
                Decl::Fn { name, .. } => Some(format!("fn:{name}")),
                Decl::Extern { abi, .. } => Some(format!("extern:{abi}")),
                _ => None,
            }
        }
        let mut modules = self.modules;
        let mut merged = modules
            .pop()
            .expect("a program has at least its root module")
            .core;
        let mut seen: std::collections::HashSet<String> =
            merged.decls.iter().filter_map(dedup_key).collect();
        for dep in modules {
            for decl in dep.core.decls {
                if let Some(key) = dedup_key(&decl) {
                    if !seen.insert(key) {
                        continue;
                    }
                }
                merged.decls.push(decl);
            }
        }
        merged
    }
}

/// Why a program did not load.
#[derive(Debug, Clone, thiserror::Error)]
pub enum DriverError {
    #[error("cannot read {}: {message}", path.display())]
    Io { path: PathBuf, message: String },

    #[error("import cycle: {}", path.join(" -> "))]
    Cycle { path: Vec<String> },

    #[error("{}: Parse error: {}", path.display(), join_parse_errors(errors))]
    Parse {
        path: PathBuf,
        errors: Vec<ParseError>,
    },

    #[error("Desugar error in {}: {error}", path.display())]
    Desugar { path: PathBuf, error: DesugarError },

    /// `source_text` is the text of the module the error is in
    /// (`error.span` indexes into it).
    #[error("Type error in module `{module}`: {error}")]
    Type {
        module: String,
        path: PathBuf,
        source_text: String,
        error: Box<SpannedTypeError>,
    },

    /// The program type-checks but uses a construct with no wasm lowering.
    #[error("{}: Codegen error: {error}", path.display())]
    Unsupported { path: PathBuf, error: CodegenError },
}

/// Every parse error with its byte span, on one line.
fn join_parse_errors(errors: &[ParseError]) -> String {
    errors
        .iter()
        .map(|e| format!("{e} at {}..{}", e.span().start, e.span().end))
        .collect::<Vec<_>>()
        .join("; ")
}

/// The stdlib search directory: `explicit` (a `--stdlib` flag) >
/// `$EPHAPAX_STDLIB` > the source tree's `stdlib/` (dev builds). `None` if
/// the chosen one is not a directory.
pub fn stdlib_dir(explicit: Option<PathBuf>) -> Option<PathBuf> {
    explicit
        .or_else(|| std::env::var_os("EPHAPAX_STDLIB").map(PathBuf::from))
        .or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../stdlib")
                .canonicalize()
                .ok()
        })
        .filter(|p| p.is_dir())
}

/// Resolve imports, parse and desugar the program rooted at the file
/// `root`. Imports are searched next to `root`, then in `stdlib_dir`.
pub fn parse_program(root: &Path, stdlib_dir: Option<&Path>) -> Result<Program, DriverError> {
    let source = std::fs::read_to_string(root).map_err(|e| DriverError::Io {
        path: root.to_path_buf(),
        message: e.to_string(),
    })?;
    // A bare file name has the empty path as its parent: use the current
    // directory, so the module index of that directory is still scanned.
    let base_dir = root
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    parse_source(&source, &root.to_string_lossy(), Some(base_dir), stdlib_dir)
}

/// [`parse_program`] for a root module held in memory (an editor buffer,
/// a REPL line). `name` stands in for its file name; `base_dir` is where
/// its imports are searched (`None`: only `stdlib_dir`).
pub fn parse_source(
    source: &str,
    name: &str,
    base_dir: Option<&Path>,
    stdlib_dir: Option<&Path>,
) -> Result<Program, DriverError> {
    let resolved = resolver::resolve(
        source.to_string(),
        PathBuf::from(name),
        base_dir,
        stdlib_dir,
    )?;

    // Chain a single DataRegistry across all modules so imported `data`
    // and `extern type` items are visible.
    let mut desugarer = Desugarer::with_registry(DataRegistry::new());
    let mut modules = Vec::with_capacity(resolved.len());
    for m in resolved {
        let core = match m.parsed {
            resolver::Parsed::Surface(surface) => {
                desugarer
                    .desugar_module(&surface)
                    .map_err(|error| DriverError::Desugar {
                        path: m.file_path.clone(),
                        error,
                    })?
            }
            resolver::Parsed::Core(core) => core,
        };
        modules.push(LoadedModule {
            logical_path: m.logical_path,
            file_path: m.file_path,
            source: m.source,
            core,
        });
    }
    Ok(Program { modules })
}

/// Type-check every module (a single registry is chained so imports
/// resolve), then run the same unsupported-construct validation codegen
/// runs, so no tool accepts a program that `compile` must reject.
pub fn check_program(program: &Program) -> Result<(), DriverError> {
    let mut registry = ModuleRegistry::new();
    for m in &program.modules {
        type_check_module_with_registry(&m.core, &mut registry).map_err(|error| {
            DriverError::Type {
                module: m.core.name.to_string(),
                path: m.file_path.clone(),
                source_text: m.source.clone(),
                error: Box::new(error),
            }
        })?;
    }
    for m in &program.modules {
        ephapax_wasm::validate_supported(&m.core).map_err(|error| DriverError::Unsupported {
            path: m.file_path.clone(),
            error,
        })?;
    }
    Ok(())
}

/// [`parse_program`] then [`check_program`].
pub fn load_program(root: &Path, stdlib_dir: Option<&Path>) -> Result<Program, DriverError> {
    let program = parse_program(root, stdlib_dir)?;
    check_program(&program)?;
    Ok(program)
}

/// [`parse_source`] then [`check_program`].
pub fn load_source(
    source: &str,
    name: &str,
    base_dir: Option<&Path>,
    stdlib_dir: Option<&Path>,
) -> Result<Program, DriverError> {
    let program = parse_source(source, name, base_dir, stdlib_dir)?;
    check_program(&program)?;
    Ok(program)
}
