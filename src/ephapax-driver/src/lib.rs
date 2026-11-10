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
use ephapax_syntax::{Decl, ExternItem, Module};
use ephapax_typing::{module_expr_types, ModuleRegistry, SpannedTypeError};
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
    /// `Fn` declarations become part of the same wasm module. A function,
    /// or an extern item, that an earlier module already declared is
    /// dropped (first-seen wins, the root first). [`check_program`]
    /// refuses a program in which that would drop a function.
    pub fn into_merged(self) -> Module {
        // Dedup keys: `fn:<name>` for a function, `extern:<abi>:<name>` for
        // an extern item (each extern fn is one wasm import, so the same
        // item from two modules must be emitted once). Extern blocks are
        // deduplicated item by item: two modules may each declare
        // different functions under one ABI, and both sets are needed.
        fn extern_key(abi: &str, item: &ExternItem) -> String {
            match item {
                ExternItem::Fn { name, .. } => format!("extern:{abi}:fn:{name}"),
                ExternItem::Type { name } => format!("extern:{abi}:type:{name}"),
            }
        }
        let mut modules = self.modules;
        let mut merged = modules
            .pop()
            .expect("a program has at least its root module")
            .core;
        // The merged module is the whole program: nothing is left to
        // import. Codegen type-checks it on its own, and a kept
        // `import lib(inc)` would not resolve there.
        merged.imports.clear();
        let mut seen = std::collections::HashSet::new();
        for decl in &merged.decls {
            match decl {
                Decl::Fn { name, .. } => {
                    seen.insert(format!("fn:{name}"));
                }
                Decl::Extern { abi, items } => {
                    seen.extend(items.iter().map(|i| extern_key(abi, i)));
                }
                _ => {}
            }
        }
        for dep in modules {
            for decl in dep.core.decls {
                match decl {
                    Decl::Fn { ref name, .. } => {
                        if seen.insert(format!("fn:{name}")) {
                            merged.decls.push(decl);
                        }
                    }
                    Decl::Extern { abi, mut items } => {
                        items.retain(|i| seen.insert(extern_key(&abi, i)));
                        if !items.is_empty() {
                            merged.decls.push(Decl::Extern { abi, items });
                        }
                    }
                    other => merged.decls.push(other),
                }
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
    parse_source(&source, &root.to_string_lossy(), root.parent(), stdlib_dir)
}

/// [`parse_program`] for a root module held in memory (an editor buffer,
/// a REPL line). `name` stands in for its file name; `base_dir` is where
/// its imports are searched (`None`: only `stdlib_dir`; the empty path,
/// which is the parent of a bare file name: the current directory).
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
    let mut types = Vec::with_capacity(program.modules.len());
    for m in &program.modules {
        types.push(module_expr_types(&m.core, &mut registry).map_err(|error| {
            DriverError::Type {
                module: m.core.name.to_string(),
                path: m.file_path.clone(),
                source_text: m.source.clone(),
                error: Box::new(error),
            }
        })?);
    }
    // A program is one wasm module, and codegen finds a callee by its
    // bare name (`Program::into_merged`). If two modules declared a
    // function or an extern function of the same name, the callers in one
    // of them would run the declaration of the other.
    // snip: an error; lift it with module-qualified names in the merge.
    // `None` is a function; an extern function has its ABI and item.
    let mut declared = std::collections::HashMap::new();
    for m in &program.modules {
        let mut callables = Vec::new();
        for decl in &m.core.decls {
            match decl {
                Decl::Fn { name, .. } => callables.push((name, None)),
                Decl::Extern { abi, items } => {
                    callables.extend(items.iter().filter_map(|item| match item {
                        ExternItem::Fn { name, .. } => Some((name, Some((abi, item)))),
                        ExternItem::Type { .. } => None,
                    }))
                }
                _ => {}
            }
        }
        for (name, ext) in callables {
            let Some((first, first_ext)) = declared.insert(name, (&m.logical_path, ext)) else {
                continue;
            };
            // Two modules may declare the same host import: it is one
            // wasm import (`into_merged` keeps one).
            if first == &m.logical_path || (ext.is_some() && first_ext == ext) {
                continue;
            }
            return Err(DriverError::Unsupported {
                path: m.file_path.clone(),
                error: CodegenError(format!(
                    "{}: function `{name}` is declared in module `{first}` and in \
                     module `{}` (a program compiles to one wasm module, which \
                     holds one function of each name)",
                    ephapax_wasm::UNSUPPORTED_PREFIX,
                    m.logical_path
                )),
            });
        }
    }
    // With the types, so a limit of the typed lowering (a `match` on a
    // 64-bit component) is an error here and not only in `compile`.
    for (m, types) in program.modules.iter().zip(&types) {
        ephapax_wasm::validate_supported_typed(&m.core, types).map_err(|error| {
            DriverError::Unsupported {
                path: m.file_path.clone(),
                error,
            }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn extern_fn_names(module: &Module) -> Vec<String> {
        let mut names = Vec::new();
        for decl in &module.decls {
            if let Decl::Extern { items, .. } = decl {
                for item in items {
                    if let ExternItem::Fn { name, .. } = item {
                        names.push(name.to_string());
                    }
                }
            }
        }
        names.sort();
        names
    }

    /// Two modules may declare different functions under one ABI. The
    /// merge used to keep the first block and drop the other whole.
    #[test]
    fn merge_keeps_extern_items_of_every_module() {
        let dir = tempfile::tempdir().expect("tempdir");
        let write = |name: &str, text: &str| {
            std::fs::write(dir.path().join(name), text).expect("write module")
        };
        write(
            "lib.eph",
            "module lib\n\nextern \"env\" {\n  fn shared(): I32\n  fn only_lib(): I32\n}\n",
        );
        write(
            "app.eph",
            "module app\n\nimport lib\n\nextern \"env\" {\n  fn shared(): I32\n  fn only_app(): I32\n}\n\n\
             fn main(): I32 = only_app() + lib.only_lib() + shared()\n",
        );
        let program = load_program(&dir.path().join("app.eph"), None).expect("loads");
        let merged = program.into_merged();
        // `shared` once (the root's), and each module's own item.
        assert_eq!(extern_fn_names(&merged), ["only_app", "only_lib", "shared"]);
        ephapax_wasm::compile_module(&merged).expect("the merged module compiles");
    }

    /// A source with no directory resolves imports in the stdlib only: a
    /// miss is an error, not a read relative to the working directory.
    #[test]
    fn fileless_source_does_not_read_the_working_directory() {
        // The test runs in the crate directory, which has a `Cargo.toml`;
        // `import Cargo` must not turn into a read of `./Cargo.eph`.
        let err = parse_source(
            "module m\n\nimport Cargo\n\nfn main(): I32 = 0\n",
            "m",
            None,
            None,
        )
        .expect_err("no such module");
        assert!(
            matches!(&err, DriverError::Io { message, .. } if message.contains("module not found")),
            "{err}"
        );
    }

    /// Two modules that each declare `helper` cannot share one wasm
    /// module. The merge used to keep one `helper` for both, without a
    /// diagnostic.
    #[test]
    fn same_function_name_in_two_modules_is_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let write = |name: &str, text: &str| {
            std::fs::write(dir.path().join(name), text).expect("write module")
        };
        write(
            "deep.eph",
            "module deep\n\nfn helper(n: I32): I32 = n + 100\n\n\
             pub fn deep_val(n: I32): I32 = helper(n)\n",
        );
        write(
            "app.eph",
            "module app\n\nimport deep\n\nfn helper(n: I32): I32 = n + 7\n\n\
             fn main(): I32 = helper(1) + deep_val(0)\n",
        );
        let refused = || {
            let err = load_program(&dir.path().join("app.eph"), None).expect_err("refused");
            assert!(
                matches!(&err, DriverError::Unsupported { error, .. } if error.0.contains("`helper`")),
                "{err}"
            );
        };
        refused();
        // An extern function is in the same namespace: under another name
        // kind, and under another ABI.
        let app_calls_deep = "module app\n\nimport deep\n\nfn main(): I32 = deep_val(0)\n";
        for helper in [
            "fn helper(n: I32): I32 = n + 7",
            "extern \"other\" {\n  fn helper(n: I32): I32\n}",
        ] {
            write(
                "deep.eph",
                "module deep\n\nextern \"env\" {\n  fn helper(n: I32): I32\n}\n\n\
                 pub fn deep_val(n: I32): I32 = helper(n)\n",
            );
            write("app.eph", &format!("{app_calls_deep}\n{helper}\n"));
            refused();
        }
    }

    /// `foo.bar` and `foo/bar` name the same module: an import may use
    /// either spelling, whichever one the header uses.
    #[test]
    fn import_and_header_may_spell_the_module_path_differently() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::create_dir(dir.path().join("foo")).expect("mkdir");
        let write = |name: &str, text: &str| {
            std::fs::write(dir.path().join(name), text).expect("write module")
        };
        write(
            "foo/bar.eph",
            "module foo/bar\n\npub fn inc(n: I32): I32 = n + 1\n",
        );
        write(
            "foo/baz.eph",
            "module foo.baz\n\npub fn dec(n: I32): I32 = n - 1\n",
        );
        for imports in [
            "import foo.bar\nimport foo/baz",
            "import foo.bar(inc)\nimport foo/baz(dec)",
        ] {
            write(
                "app.eph",
                &format!("module app\n\n{imports}\n\nfn main(): I32 = inc(dec(41))\n"),
            );
            load_program(&dir.path().join("app.eph"), None)
                .unwrap_or_else(|e| panic!("`{imports}`: {e}"));
        }
    }

    /// The module index reads the header the parser reads: a line in a
    /// comment that looks like a header is not one.
    #[test]
    fn module_index_ignores_a_header_inside_a_comment() {
        let dir = tempfile::tempdir().expect("tempdir");
        let write = |name: &str, text: &str| {
            std::fs::write(dir.path().join(name), text).expect("write module")
        };
        // Not at the literal path `Real.eph`: only the index finds it.
        write(
            "impl.eph",
            "/*\nmodule Example\n*/\nmodule Real\n\npub fn inc(n: I32): I32 = n + 1\n",
        );
        write(
            "app.eph",
            "module app\n\nimport Real\n\nfn main(): I32 = inc(41)\n",
        );
        load_program(&dir.path().join("app.eph"), None).expect("loads");
    }

    /// `module_size(x)` is not a `module` header.
    #[test]
    fn module_keyword_needs_a_word_boundary() {
        let program = parse_source("fn module_size(x: I32): I32 = x\n", "app.eph", None, None)
            .expect("parses");
        assert_eq!(program.root().logical_path, "app");
    }
}
