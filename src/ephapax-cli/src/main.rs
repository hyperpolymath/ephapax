#![forbid(unsafe_code)]
// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Command-Line Interface
//!
//! The main entry point for the Ephapax compiler and tools.

mod runner;

// Note: ariadne removed for now - using simple error output
use clap::{Parser, Subcommand};
use colored::Colorize;
use ephapax_driver::DriverError;
use ephapax_interp::Interpreter;
use ephapax_lexer::Lexer;
use ephapax_parser::{parse, parse_module};
use ephapax_repl::Repl;
use ephapax_syntax::{BaseTy, Decl, Ty};
// AST dump support (sexpr + json output)
#[allow(unused_imports)]
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Parser)]
#[command(name = "ephapax")]
#[command(author = "Jonathan D.A. Jewell")]
#[command(version)]
#[command(about = "Ephapax - Linear Types for Safe Memory Management", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Input file (runs the file if no subcommand given)
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

    /// Enable verbose output
    #[arg(short, long, global = true)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// Start interactive REPL
    Repl {
        /// Preload a file before starting REPL
        #[arg(short, long)]
        preload: Option<PathBuf>,
    },

    /// Run an Ephapax file
    Run {
        /// File to run
        file: PathBuf,

        /// Run with the legacy tree-walking interpreter instead of
        /// compiling to WebAssembly. The interpreter is incomplete (no
        /// `extern`, no program arguments): tests/interp-known-failures.txt
        /// lists the programs on which it disagrees with the wasm path.
        #[arg(long)]
        interp: bool,

        /// Native shared libraries to load for FFI (e.g. libgossamer.so).
        /// Interpreter only: rejected without --interp.
        #[arg(long = "ffi-lib", short = 'L')]
        ffi_libs: Vec<String>,

        /// Arguments to pass to the program (read through `import Argv`)
        #[arg(trailing_var_arg = true)]
        args: Vec<String>,
    },

    /// Type-check a file without running
    Check {
        /// Files to check
        #[arg(required = true)]
        files: Vec<PathBuf>,

        /// Rejected if given: the discipline is chosen per binding (`let`
        /// is affine, `let!` is linear), not by a global mode.
        #[arg(short, long)]
        mode: Option<String>,
    },

    /// Compile to WebAssembly.
    ///
    /// Aliased as `compile-eph` and `compile-affine` for downstream
    /// consumers (notably hypatia's `build-gossamer-gui` workflow, which
    /// probes for these names in order). All three names route to the same
    /// surface-parse → desugar → typecheck → wasm pipeline.
    /// Closes hyperpolymath/ephapax#36.
    #[command(alias = "compile-eph", alias = "compile-affine")]
    Compile {
        /// Input file
        file: PathBuf,

        /// Output file (default: input.wasm)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Optimization level. No optimiser exists, so only 0 (the
        /// default) is accepted; any other level is rejected.
        #[arg(short = 'O', long, default_value = "0")]
        opt_level: u8,

        /// Emit debug information: an `ephapax.debug.mode` custom section
        /// in the module and a `<output>.wasm.map` source map.
        #[arg(long)]
        debug: bool,

        /// Rejected if given: the discipline is chosen per binding (`let`
        /// is affine, `let!` is linear), not by a global mode.
        #[arg(short, long)]
        mode: Option<String>,

        /// Run the typed-wasm L7+L10 verifier on the emitted module.
        /// Reads the `typedwasm.ownership` custom section and
        /// reports any aliasing / linearity violations. Non-zero exit
        /// if any are found.
        #[arg(long)]
        verify_ownership: bool,

        /// Directory searched for stdlib modules (`import Argv`, ...)
        /// after the program's own directory. Defaults to
        /// $EPHAPAX_STDLIB, else the repo stdlib/ when built from
        /// source. Local files shadow stdlib modules of the same name.
        #[arg(long)]
        stdlib: Option<PathBuf>,
    },

    /// Compile an S-expression IR module to WebAssembly
    CompileSexpr {
        /// Input S-expression file
        file: PathBuf,

        /// Output file (default: input.wasm)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Show lexer tokens
    Tokens {
        /// Input file or expression
        input: String,
    },

    /// Parse and show AST
    Parse {
        /// Input file or expression
        input: String,

        /// Pretty print AST
        #[arg(short, long)]
        pretty: bool,

        /// Output format: pretty (default), sexpr, json
        #[arg(short, long, default_value = "pretty")]
        format: String,
    },

    /// Package management commands
    #[command(subcommand)]
    Package(PackageCommands),
}

#[derive(Subcommand)]
enum PackageCommands {
    /// Initialize a new Ephapax project
    Init {
        /// Project name
        name: String,

        /// Project directory (default: current directory)
        #[arg(short, long)]
        path: Option<PathBuf>,
    },

    /// Install dependencies
    Install {
        /// Package names to install (if empty, installs from ephapax.toml)
        packages: Vec<String>,
    },

    /// Search for packages
    Search {
        /// Search query
        query: String,
    },

    /// List installed packages
    List,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Some(Commands::Repl { preload }) => run_repl(preload, cli.verbose),
        Some(Commands::Run {
            file,
            interp,
            ffi_libs,
            args,
        }) => run_file(&file, interp, &ffi_libs, &args, cli.verbose),
        Some(Commands::Check { files, mode }) => check_files(&files, mode.as_deref(), cli.verbose),
        Some(Commands::Compile {
            file,
            output,
            opt_level,
            debug,
            mode,
            verify_ownership,
            stdlib,
        }) => compile_file(
            &file,
            output,
            opt_level,
            debug,
            mode.as_deref(),
            verify_ownership,
            stdlib,
            cli.verbose,
        ),
        Some(Commands::CompileSexpr { file, output }) => {
            compile_sexpr_file(&file, output, cli.verbose)
        }
        Some(Commands::Tokens { input }) => show_tokens(&input),
        Some(Commands::Parse {
            input,
            pretty,
            format,
        }) => show_parse(&input, pretty, &format),
        Some(Commands::Package(pkg_cmd)) => handle_package_command(pkg_cmd, cli.verbose),
        None => {
            // If a file is given without subcommand, run it
            if let Some(file) = cli.file {
                run_file(&file, false, &[], &[], cli.verbose)
            } else {
                // No file, start REPL
                run_repl(None, cli.verbose)
            }
        }
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{} {}", "Error:".red().bold(), e);
            ExitCode::FAILURE
        }
    }
}

fn run_repl(preload: Option<PathBuf>, verbose: bool) -> Result<(), String> {
    let config = ephapax_repl::ReplConfig {
        show_types: true,
        verbose,
        history_file: Some(".ephapax_history".to_string()),
    };

    let mut repl = Repl::with_config(config)?;

    // Preload file if specified
    if let Some(path) = preload {
        repl.load_path(&path).map_err(|e| e.to_string())?;
        println!("{} {}", "Preloaded:".green(), path.display());
    }

    repl.run()
}

/// Load a program through the one front end. On failure, print the
/// details to stderr and return the one-line summary.
fn load_program(path: &Path, stdlib: Option<PathBuf>) -> Result<ephapax_driver::Program, String> {
    if let Some(dir) = stdlib.as_ref().filter(|d| !d.is_dir()) {
        return Err(format!("--stdlib {}: not a directory", dir.display()));
    }
    let stdlib_dir = ephapax_driver::stdlib_dir(stdlib);
    ephapax_driver::load_program(path, stdlib_dir.as_deref()).map_err(|e| report_load_error(&e))
}

/// Describe a load failure. A type error is also printed to stderr with
/// its line and column; the returned one-line summary carries the error's
/// debug form, which names the exact `TypeError` variant.
fn report_load_error(e: &DriverError) -> String {
    match e {
        DriverError::Type {
            module,
            path,
            source_text,
            error,
        } => {
            report_type_error(&path.to_string_lossy(), source_text, error);
            format!("Type error in module `{module}`: {error:?}")
        }
        _ => e.to_string(),
    }
}

/// `ephapax run`: load, then execute `main`. By default the program is
/// compiled and the wasm runs under wasmtime, with `args` reachable
/// through `import Argv` and the program path as `argv[0]`. `--interp`
/// uses the legacy interpreter on the same loaded program.
fn run_file(
    path: &Path,
    interp: bool,
    ffi_libs: &[String],
    args: &[String],
    verbose: bool,
) -> Result<(), String> {
    if !interp && !ffi_libs.is_empty() {
        return Err(
            "-L/--ffi-lib only applies to the interpreter; add --interp to use it".to_string(),
        );
    }

    let program = load_program(path, None)?;
    if verbose {
        println!("{} Type check passed", "✓".green());
    }
    // The entry point is the `main` of the module that was asked for,
    // never the `main` of a module it imports.
    let main = program.root().core.decls.iter().find_map(|d| match d {
        Decl::Fn {
            name,
            params,
            ret_ty,
            ..
        } if name == "main" => Some((params.len(), ret_ty.clone())),
        _ => None,
    });
    let module = program.into_merged().map_err(|e| report_load_error(&e))?;
    let Some((n_params, ret_ty)) = main else {
        if verbose {
            println!("{} Module loaded (no main function)", "✓".green());
        }
        return Ok(());
    };

    if interp {
        return run_interp(&module, ffi_libs, verbose);
    }

    if n_params != 0 {
        return Err(format!(
            "`main` takes {n_params} parameter(s); `ephapax run` calls `main` with none"
        ));
    }

    let wasm = ephapax_wasm::compile_module(&module).map_err(|e| format!("Codegen error: {e}"))?;
    wasmparser::validate(&wasm)
        .map_err(|e| format!("emitted wasm failed structural validation: {e}"))?;

    let mut argv = vec![path.to_string_lossy().into_owned()];
    argv.extend(args.iter().cloned());
    let result = runner::run_main(&wasm, argv)?;

    // Print scalars the way the interpreter prints them.
    use wasmtime::Val;
    match (&ret_ty, result) {
        (Ty::Base(BaseTy::Unit), _) => println!("()"),
        (Ty::Base(BaseTy::Bool), Val::I32(n)) => println!("{}", n != 0),
        (Ty::Base(BaseTy::I32), Val::I32(n)) => println!("{n}"),
        (Ty::Base(BaseTy::I64), Val::I64(n)) => println!("{n}i64"),
        (Ty::Base(BaseTy::F32), Val::F32(bits)) => println!("{}f32", f32::from_bits(bits)),
        (Ty::Base(BaseTy::F64), Val::F64(bits)) => println!("{}", f64::from_bits(bits)),
        // A string, pair or sum comes back as an address in linear memory.
        _ => eprintln!(
            "{} `main` returned a non-scalar value ({:?}); it is not printed",
            "note:".yellow().bold(),
            ret_ty
        ),
    }
    Ok(())
}

/// `run --interp`: run `main` of `module` in the interpreter and print
/// its value.
fn run_interp(
    module: &ephapax_syntax::Module,
    ffi_libs: &[String],
    verbose: bool,
) -> Result<(), String> {
    let mut interp = Interpreter::new();

    // Load FFI libraries (native shared objects for __ffi() calls)
    for lib_path in ffi_libs {
        if verbose {
            println!("{} Loading FFI library: {}", "⚙".yellow(), lib_path);
        }
        interp
            .load_ffi_library(lib_path)
            .map_err(|e| format!("Failed to load FFI library '{}': {}", lib_path, e))?;
        if verbose {
            println!("{} Loaded FFI library: {}", "✓".green(), lib_path);
        }
    }

    interp.load_module(module);

    // The caller has checked that the root module has a `main`.
    match interp.call_main() {
        Ok(result) => {
            println!("{}", result);
            Ok(())
        }
        Err(e) => Err(format!("Runtime error: {}", e)),
    }
}

/// `--mode` used to be accepted and ignored. The discipline is chosen per
/// binding (`let` affine, `let!` linear), so a global mode cannot take
/// effect: the flag is rejected instead (v2 plan E1).
fn reject_mode_flag(mode: Option<&str>) -> Result<(), String> {
    match mode {
        None => Ok(()),
        Some(m) => Err(format!(
            "--mode {m} is not supported: the discipline is chosen per binding \
             (`let` is affine, `let!` is linear), so there is no global mode; \
             remove the flag"
        )),
    }
}

/// `-O` used to be accepted and ignored. No optimiser exists, so any level
/// above 0 is rejected (v2 plan E1).
fn reject_opt_level(opt_level: u8) -> Result<(), String> {
    if opt_level == 0 {
        Ok(())
    } else {
        Err(format!(
            "-O{opt_level} is not supported: no optimiser is implemented; \
             only -O0 (the default) is accepted"
        ))
    }
}

fn check_files(files: &[PathBuf], mode: Option<&str>, verbose: bool) -> Result<(), String> {
    reject_mode_flag(mode)?;

    let stdlib_dir = ephapax_driver::stdlib_dir(None);
    let mut errors = 0;
    let mut checked = 0;

    for path in files {
        match ephapax_driver::load_program(path, stdlib_dir.as_deref()) {
            Ok(program) => {
                if verbose {
                    println!(
                        "{} {} ({} declarations)",
                        "✓".green(),
                        path.display(),
                        program.root().core.decls.len()
                    );
                }
                checked += 1;
            }
            Err(e) => {
                let summary = report_load_error(&e);
                // A type error was already printed with its position.
                if !matches!(e, DriverError::Type { .. }) {
                    eprintln!("{} {}", "✗".red(), summary);
                }
                errors += 1;
            }
        }
    }

    if errors > 0 {
        Err(format!(
            "{} file(s) checked, {} error(s)",
            checked + errors,
            errors
        ))
    } else {
        println!(
            "{} {} file(s) checked successfully",
            "✓".green().bold(),
            checked
        );
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)] // CLI entry point: 8 options vs the 7 default threshold
fn compile_file(
    path: &Path,
    output: Option<PathBuf>,
    opt_level: u8,
    debug: bool,
    mode: Option<&str>,
    verify_ownership: bool,
    stdlib: Option<PathBuf>,
    verbose: bool,
) -> Result<(), String> {
    let filename = path.to_str().unwrap_or("input").to_string();

    reject_mode_flag(mode)?;
    reject_opt_level(opt_level)?;

    let program = load_program(path, stdlib)?;

    if verbose {
        println!(
            "{} Resolved {} module(s) in import graph",
            "✓".green(),
            program.modules.len()
        );
        println!(
            "{} Parsed {} declarations in root module",
            "✓".green(),
            program.root().core.decls.len()
        );
        println!("{} Type check passed", "✓".green());
    }

    finish_compile(
        program.into_merged().map_err(|e| report_load_error(&e))?,
        &filename,
        path,
        output,
        opt_level,
        debug,
        verify_ownership,
        verbose,
    )
}

/// Codegen + optional ownership verification + output write.
#[allow(clippy::too_many_arguments)] // CLI entry point: 8 options vs the 7 default threshold
fn finish_compile(
    module: ephapax_syntax::Module,
    filename: &str,
    path: &Path,
    output: Option<PathBuf>,
    opt_level: u8,
    debug: bool,
    verify_ownership: bool,
    verbose: bool,
) -> Result<(), String> {
    // Compile to WASM (with or without debug info)
    let wasm_bytes = if debug {
        ephapax_wasm::compile_module_with_debug(&module, filename)
            .map_err(|e| format!("Codegen error: {}", e))?
    } else {
        ephapax_wasm::compile_module(&module).map_err(|e| format!("Codegen error: {}", e))?
    };

    if verbose {
        println!(
            "{} Generated {} bytes of WebAssembly",
            "✓".green(),
            wasm_bytes.len()
        );
    }

    // No optimiser exists: `compile_file` rejects any `-O` above 0 before
    // this point (`reject_opt_level`), so the bytes are written as
    // generated.
    debug_assert_eq!(opt_level, 0);

    // Always-on structural validation floor: never write an invalid
    // module to disk. In-process (wasmparser) twin of the `wasm-tools
    // validate` gate; distinct from the optional semantic
    // `--verify-ownership` (L7/L10) check below.
    wasmparser::validate(&wasm_bytes)
        .map_err(|e| format!("emitted wasm failed structural validation: {}", e))?;

    // Run the typed-wasm L7+L10 verifier on the emitted module if
    // requested. Fails the build with a non-zero exit if any
    // ownership violation is found. Gated by the `typed-wasm-verify`
    // feature: when off, --verify-ownership warns and continues.
    if verify_ownership {
        #[cfg(feature = "typed-wasm-verify")]
        {
            report_ownership_verification(&wasm_bytes, verbose)?;
        }
        #[cfg(not(feature = "typed-wasm-verify"))]
        {
            eprintln!(
                "{} --verify-ownership requested but this build was \
                 compiled without the `typed-wasm-verify` feature; \
                 skipping verification (emitted wasm still carries the \
                 typedwasm.ownership section).",
                "warning:".yellow().bold()
            );
        }
    }

    // Write output
    let output_path = output.unwrap_or_else(|| path.with_extension("wasm"));
    fs::write(&output_path, &wasm_bytes)
        .map_err(|e| format!("Cannot write {}: {}", output_path.display(), e))?;

    // Write source map if debug enabled
    if debug {
        let source_map = ephapax_wasm::generate_source_map_for_module(&module, filename)
            .map_err(|e| format!("Source map generation error: {}", e))?;

        let map_path = output_path.with_extension("wasm.map");
        fs::write(&map_path, source_map)
            .map_err(|e| format!("Cannot write source map {}: {}", map_path.display(), e))?;

        if verbose {
            println!(
                "{} Generated source map: {}",
                "✓".green(),
                map_path.display()
            );
        }
    }

    println!(
        "{} Compiled to {} ({} bytes{})",
        "✓".green().bold(),
        output_path.display(),
        wasm_bytes.len(),
        if debug { ", with debug info" } else { "" }
    );

    Ok(())
}

/// Run the typed-wasm L7+L10 verifier on a compiled module and report
/// any violations. Returns `Ok(())` if the module is clean (or if it
/// has no ownership section, which both verifiers treat as fully
/// unconstrained). Returns `Err` with a user-facing message if any
/// violation is found — the caller surfaces this as a non-zero exit.
///
/// Gated by `feature = "typed-wasm-verify"`. With the feature off, the
/// call site at `compile_file` skips this function entirely and emits
/// a stderr warning instead.
#[cfg(feature = "typed-wasm-verify")]
fn report_ownership_verification(wasm_bytes: &[u8], verbose: bool) -> Result<(), String> {
    use typed_wasm_verify::{verify_from_module, VerifyError};

    match verify_from_module(wasm_bytes) {
        Ok(()) => {
            if verbose {
                println!("{} typed-wasm L7+L10 verification: clean", "✓".green());
            }
            Ok(())
        }
        Err(VerifyError::Parse(e)) => Err(format!("verifier could not parse emitted wasm: {}", e)),
        Err(VerifyError::Ownership(errs)) => {
            eprintln!(
                "{} typed-wasm verification failed: {} violation(s)",
                "✗".red().bold(),
                errs.len()
            );
            for err in &errs {
                eprintln!("  {}", err);
            }
            Err(format!("{} ownership violation(s)", errs.len()))
        }
        Err(VerifyError::Cross(errs)) => {
            // Single-module compile shouldn't ever produce Cross
            // errors (those come from cross-module verification, which
            // takes a separate callee_iface argument). Surface it
            // generically rather than silently passing.
            eprintln!(
                "{} typed-wasm cross-module verification reported {} violation(s)",
                "✗".red().bold(),
                errs.len()
            );
            for err in &errs {
                eprintln!("  {}", err);
            }
            Err(format!("{} cross-module violation(s)", errs.len()))
        }
    }
}

fn compile_sexpr_file(
    path: &PathBuf,
    output: Option<PathBuf>,
    verbose: bool,
) -> Result<(), String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let wasm = ephapax_wasm::compile_sexpr_module(&content)
        .map_err(|e| format!("Codegen error: {}", e))?;

    // Structural validation floor (see finish_compile): never write an
    // invalid module to disk.
    wasmparser::validate(&wasm)
        .map_err(|e| format!("emitted wasm failed structural validation: {}", e))?;

    let output_path = output.unwrap_or_else(|| path.with_extension("wasm"));
    fs::write(&output_path, &wasm)
        .map_err(|e| format!("Cannot write {}: {}", output_path.display(), e))?;

    if verbose {
        println!("{} Wrote {}", "✓".green(), output_path.display());
    }

    Ok(())
}

fn show_tokens(input: &str) -> Result<(), String> {
    // Try to read as file first
    let source = if std::path::Path::new(input).exists() {
        fs::read_to_string(input).map_err(|e| format!("Cannot read {}: {}", input, e))?
    } else {
        input.to_string()
    };

    let (tokens, errors) = Lexer::tokenize(&source);

    for error in &errors {
        eprintln!("{} {}", "Lexer error:".red().bold(), error);
    }

    for token in &tokens {
        println!(
            "{:4}..{:4}  {:?}",
            token.span.start, token.span.end, token.kind
        );
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!("{} lexer error(s)", errors.len()))
    }
}

fn show_parse(input: &str, pretty: bool, format: &str) -> Result<(), String> {
    // Try to read as file first
    let source = if std::path::Path::new(input).exists() {
        fs::read_to_string(input).map_err(|e| format!("Cannot read {}: {}", input, e))?
    } else {
        input.to_string()
    };

    let filename = if std::path::Path::new(input).exists() {
        input
    } else {
        "input"
    };

    // For sexpr/json, parse as module (richer output)
    if format == "sexpr" || format == "json" {
        // Try as module first (preferred for structured output)
        if let Ok(module) = parse_module(&source, filename) {
            match format {
                "sexpr" => println!("{}", ephapax_ir::module_to_sexpr(&module)),
                "json" => println!("{}", ephapax_ir::module_to_json(&module)),
                _ => unreachable!(),
            }
            return Ok(());
        }
        // Fall back to expression
        match parse(&source) {
            Ok(expr) => {
                // Wrap single expression in a synthetic module for consistent output
                let module = ephapax_syntax::Module {
                    name: smol_str::SmolStr::new(filename),
                    imports: vec![],
                    decls: vec![ephapax_syntax::Decl::Fn {
                        name: smol_str::SmolStr::new("_expr"),
                        visibility: ephapax_syntax::Visibility::Private,
                        type_params: vec![],
                        params: vec![],
                        ret_ty: ephapax_syntax::Ty::Base(ephapax_syntax::BaseTy::Unit),
                        body: expr,
                    }],
                };
                match format {
                    "sexpr" => println!("{}", ephapax_ir::module_to_sexpr(&module)),
                    "json" => println!("{}", ephapax_ir::module_to_json(&module)),
                    _ => unreachable!(),
                }
                return Ok(());
            }
            Err(errors) => {
                for error in &errors {
                    eprintln!("{} {}", "Parse error:".red().bold(), error);
                }
                return Err(format!("{} parse error(s)", errors.len()));
            }
        }
    }

    // Default: pretty/debug format
    // Try as expression first
    if let Ok(expr) = parse(&source) {
        if pretty {
            println!("{:#?}", expr);
        } else {
            println!("{:?}", expr);
        }
        return Ok(());
    }

    // Try as module
    match parse_module(&source, filename) {
        Ok(module) => {
            if pretty {
                println!("{:#?}", module);
            } else {
                println!("{:?}", module);
            }
            Ok(())
        }
        Err(errors) => {
            for error in &errors {
                eprintln!("{} {}", "Parse error:".red().bold(), error);
            }
            Err(format!("{} parse error(s)", errors.len()))
        }
    }
}

fn handle_package_command(cmd: PackageCommands, verbose: bool) -> Result<(), String> {
    match cmd {
        PackageCommands::Init { name, path } => {
            let project_path = path.unwrap_or_else(|| PathBuf::from("."));

            ephapax_package::init_project(&project_path, &name)
                .map_err(|e| format!("Failed to initialize project: {}", e))?;

            if verbose {
                println!(
                    "{} Initialized project '{}' in {}",
                    "✓".green().bold(),
                    name,
                    project_path.display()
                );
            }

            println!(
                "{} Created ephapax.toml and src/main.eph",
                "✓".green().bold()
            );
            Ok(())
        }

        PackageCommands::Install { packages } => {
            if packages.is_empty() {
                // Install from ephapax.toml
                let manifest_path = PathBuf::from("ephapax.toml");
                if !manifest_path.exists() {
                    return Err(
                        "No ephapax.toml found. Run 'ephapax package init' first.".to_string()
                    );
                }

                if verbose {
                    println!("{} Resolving dependencies...", "⚙".yellow());
                }

                let resolved = ephapax_package::install_dependencies(&manifest_path)
                    .map_err(|e| format!("Failed to install dependencies: {}", e))?;

                println!(
                    "{} Resolved {} packages:",
                    "✓".green().bold(),
                    resolved.packages.len()
                );
                for (name, pkg) in &resolved.packages {
                    println!("  {} v{}", name, pkg.version);
                }
            } else {
                return Err("Installing individual packages not yet implemented. Install from ephapax.toml for now.".to_string());
            }

            Ok(())
        }

        PackageCommands::Search { query } => {
            let registry = ephapax_package::Registry::open()
                .map_err(|e| format!("Failed to open registry: {}", e))?;

            let results = registry.search(&query);

            if results.is_empty() {
                println!("No packages found matching '{}'", query);
            } else {
                println!("Found {} package(s):", results.len());
                for name in results {
                    let versions = registry.get_versions(&name);
                    println!("  {} ({})", name, versions.join(", "));
                }
            }

            Ok(())
        }

        PackageCommands::List => {
            let registry = ephapax_package::Registry::open()
                .map_err(|e| format!("Failed to open registry: {}", e))?;

            let packages = registry.list_packages();

            if packages.is_empty() {
                println!("No packages installed.");
                println!("Install packages with: ephapax package install");
            } else {
                println!("Installed packages:");
                for name in packages {
                    let versions = registry.get_versions(&name);
                    println!("  {} ({})", name, versions.join(", "));
                }
            }

            Ok(())
        }
    }
}

fn report_type_error(filename: &str, source: &str, error: &ephapax_typing::SpannedTypeError) {
    let span = error.span;
    if span.start != 0 || span.end != 0 {
        // Calculate line/column from byte offset
        let before = &source[..span.start.min(source.len())];
        let line = before.matches('\n').count() + 1;
        let col = before.len() - before.rfind('\n').map(|p| p + 1).unwrap_or(0) + 1;
        eprintln!(
            "{}:{}:{}: {} {}",
            filename,
            line,
            col,
            "Type error:".red().bold(),
            error
        );
    } else {
        eprintln!("{}: {} in {}", "Type error".red().bold(), error, filename);
    }
}
