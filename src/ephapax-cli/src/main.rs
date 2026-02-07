// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Command-Line Interface
//!
//! The main entry point for the Ephapax compiler and tools.

// Note: ariadne removed for now - using simple error output
use clap::{Parser, Subcommand};
use colored::Colorize;
use ephapax_interp::Interpreter;
use ephapax_lexer::Lexer;
use ephapax_parser::{parse, parse_module};
use ephapax_repl::Repl;
use ephapax_typing::{type_check_module, type_check_module_with_mode, Mode as TypingMode};
use std::fs;
use std::path::PathBuf;
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

        /// Arguments to pass to the program
        #[arg(trailing_var_arg = true)]
        args: Vec<String>,
    },

    /// Type-check a file without running
    Check {
        /// Files to check
        #[arg(required = true)]
        files: Vec<PathBuf>,

        /// Type checking mode (linear or affine)
        #[arg(short, long, default_value = "linear")]
        mode: String,
    },

    /// Compile to WebAssembly
    Compile {
        /// Input file
        file: PathBuf,

        /// Output file (default: input.wasm)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Optimization level (0-3)
        #[arg(short = 'O', long, default_value = "0")]
        opt_level: u8,

        /// Enable debug information generation
        #[arg(long)]
        debug: bool,

        /// Compilation mode (linear or affine)
        #[arg(short, long, default_value = "linear")]
        mode: String,
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
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Some(Commands::Repl { preload }) => run_repl(preload, cli.verbose),
        Some(Commands::Run { file, args: _ }) => run_file(&file, cli.verbose),
        Some(Commands::Check { files, mode }) => check_files(&files, &mode, cli.verbose),
        Some(Commands::Compile { file, output, opt_level, debug, mode }) => {
            compile_file(&file, output, opt_level, debug, &mode, cli.verbose)
        }
        Some(Commands::CompileSexpr { file, output }) => {
            compile_sexpr_file(&file, output, cli.verbose)
        }
        Some(Commands::Tokens { input }) => show_tokens(&input),
        Some(Commands::Parse { input, pretty }) => show_parse(&input, pretty),
        None => {
            // If a file is given without subcommand, run it
            if let Some(file) = cli.file {
                run_file(&file, cli.verbose)
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
        let content = fs::read_to_string(&path)
            .map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;
        repl.load_module(&content, path.to_str().unwrap_or("preload"))
            .map_err(|e| e.to_string())?;
        println!("{} {}", "Preloaded:".green(), path.display());
    }

    repl.run()
}

fn run_file(path: &PathBuf, verbose: bool) -> Result<(), String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let filename = path.to_str().unwrap_or("input");

    // Parse as module
    let module = parse_module(&content, filename).map_err(|errors| {
        for error in &errors {
            report_parse_error(filename, &content, error);
        }
        format!("{} parse error(s)", errors.len())
    })?;

    if verbose {
        println!("{} Parsed {} declarations", "✓".green(), module.decls.len());
    }

    // Type check
    type_check_module(&module).map_err(|e| {
        report_type_error(filename, &content, &e);
        format!("Type error: {}", e)
    })?;

    if verbose {
        println!("{} Type check passed", "✓".green());
    }

    // Run with interpreter
    let mut interp = Interpreter::new();
    interp.load_module(&module);

    // Look for main function and run it
    if let Some(_main_val) = interp.get_binding("main") {
        match interp.call_main() {
            Ok(result) => {
                println!("{}", result);
                Ok(())
            }
            Err(e) => Err(format!("Runtime error: {}", e)),
        }
    } else {
        // No main, just report success
        if verbose {
            println!("{} Module loaded (no main function)", "✓".green());
        }
        Ok(())
    }
}

fn check_files(files: &[PathBuf], mode_str: &str, verbose: bool) -> Result<(), String> {
    // Parse mode argument
    let mode = match mode_str.to_lowercase().as_str() {
        "linear" => TypingMode::Linear,
        "affine" => TypingMode::Affine,
        _ => {
            return Err(format!("Invalid mode '{}'. Must be 'linear' or 'affine'", mode_str));
        }
    };

    let mut errors = 0;
    let mut checked = 0;

    for path in files {
        let content = match fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("{} Cannot read {}: {}", "✗".red(), path.display(), e);
                errors += 1;
                continue;
            }
        };

        let filename = path.to_str().unwrap_or("input");

        // Parse
        let module = match parse_module(&content, filename) {
            Ok(m) => m,
            Err(parse_errors) => {
                for error in &parse_errors {
                    report_parse_error(filename, &content, error);
                }
                errors += 1;
                continue;
            }
        };

        // Type check with specified mode
        match type_check_module_with_mode(&module, mode) {
            Ok(()) => {
                if verbose {
                    println!(
                        "{} {} ({} declarations)",
                        "✓".green(),
                        path.display(),
                        module.decls.len()
                    );
                }
                checked += 1;
            }
            Err(e) => {
                report_type_error(filename, &content, &e);
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

fn compile_file(
    path: &PathBuf,
    output: Option<PathBuf>,
    opt_level: u8,
    debug: bool,
    mode_str: &str,
    verbose: bool,
) -> Result<(), String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let filename = path.to_str().unwrap_or("input");

    // Parse mode
    let mode = match mode_str.to_lowercase().as_str() {
        "linear" => TypingMode::Linear,
        "affine" => TypingMode::Affine,
        _ => {
            return Err(format!("Invalid mode '{}'. Must be 'linear' or 'affine'", mode_str));
        }
    };

    // Parse
    let module = parse_module(&content, filename).map_err(|errors| {
        for error in &errors {
            report_parse_error(filename, &content, error);
        }
        format!("{} parse error(s)", errors.len())
    })?;

    if verbose {
        println!("{} Parsed {} declarations", "✓".green(), module.decls.len());
    }

    // Type check with mode
    type_check_module_with_mode(&module, mode).map_err(|e| {
        report_type_error(filename, &content, &e);
        format!("Type error: {}", e)
    })?;

    if verbose {
        println!("{} Type check passed ({} mode)", "✓".green(), mode_str);
    }

    // Convert typing mode to codegen mode
    let codegen_mode = match mode {
        TypingMode::Linear => ephapax_wasm::Mode::Linear,
        TypingMode::Affine => ephapax_wasm::Mode::Affine,
    };

    // Compile to WASM (with or without debug info)
    let wasm_bytes = if debug {
        ephapax_wasm::compile_module_with_debug(&module, codegen_mode, filename)
            .map_err(|e| format!("Codegen error: {}", e))?
    } else {
        ephapax_wasm::compile_module_with_mode(&module, codegen_mode)
            .map_err(|e| format!("Codegen error: {}", e))?
    };

    if verbose {
        println!(
            "{} Generated {} bytes of WebAssembly",
            "✓".green(),
            wasm_bytes.len()
        );
    }

    // Optimize if requested
    let wasm_bytes = if opt_level > 0 {
        if verbose {
            println!("{} Optimization level {} (not yet implemented)", "⚠".yellow(), opt_level);
        }
        wasm_bytes
    } else {
        wasm_bytes
    };

    // Write output
    let output_path = output.unwrap_or_else(|| path.with_extension("wasm"));
    fs::write(&output_path, &wasm_bytes)
        .map_err(|e| format!("Cannot write {}: {}", output_path.display(), e))?;

    // Write source map if debug enabled
    if debug {
        let source_map = ephapax_wasm::generate_source_map_for_module(&module, codegen_mode, filename)
            .map_err(|e| format!("Source map generation error: {}", e))?;

        let map_path = output_path.with_extension("wasm.map");
        fs::write(&map_path, source_map)
            .map_err(|e| format!("Cannot write source map {}: {}", map_path.display(), e))?;

        if verbose {
            println!("{} Generated source map: {}", "✓".green(), map_path.display());
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

fn compile_sexpr_file(
    path: &PathBuf,
    output: Option<PathBuf>,
    verbose: bool,
) -> Result<(), String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let wasm = ephapax_wasm::compile_sexpr_module(&content)
        .map_err(|e| format!("Codegen error: {}", e))?;

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

fn show_parse(input: &str, pretty: bool) -> Result<(), String> {
    // Try to read as file first
    let source = if std::path::Path::new(input).exists() {
        fs::read_to_string(input).map_err(|e| format!("Cannot read {}: {}", input, e))?
    } else {
        input.to_string()
    };

    // Try as expression first
    match parse(&source) {
        Ok(expr) => {
            if pretty {
                println!("{:#?}", expr);
            } else {
                println!("{:?}", expr);
            }
            return Ok(());
        }
        Err(_) => {}
    }

    // Try as module
    match parse_module(&source, "input") {
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

fn report_parse_error(
    _filename: &str,
    _source: &str,
    error: &ephapax_parser::ParseError,
) {
    let span = error.span();
    eprintln!(
        "{}: {} at {}..{}",
        "Parse error".red().bold(),
        error,
        span.start,
        span.end
    );
}

fn report_type_error(
    filename: &str,
    _source: &str,
    error: &ephapax_typing::TypeError,
) {
    eprintln!(
        "{}: {} in {}",
        "Type error".red().bold(),
        error,
        filename
    );
}
