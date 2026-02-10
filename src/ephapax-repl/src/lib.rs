// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax REPL (Read-Eval-Print Loop)
//!
//! Interactive environment for exploring and testing Ephapax code.

use colored::Colorize;
use ephapax_interp::{Interpreter, RuntimeError, Value};
use ephapax_lexer::Lexer;
use ephapax_parser::{parse, parse_module, ParseError};
use ephapax_syntax::Ty;
use ephapax_typing::{type_check, TypeError};
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{DefaultEditor, Editor};

/// REPL configuration
pub struct ReplConfig {
    /// Show types after evaluation
    pub show_types: bool,
    /// Enable verbose output
    pub verbose: bool,
    /// History file path
    pub history_file: Option<String>,
}

impl Default for ReplConfig {
    fn default() -> Self {
        Self {
            show_types: true,
            verbose: false,
            history_file: Some(".ephapax_history".to_string()),
        }
    }
}

/// REPL state
pub struct Repl {
    interpreter: Interpreter,
    config: ReplConfig,
    editor: Editor<(), DefaultHistory>,
}

impl Repl {
    /// Create a new REPL with default configuration
    pub fn new() -> Result<Self, String> {
        Self::with_config(ReplConfig::default())
    }

    /// Create a new REPL with custom configuration
    pub fn with_config(config: ReplConfig) -> Result<Self, String> {
        let mut editor = DefaultEditor::new().map_err(|e| e.to_string())?;

        // Load history if available
        if let Some(ref path) = config.history_file {
            let _ = editor.load_history(path);
        }

        Ok(Self {
            interpreter: Interpreter::new(),
            config,
            editor,
        })
    }

    /// Run the REPL loop
    pub fn run(&mut self) -> Result<(), String> {
        self.print_banner();

        loop {
            match self.editor.readline("ephapax> ") {
                Ok(line) => {
                    let line = line.trim();

                    if line.is_empty() {
                        continue;
                    }

                    // Add to history
                    let _ = self.editor.add_history_entry(line);

                    // Handle commands
                    if line.starts_with(':') {
                        match self.handle_command(line) {
                            CommandResult::Continue => continue,
                            CommandResult::Quit => break,
                            CommandResult::Error(e) => {
                                eprintln!("{} {}", "Error:".red().bold(), e);
                                continue;
                            }
                        }
                    }

                    // Try to parse and evaluate
                    self.eval_line(line);
                }
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    continue;
                }
                Err(ReadlineError::Eof) => {
                    println!("Goodbye!");
                    break;
                }
                Err(err) => {
                    eprintln!("{} {:?}", "Error:".red().bold(), err);
                    break;
                }
            }
        }

        // Save history
        if let Some(ref path) = self.config.history_file {
            let _ = self.editor.save_history(path);
        }

        Ok(())
    }

    fn print_banner(&self) {
        println!("{}", "╔══════════════════════════════════════════════════╗".cyan());
        println!("{}", "║     Ephapax - Linear Types for Safe Memory       ║".cyan());
        println!("{}", "║                   v0.1.0                         ║".cyan());
        println!("{}", "╚══════════════════════════════════════════════════╝".cyan());
        println!();
        println!("Type {} for help, {} to quit", ":help".green(), ":quit".green());
        println!();
    }

    fn handle_command(&mut self, line: &str) -> CommandResult {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let cmd = parts.first().unwrap_or(&"");

        match *cmd {
            ":quit" | ":q" | ":exit" => CommandResult::Quit,
            ":help" | ":h" | ":?" => {
                self.print_help();
                CommandResult::Continue
            }
            ":type" | ":t" => {
                if parts.len() < 2 {
                    return CommandResult::Error("Usage: :type <expression>".to_string());
                }
                let expr_str = parts[1..].join(" ");
                self.show_type(&expr_str);
                CommandResult::Continue
            }
            ":load" | ":l" => {
                if parts.len() < 2 {
                    return CommandResult::Error("Usage: :load <filename>".to_string());
                }
                match std::fs::read_to_string(parts[1]) {
                    Ok(content) => {
                        self.load_file(parts[1], &content);
                    }
                    Err(e) => {
                        eprintln!("{} Cannot read file: {}", "Error:".red().bold(), e);
                    }
                }
                CommandResult::Continue
            }
            ":reset" => {
                self.interpreter = Interpreter::new();
                println!("Environment reset.");
                CommandResult::Continue
            }
            ":tokens" => {
                if parts.len() < 2 {
                    return CommandResult::Error("Usage: :tokens <expression>".to_string());
                }
                let expr_str = parts[1..].join(" ");
                self.show_tokens(&expr_str);
                CommandResult::Continue
            }
            ":verbose" => {
                self.config.verbose = !self.config.verbose;
                println!("Verbose mode: {}", if self.config.verbose { "on" } else { "off" });
                CommandResult::Continue
            }
            _ => CommandResult::Error(format!("Unknown command: {}", cmd)),
        }
    }

    fn print_help(&self) {
        println!("{}", "Commands:".yellow().bold());
        println!("  {}  {:30} {}", ":help".green(), "(:h, :?)".dimmed(), "Show this help");
        println!("  {}  {:30} {}", ":quit".green(), "(:q, :exit)".dimmed(), "Exit the REPL");
        println!("  {}  {:30} {}", ":type <expr>".green(), "(:t)".dimmed(), "Show type of expression");
        println!("  {}  {:30} {}", ":load <file>".green(), "(:l)".dimmed(), "Load a file");
        println!("  {}  {:30} {}", ":reset".green(), "".dimmed(), "Reset the environment");
        println!("  {}  {:30} {}", ":tokens <expr>".green(), "".dimmed(), "Show lexer tokens");
        println!("  {}  {:30} {}", ":verbose".green(), "".dimmed(), "Toggle verbose mode");
        println!();
        println!("{}", "Examples:".yellow().bold());
        println!("  let x = 42 in x");
        println!("  fn(x: I32) -> x");
        println!("  if true then 1 else 0");
        println!("  region r {{ String.new@r(\"hello\") }}");
    }

    fn eval_line(&mut self, line: &str) {
        // Try parsing as expression
        match parse(line) {
            Ok(expr) => {
                // Type check (optional in REPL mode)
                if self.config.verbose {
                    match type_check(&expr) {
                        Ok(ty) => println!("{} {}", "Type:".blue(), format_type(&ty)),
                        Err(e) => {
                            eprintln!("{} {}", "Type warning:".yellow(), e);
                        }
                    }
                }

                // Evaluate
                match self.interpreter.eval(&expr) {
                    Ok(value) => {
                        if self.config.show_types {
                            let ty = value.to_type();
                            println!("{} {} {}", value, ":".dimmed(), format_type(&ty).dimmed());
                        } else {
                            println!("{}", value);
                        }
                    }
                    Err(e) => {
                        eprintln!("{} {}", "Runtime error:".red().bold(), e);
                    }
                }
            }
            Err(errors) => {
                // Try parsing as declaration/module
                let module_src = format!("{}\n", line);
                match parse_module(&module_src, "repl") {
                    Ok(module) => {
                        self.interpreter.load_module(&module);
                        println!("{}", "Loaded.".green());
                    }
                    Err(_) => {
                        // Show parse errors
                        for error in errors {
                            eprintln!("{} {}", "Parse error:".red().bold(), error);
                        }
                    }
                }
            }
        }
    }

    fn show_type(&mut self, expr_str: &str) {
        match parse(expr_str) {
            Ok(expr) => match type_check(&expr) {
                Ok(ty) => println!("{}", format_type(&ty)),
                Err(e) => eprintln!("{} {}", "Type error:".red().bold(), e),
            },
            Err(errors) => {
                for error in errors {
                    eprintln!("{} {}", "Parse error:".red().bold(), error);
                }
            }
        }
    }

    fn show_tokens(&self, expr_str: &str) {
        let (tokens, errors) = Lexer::tokenize(expr_str);

        if !errors.is_empty() {
            for error in errors {
                eprintln!("{} {}", "Lexer error:".red().bold(), error);
            }
        }

        for token in tokens {
            println!("{:?} @ {:?}", token.kind, token.span);
        }
    }

    fn load_file(&mut self, filename: &str, content: &str) {
        match parse_module(content, filename) {
            Ok(module) => {
                // Type check module
                match ephapax_typing::type_check_module(&module) {
                    Ok(()) => {
                        self.interpreter.load_module(&module);
                        println!("{} {} ({} declarations)",
                            "Loaded".green(),
                            filename,
                            module.decls.len()
                        );
                    }
                    Err(e) => {
                        eprintln!("{} {}", "Type error:".red().bold(), e);
                    }
                }
            }
            Err(errors) => {
                for error in errors {
                    eprintln!("{} {}", "Parse error:".red().bold(), error);
                }
            }
        }
    }

    /// Evaluate a single expression and return the result
    pub fn eval_expr(&mut self, source: &str) -> Result<Value, ReplError> {
        let expr = parse(source).map_err(ReplError::Parse)?;
        type_check(&expr).map_err(ReplError::Type)?;
        self.interpreter.eval(&expr).map_err(ReplError::Runtime)
    }

    /// Load a module into the REPL
    pub fn load_module(&mut self, source: &str, name: &str) -> Result<(), ReplError> {
        let module = parse_module(source, name).map_err(ReplError::Parse)?;
        ephapax_typing::type_check_module(&module).map_err(ReplError::Type)?;
        self.interpreter.load_module(&module);
        Ok(())
    }
}

impl Default for Repl {
    fn default() -> Self {
        Self::new().expect("Failed to create REPL")
    }
}

/// Command result
enum CommandResult {
    Continue,
    Quit,
    Error(String),
}

/// REPL error types
#[derive(Debug)]
pub enum ReplError {
    Parse(Vec<ParseError>),
    Type(TypeError),
    Runtime(RuntimeError),
}

impl std::fmt::Display for ReplError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplError::Parse(errors) => {
                write!(f, "Parse errors: ")?;
                for e in errors {
                    write!(f, "{}, ", e)?;
                }
                Ok(())
            }
            ReplError::Type(e) => write!(f, "Type error: {}", e),
            ReplError::Runtime(e) => write!(f, "Runtime error: {}", e),
        }
    }
}

impl std::error::Error for ReplError {}

/// Format a type for display
fn format_type(ty: &Ty) -> String {
    match ty {
        Ty::Base(base) => format!("{:?}", base),
        Ty::String(region) => format!("String@{}", region),
        Ty::Fun { param, ret } => format!("{} -> {}", format_type(param), format_type(ret)),
        Ty::Prod { left, right } => format!("({}, {})", format_type(left), format_type(right)),
        Ty::Sum { left, right } => format!("{} + {}", format_type(left), format_type(right)),
        Ty::Borrow(inner) => format!("&{}", format_type(inner)),
        Ty::List(elem_ty) => format!("[{}]", format_type(elem_ty)),
        Ty::Tuple(elem_types) => {
            let types_str = elem_types
                .iter()
                .map(|t| format_type(t))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", types_str)
        }
        Ty::Region { name, inner } => format!("region {} . {}", name, format_type(inner)),
        Ty::Ref { inner, .. } => format!("Ref({})", format_type(inner)),
        Ty::Var(v) => v.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_expr() {
        let mut repl = Repl::new().unwrap();
        let result = repl.eval_expr("42").unwrap();
        assert!(matches!(result, Value::I32(42)));
    }

    #[test]
    fn test_eval_let() {
        let mut repl = Repl::new().unwrap();
        let result = repl.eval_expr("let x = 1 in x").unwrap();
        assert!(matches!(result, Value::I32(1)));
    }

    #[test]
    fn test_eval_if() {
        let mut repl = Repl::new().unwrap();
        let result = repl.eval_expr("if true then 42 else 0").unwrap();
        assert!(matches!(result, Value::I32(42)));
    }
}
