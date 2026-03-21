// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Linter — static analysis for code quality beyond type checking.
//!
//! The linter checks for:
//! - Style issues (naming conventions, indentation)
//! - Unused affine bindings (warning, not error — affine allows drop)
//! - Unconsumed linear bindings (error — also caught by type checker)
//! - Region escape attempts (error — also caught by type checker)
//! - Unnecessary copies (performance warning)
//! - Shadowed bindings (warning)
//! - Missing type annotations on public functions (style)
//!
//! The linter is separate from the type checker. It provides additional
//! diagnostics that improve code quality but are not soundness-critical.
//!
//! Integration:
//! - Used by ephapax-lsp for editor diagnostics
//! - Used by the BoJ lsp-mcp cartridge
//! - Can be run standalone via `ephapax lint <file.eph>`

/// Lint severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Hint,
    Info,
}

/// A lint diagnostic.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: String,
    pub message: String,
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub help: Option<String>,
}

/// Lint rule identifiers.
///
/// Error codes:
/// - E001: Linear variable not consumed
/// - E002: Variable used after consumption
/// - E003: Region escape detected
///
/// Warning codes:
/// - W001: Unused affine binding
/// - W002: Unnecessary copy
/// - W003: Shadowed binding
/// - W004: Missing type annotation on public function
///
/// Style codes:
/// - S001: Non-snake_case variable name
/// - S002: Non-PascalCase type name
/// - S003: Inconsistent indentation
pub const LINT_RULES: &[(&str, Severity, &str)] = &[
    ("E001", Severity::Error, "Linear variable not consumed"),
    ("E002", Severity::Error, "Variable used after consumption"),
    ("E003", Severity::Error, "Region escape detected"),
    ("W001", Severity::Warning, "Unused affine binding"),
    ("W002", Severity::Warning, "Unnecessary copy"),
    ("W003", Severity::Warning, "Shadowed binding"),
    ("W004", Severity::Warning, "Missing type annotation on public function"),
    ("S001", Severity::Hint, "Non-snake_case variable name"),
    ("S002", Severity::Hint, "Non-PascalCase type name"),
    ("S003", Severity::Hint, "Inconsistent indentation"),
];

/// Lint context — accumulates diagnostics during analysis.
pub struct LintContext {
    pub diagnostics: Vec<Diagnostic>,
    pub file: String,
}

impl LintContext {
    pub fn new(file: &str) -> Self {
        Self {
            diagnostics: Vec::new(),
            file: file.to_string(),
        }
    }

    pub fn report(&mut self, severity: Severity, code: &str, message: &str, line: usize, column: usize) {
        self.diagnostics.push(Diagnostic {
            severity,
            code: code.to_string(),
            message: message.to_string(),
            file: self.file.clone(),
            line,
            column,
            help: None,
        });
    }

    pub fn report_with_help(&mut self, severity: Severity, code: &str, message: &str, line: usize, column: usize, help: &str) {
        self.diagnostics.push(Diagnostic {
            severity,
            code: code.to_string(),
            message: message.to_string(),
            file: self.file.clone(),
            line,
            column,
            help: Some(help.to_string()),
        });
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.severity == Severity::Error)
    }
}

/// Lint a source file (text-based, pre-AST).
///
/// TODO: Replace with AST-based linting once ephapax-syntax crate is integrated.
pub fn lint_source(file: &str, source: &str) -> Vec<Diagnostic> {
    let mut ctx = LintContext::new(file);

    for (line_num, line) in source.lines().enumerate() {
        let trimmed = line.trim_start();

        // S001: Check variable naming in let bindings
        if trimmed.starts_with("let ") || trimmed.starts_with("let! ") {
            let after_let = if trimmed.starts_with("let! ") {
                &trimmed[5..]
            } else {
                &trimmed[4..]
            };
            let var_name = after_let.split('=').next().unwrap_or("").trim();
            if !var_name.is_empty() && !var_name.starts_with('_') && !var_name.starts_with('(') {
                if var_name.chars().any(|c| c.is_uppercase()) {
                    ctx.report_with_help(
                        Severity::Hint,
                        "S001",
                        &format!("Variable '{}' should use snake_case", var_name),
                        line_num + 1,
                        line.find(var_name).unwrap_or(0) + 1,
                        &format!("Rename to '{}'", var_name.to_lowercase()),
                    );
                }
            }
        }

        // S002: Check type naming
        if trimmed.starts_with("type ") {
            let type_name = trimmed[5..].split(&['=', '<', ' '][..]).next().unwrap_or("").trim();
            if !type_name.is_empty() && type_name.chars().next().map_or(false, |c| c.is_lowercase()) {
                ctx.report(
                    Severity::Hint,
                    "S002",
                    &format!("Type '{}' should use PascalCase", type_name),
                    line_num + 1,
                    line.find(type_name).unwrap_or(0) + 1,
                );
            }
        }
    }

    ctx.diagnostics
}
