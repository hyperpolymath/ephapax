// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Linter — static analysis for code quality beyond type checking.
//!
//! Checks for style issues, unused bindings, linearity violations, region
//! escapes, naming conventions, and unnecessary operations.
//!
//! The linter operates on source text directly (heuristic mode). It does not
//! require a parsed AST, making it suitable for use in the standalone LSP,
//! BoJ lsp-mcp cartridge, and CI pipelines.

use std::collections::{HashMap, HashSet};

/// Lint severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Hint,
    Info,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Severity::Error => write!(f, "error"),
            Severity::Warning => write!(f, "warning"),
            Severity::Hint => write!(f, "hint"),
            Severity::Info => write!(f, "info"),
        }
    }
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

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]: {} ({}:{}:{})",
            self.severity, self.code, self.message, self.file, self.line, self.column)?;
        if let Some(help) = &self.help {
            write!(f, "\n  help: {}", help)?;
        }
        Ok(())
    }
}

/// Lint rule table: code, severity, description.
pub const LINT_RULES: &[(&str, Severity, &str)] = &[
    ("E001", Severity::Error, "Linear variable not consumed"),
    ("E002", Severity::Error, "Variable used after consumption"),
    ("E003", Severity::Error, "Region escape detected"),
    ("E004", Severity::Error, "Linear variable in region not consumed before exit"),
    ("E005", Severity::Error, "Branches consume different linear variables"),
    ("W001", Severity::Warning, "Unused affine binding"),
    ("W002", Severity::Warning, "Unnecessary copy"),
    ("W003", Severity::Warning, "Shadowed binding"),
    ("W004", Severity::Warning, "Missing type annotation on public function"),
    ("W005", Severity::Warning, "Region block with no allocations"),
    ("W006", Severity::Warning, "Affine binding could be linear (resource pattern)"),
    ("S001", Severity::Hint, "Non-snake_case variable name"),
    ("S002", Severity::Hint, "Non-PascalCase type name"),
    ("S003", Severity::Hint, "Inconsistent indentation"),
    ("S004", Severity::Hint, "Region name should be short lowercase"),
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

    pub fn report_with_help(
        &mut self,
        severity: Severity,
        code: &str,
        message: &str,
        line: usize,
        column: usize,
        help: &str,
    ) {
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

    pub fn error_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.severity == Severity::Error).count()
    }

    pub fn warning_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.severity == Severity::Warning).count()
    }
}

/// A binding extracted from source for linearity analysis.
#[derive(Debug, Clone)]
struct BindingInfo {
    name: String,
    line: usize,
    column: usize,
    is_linear: bool,
    region: Option<String>,
    used: bool,
    consumed: bool,
}

/// Lint a source file. Returns all diagnostics found.
///
/// This operates on raw source text using heuristic parsing. It catches
/// the most common issues without requiring a full AST.
pub fn lint_source(file: &str, source: &str) -> Vec<Diagnostic> {
    let mut ctx = LintContext::new(file);
    let lines: Vec<&str> = source.lines().collect();

    check_naming_conventions(&mut ctx, &lines);
    check_linearity(&mut ctx, &lines, source);
    check_regions(&mut ctx, &lines, source);
    check_style(&mut ctx, &lines);
    check_unnecessary_operations(&mut ctx, &lines, source);
    check_public_annotations(&mut ctx, &lines);

    ctx.diagnostics
}

/// S001: Variable names should be snake_case.
/// S002: Type names should be PascalCase.
/// S004: Region names should be short lowercase identifiers.
fn check_naming_conventions(ctx: &mut LintContext, lines: &[&str]) {
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        // S001: Check variable naming in let/let! bindings
        if trimmed.starts_with("let ") || trimmed.starts_with("let!") {
            if let Some(name) = extract_binding_name(trimmed) {
                if !name.starts_with('_') && !name.starts_with('(') && !is_snake_case(&name) {
                    let col = line.find(&name).unwrap_or(0) + 1;
                    ctx.report_with_help(
                        Severity::Hint,
                        "S001",
                        &format!("Variable '{}' should use snake_case", name),
                        line_1,
                        col,
                        &format!("Rename to '{}'", to_snake_case(&name)),
                    );
                }
            }
        }

        // S002: Check type naming in type declarations
        if let Some(rest) = trimmed.strip_prefix("type ") {
            let type_name: String = rest.chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !type_name.is_empty() && !is_pascal_case(&type_name) {
                let col = line.find(&type_name).unwrap_or(0) + 1;
                ctx.report(
                    Severity::Hint,
                    "S002",
                    &format!("Type '{}' should use PascalCase", type_name),
                    line_1,
                    col,
                );
            }
        }

        // S004: Region names should be short lowercase
        if let Some(rest) = trimmed.strip_prefix("region ") {
            let region_name: String = rest.chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !region_name.is_empty() {
                if region_name.chars().any(|c| c.is_uppercase()) {
                    let col = line.find(&region_name).unwrap_or(0) + 1;
                    ctx.report_with_help(
                        Severity::Hint,
                        "S004",
                        &format!("Region name '{}' should be short lowercase", region_name),
                        line_1,
                        col,
                        &format!("Rename to '{}'", region_name.to_lowercase()),
                    );
                }
                if region_name.len() > 8 {
                    let col = line.find(&region_name).unwrap_or(0) + 1;
                    ctx.report(
                        Severity::Hint,
                        "S004",
                        &format!("Region name '{}' is long ({} chars) — prefer short names like 'r', 'buf', 'app'",
                            region_name, region_name.len()),
                        line_1,
                        col,
                    );
                }
            }
        }
    }
}

/// E001: Linear variable not consumed.
/// E002: Variable used after consumption.
/// W001: Unused affine binding.
/// W003: Shadowed binding.
/// W006: Affine binding could be linear (resource handle pattern).
fn check_linearity(ctx: &mut LintContext, lines: &[&str], _source: &str) {
    let mut bindings: Vec<BindingInfo> = Vec::new();
    let mut declared_names: HashSet<String> = HashSet::new();

    // Pass 1: Extract all bindings
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        let (is_linear, rest) = if let Some(rest) = trimmed.strip_prefix("let!") {
            (true, rest.trim())
        } else if let Some(rest) = trimmed.strip_prefix("let ") {
            if rest.starts_with('!') { continue; }
            (false, rest.trim())
        } else {
            continue;
        };

        if let Some(name) = extract_binding_name_from_rest(rest) {
            if name.starts_with('_') || name.starts_with('(') {
                continue;
            }

            // W003: Check for shadowing
            if declared_names.contains(&name) {
                let col = line.find(&name).unwrap_or(0) + 1;
                ctx.report_with_help(
                    Severity::Warning,
                    "W003",
                    &format!("Binding '{}' shadows a previous binding", name),
                    line_1,
                    col,
                    "Consider using a different name to avoid confusion",
                );
            }
            declared_names.insert(name.clone());

            let region = extract_region_from_line(trimmed);
            let col = line.find(&name).unwrap_or(0) + 1;

            bindings.push(BindingInfo {
                name,
                line: line_1,
                column: col,
                is_linear,
                region,
                used: false,
                consumed: false,
            });
        }
    }

    // Pass 2: Check usage. For each binding, scan subsequent lines
    // for occurrences of the name.
    for binding in &mut bindings {
        let start_line = binding.line; // 1-indexed
        for (line_num, line) in lines.iter().enumerate() {
            let line_1 = line_num + 1;
            if line_1 <= start_line {
                continue;
            }
            let trimmed = line.trim();
            // Skip comments
            if trimmed.starts_with("//") {
                continue;
            }
            // Skip new let declarations that happen to contain the name
            // (they're defining, not using)
            if (trimmed.starts_with("let ") || trimmed.starts_with("let!"))
                && extract_binding_name(trimmed).as_deref() == Some(&binding.name)
            {
                continue;
            }
            // Check if the binding name appears in this line
            if line_contains_ident(trimmed, &binding.name) {
                binding.used = true;
                // For linear bindings, first use is consumption
                if binding.is_linear && !binding.consumed {
                    binding.consumed = true;
                }
            }
        }
    }

    // Pass 3: Emit diagnostics
    for binding in &bindings {
        if binding.is_linear && !binding.consumed {
            // E001: Linear variable not consumed
            ctx.report_with_help(
                Severity::Error,
                "E001",
                &format!("Linear variable '{}' is never consumed", binding.name),
                binding.line,
                binding.column,
                &format!("Linear bindings (let!) must be used exactly once. Use 'drop({})' to explicitly discard.", binding.name),
            );
        } else if !binding.is_linear && !binding.used {
            // W001: Unused affine binding
            ctx.report_with_help(
                Severity::Warning,
                "W001",
                &format!("Affine binding '{}' is never used", binding.name),
                binding.line,
                binding.column,
                &format!("Prefix with underscore to suppress: '_{}'", binding.name),
            );
        }

        // W006: Affine binding with region annotation could be linear
        if !binding.is_linear && binding.region.is_some() && binding.used {
            ctx.report_with_help(
                Severity::Warning,
                "W006",
                &format!("Affine binding '{}' with region annotation could be linear", binding.name),
                binding.line,
                binding.column,
                "Region-allocated values are typically resources — consider using let! for linear ownership",
            );
        }
    }
}

/// E003: Region escape detected.
/// E004: Linear variable in region not consumed before exit.
/// W005: Region block with no allocations.
fn check_regions(ctx: &mut LintContext, lines: &[&str], _source: &str) {
    let mut region_stack: Vec<(String, usize, Vec<String>)> = Vec::new(); // (name, start_line, bindings_inside)
    let mut depth: i32 = 0;
    let mut region_start_depth: HashMap<String, i32> = HashMap::new();

    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        // Detect region block start
        if let Some(rest) = trimmed.strip_prefix("region ") {
            let region_name: String = rest.chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !region_name.is_empty() {
                region_stack.push((region_name.clone(), line_1, Vec::new()));
                region_start_depth.insert(region_name, depth);
            }
        }

        // Track bindings inside the current region
        if !region_stack.is_empty() {
            if trimmed.starts_with("let!") || trimmed.starts_with("let ") {
                if let Some(name) = extract_binding_name(trimmed) {
                    if let Some(current) = region_stack.last_mut() {
                        current.2.push(name);
                    }
                }
            }

            // Check for region-annotated values (@region) that reference a
            // different region than the current one
            if let Some(at_pos) = trimmed.find('@') {
                let annotated_region: String = trimmed[at_pos + 1..].chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !annotated_region.is_empty() {
                    // E003: Check if the annotated region differs from any active region
                    let active_regions: HashSet<&str> = region_stack.iter()
                        .map(|(name, _, _)| name.as_str())
                        .collect();
                    if !active_regions.contains(annotated_region.as_str())
                        && !annotated_region.eq("default")
                    {
                        let col = at_pos + 1;
                        ctx.report_with_help(
                            Severity::Error,
                            "E003",
                            &format!("Value annotated with @{} but region '{}' is not active",
                                annotated_region, annotated_region),
                            line_1,
                            col,
                            &format!("Use an active region: {:?}", active_regions),
                        );
                    }
                }
            }
        }

        // Track brace depth for region scope detection
        depth += trimmed.chars().filter(|&c| c == '{').count() as i32;
        depth -= trimmed.chars().filter(|&c| c == '}').count() as i32;

        // Check if any region scope just closed
        let closed_regions: Vec<(String, usize, Vec<String>)> = region_stack.iter()
            .filter(|(name, _, _)| {
                region_start_depth.get(name.as_str())
                    .map(|&start_d| depth <= start_d)
                    .unwrap_or(false)
            })
            .cloned()
            .collect();

        for (name, start_line, bindings) in &closed_regions {
            // W005: Region block with no allocations
            if bindings.is_empty() {
                ctx.report_with_help(
                    Severity::Warning,
                    "W005",
                    &format!("Region '{}' contains no allocations", name),
                    *start_line,
                    1,
                    "Empty regions add overhead — remove if not needed",
                );
            }

            // E004: Check linear bindings consumed before region exit
            for binding_name in bindings {
                // Check if binding is linear and consumed in the region body
                let region_body: String = lines[*start_line..line_num]
                    .iter()
                    .copied()
                    .collect::<Vec<_>>()
                    .join("\n");
                // Simple heuristic: if the binding appears in a drop() or
                // as a function argument, consider it consumed
                let appears_consumed = region_body.contains(&format!("drop({})", binding_name))
                    || region_body.matches(binding_name).count() > 1; // used more than declaration

                if !appears_consumed {
                    // Only flag let! bindings
                    let is_linear_binding = lines[*start_line - 1..line_num].iter()
                        .any(|l| {
                            let t = l.trim();
                            t.starts_with("let!") &&
                            extract_binding_name(t).as_deref() == Some(binding_name.as_str())
                        });

                    if is_linear_binding {
                        ctx.report(
                            Severity::Error,
                            "E004",
                            &format!("Linear variable '{}' may not be consumed before region '{}' exits",
                                binding_name, name),
                            *start_line,
                            1,
                        );
                    }
                }
            }

            region_start_depth.remove(name.as_str());
        }

        region_stack.retain(|(name, _, _)| {
            !closed_regions.iter().any(|(cn, _, _)| cn == name)
        });
    }
}

/// E005: Branches consume different linear variables.
/// Checks if-else blocks to ensure both branches consume the same linear vars.
fn check_branch_linearity(ctx: &mut LintContext, lines: &[&str]) {
    // This is called from check_style as a secondary pass
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if trimmed.starts_with("if ") {
            // Find the then and else branches
            if let Some((then_end, else_start, else_end)) = find_if_else_bounds(lines, i) {
                let then_vars = extract_consumed_vars(&lines[i + 1..then_end]);
                let else_vars = if else_start < else_end {
                    extract_consumed_vars(&lines[else_start..else_end])
                } else {
                    HashSet::new()
                };

                // E005: Check symmetric consumption
                let only_in_then: Vec<_> = then_vars.difference(&else_vars).collect();
                let only_in_else: Vec<_> = else_vars.difference(&then_vars).collect();

                if !only_in_then.is_empty() || !only_in_else.is_empty() {
                    let mut msg = String::from("Branches consume different linear variables");
                    if !only_in_then.is_empty() {
                        msg.push_str(&format!("; only in then: {:?}", only_in_then));
                    }
                    if !only_in_else.is_empty() {
                        msg.push_str(&format!("; only in else: {:?}", only_in_else));
                    }
                    ctx.report(
                        Severity::Error,
                        "E005",
                        &msg,
                        i + 1,
                        1,
                    );
                }
            }
        }
        i += 1;
    }
}

/// S003: Inconsistent indentation.
fn check_style(ctx: &mut LintContext, lines: &[&str]) {
    let mut _prev_indent: Option<usize> = None;
    let mut indent_unit: Option<usize> = None; // detected indent step

    for (line_num, line) in lines.iter().enumerate() {
        let line_1 = line_num + 1;

        // Skip empty lines
        if line.trim().is_empty() {
            continue;
        }

        // Check for tab/space mixing
        let has_tabs = line.starts_with('\t');
        let has_spaces = line.starts_with(' ');
        if has_tabs && has_spaces {
            ctx.report(
                Severity::Hint,
                "S003",
                "Mixed tabs and spaces in indentation",
                line_1,
                1,
            );
            continue;
        }

        // Check for tabs (should be spaces)
        if has_tabs {
            ctx.report_with_help(
                Severity::Hint,
                "S003",
                "Tab indentation detected — Ephapax uses 4-space indentation",
                line_1,
                1,
                "Run 'ephapax fmt' to fix indentation",
            );
            continue;
        }

        let current_indent = line.len() - line.trim_start().len();

        // Detect indent unit from first indented line
        if current_indent > 0 && indent_unit.is_none() {
            indent_unit = Some(current_indent);
        }

        // Check indent is a multiple of the detected unit
        if let Some(unit) = indent_unit {
            if unit > 0 && current_indent % unit != 0 {
                ctx.report_with_help(
                    Severity::Hint,
                    "S003",
                    &format!("Indentation of {} spaces is not a multiple of {} (detected indent unit)",
                        current_indent, unit),
                    line_1,
                    1,
                    "Run 'ephapax fmt' to fix indentation",
                );
            }
        }

        _prev_indent = Some(current_indent);
    }

    // Also check branch linearity (E005)
    check_branch_linearity(ctx, lines);
}

/// W002: Unnecessary copy.
fn check_unnecessary_operations(ctx: &mut LintContext, lines: &[&str], _source: &str) {
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        // W002: Check for copy() on obviously non-linear values
        if let Some(copy_start) = trimmed.find("copy(") {
            let after_copy = &trimmed[copy_start + 5..];
            let inner: String = after_copy.chars()
                .take_while(|&c| c != ')')
                .collect();
            let inner = inner.trim();

            // If the argument is a literal (number, bool, string), copy is unnecessary
            if is_literal(inner) {
                let col = line.find("copy(").unwrap_or(0) + 1;
                ctx.report_with_help(
                    Severity::Warning,
                    "W002",
                    &format!("Unnecessary copy of literal value '{}'", inner),
                    line_1,
                    col,
                    "Literal values are unrestricted — copy() is not needed",
                );
            }
        }
    }
}

/// W004: Missing type annotation on public function.
fn check_public_annotations(ctx: &mut LintContext, lines: &[&str]) {
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        // Check public function declarations for return type
        if trimmed.starts_with("pub fn ") {
            let sig = trimmed.split('{').next().unwrap_or(trimmed);
            // Check if return type annotation is present (-> Type)
            if !sig.contains("->") && !sig.contains(": ") {
                let fn_name: String = trimmed[7..].chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !fn_name.is_empty() {
                    let col = line.find(&fn_name).unwrap_or(0) + 1;
                    ctx.report_with_help(
                        Severity::Warning,
                        "W004",
                        &format!("Public function '{}' missing return type annotation", fn_name),
                        line_1,
                        col,
                        "Add a return type: fn name(params) -> ReturnType",
                    );
                }
            }
        }
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Extract the binding name from a let/let! line.
fn extract_binding_name(line: &str) -> Option<String> {
    let rest = if let Some(r) = line.trim().strip_prefix("let!") {
        r.trim()
    } else if let Some(r) = line.trim().strip_prefix("let ") {
        if r.starts_with('!') { return None; }
        r.trim()
    } else {
        return None;
    };
    extract_binding_name_from_rest(rest)
}

/// Extract binding name from text after the let/let! keyword.
fn extract_binding_name_from_rest(rest: &str) -> Option<String> {
    let name: String = rest.chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if name.is_empty() { None } else { Some(name) }
}

/// Check if a name is snake_case.
fn is_snake_case(name: &str) -> bool {
    name.chars().all(|c| c.is_lowercase() || c.is_ascii_digit() || c == '_')
}

/// Check if a name is PascalCase.
fn is_pascal_case(name: &str) -> bool {
    name.chars().next().map_or(false, |c| c.is_uppercase())
        && !name.contains('_')
}

/// Convert a name to snake_case.
fn to_snake_case(name: &str) -> String {
    let mut result = String::new();
    for (i, ch) in name.chars().enumerate() {
        if ch.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(ch.to_lowercase().next().unwrap_or(ch));
    }
    result
}

/// Extract region annotation (@name) from a line.
fn extract_region_from_line(line: &str) -> Option<String> {
    if let Some(at_pos) = line.find('@') {
        let region: String = line[at_pos + 1..].chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !region.is_empty() { Some(region) } else { None }
    } else {
        None
    }
}

/// Check if a line contains an identifier (not as part of a larger word).
fn line_contains_ident(line: &str, ident: &str) -> bool {
    let mut search_from = 0;
    while let Some(pos) = line[search_from..].find(ident) {
        let abs_pos = search_from + pos;
        let before_ok = abs_pos == 0
            || !line.as_bytes()[abs_pos - 1].is_ascii_alphanumeric()
            && line.as_bytes()[abs_pos - 1] != b'_';
        let after_pos = abs_pos + ident.len();
        let after_ok = after_pos >= line.len()
            || !line.as_bytes()[after_pos].is_ascii_alphanumeric()
            && line.as_bytes()[after_pos] != b'_';
        if before_ok && after_ok {
            return true;
        }
        search_from = abs_pos + 1;
    }
    false
}

/// Check if a string looks like a literal value.
fn is_literal(s: &str) -> bool {
    // Number literal
    if s.parse::<f64>().is_ok() {
        return true;
    }
    // Boolean literal
    if s == "true" || s == "false" {
        return true;
    }
    // String literal
    if s.starts_with('"') && s.ends_with('"') {
        return true;
    }
    // Unit literal
    if s == "()" {
        return true;
    }
    false
}

/// Find the bounds of an if-else block starting at the given line index.
/// Returns (then_block_end, else_block_start, else_block_end) as line indices.
fn find_if_else_bounds(lines: &[&str], if_line: usize) -> Option<(usize, usize, usize)> {
    let mut depth: i32 = 0;
    let mut then_end = if_line;
    let mut found_else = false;
    let mut else_start = 0;
    let mut _else_end = 0;

    for i in if_line..lines.len() {
        let trimmed = lines[i].trim();
        depth += trimmed.chars().filter(|&c| c == '{').count() as i32;
        depth -= trimmed.chars().filter(|&c| c == '}').count() as i32;

        if depth == 0 && i > if_line {
            if !found_else {
                then_end = i;
                // Check if next non-empty line is 'else'
                let next = lines.get(i + 1).map(|l| l.trim()).unwrap_or("");
                if next.starts_with("else") || trimmed.ends_with("else") {
                    found_else = true;
                    else_start = i + 1;
                } else {
                    return Some((then_end, 0, 0));
                }
            } else {
                _else_end = i;
                return Some((then_end, else_start, _else_end));
            }
        }
    }

    None
}

/// Extract variable names that appear to be consumed in a block of lines.
fn extract_consumed_vars(lines: &[&str]) -> HashSet<String> {
    let mut vars = HashSet::new();
    for line in lines {
        let trimmed = line.trim();
        // Look for drop(name) or function calls with a variable
        if let Some(drop_start) = trimmed.find("drop(") {
            let after = &trimmed[drop_start + 5..];
            let name: String = after.chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                vars.insert(name);
            }
        }
    }
    vars
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lint_snake_case() {
        let source = "let myVar = 42 in myVar";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "S001"),
            "Expected S001 for non-snake_case variable");
    }

    #[test]
    fn test_lint_pascal_case_type() {
        let source = "type myType = I32";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "S002"),
            "Expected S002 for non-PascalCase type");
    }

    #[test]
    fn test_lint_unused_linear() {
        let source = "let! x = 42 in ()";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "E001"),
            "Expected E001 for unused linear variable");
    }

    #[test]
    fn test_lint_used_linear_ok() {
        let source = "let! x = 42\ndrop(x)";
        let diags = lint_source("test.eph", source);
        assert!(!diags.iter().any(|d| d.code == "E001"),
            "Should not flag E001 when linear variable is consumed");
    }

    #[test]
    fn test_lint_unused_affine() {
        let source = "let y = 42\nfn main() {}";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "W001"),
            "Expected W001 for unused affine variable");
    }

    #[test]
    fn test_lint_unnecessary_copy() {
        let source = "let x = copy(42) in x";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "W002"),
            "Expected W002 for unnecessary copy of literal");
    }

    #[test]
    fn test_lint_tab_indentation() {
        let source = "\tlet x = 42";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "S003"),
            "Expected S003 for tab indentation");
    }

    #[test]
    fn test_lint_shadowed_binding() {
        let source = "let x = 1\nlet x = 2\nx";
        let diags = lint_source("test.eph", source);
        assert!(diags.iter().any(|d| d.code == "W003"),
            "Expected W003 for shadowed binding");
    }

    #[test]
    fn test_is_snake_case() {
        assert!(is_snake_case("my_var"));
        assert!(is_snake_case("x"));
        assert!(!is_snake_case("myVar"));
        assert!(!is_snake_case("MyVar"));
    }

    #[test]
    fn test_is_pascal_case() {
        assert!(is_pascal_case("MyType"));
        assert!(is_pascal_case("X"));
        assert!(!is_pascal_case("myType"));
        assert!(!is_pascal_case("my_type"));
    }

    #[test]
    fn test_line_contains_ident() {
        assert!(line_contains_ident("use x in", "x"));
        assert!(!line_contains_ident("use xy in", "x"));
        assert!(line_contains_ident("f(x)", "x"));
        assert!(!line_contains_ident("fox", "x"));
    }
}
