// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Code Formatter — consistent formatting for .eph files.
//!
//! Formatting rules:
//! - 4-space indentation (no tabs)
//! - Opening brace on same line as declaration
//! - Closing brace on its own line, aligned with declaration
//! - One space around binary operators
//! - No trailing whitespace
//! - Single blank line between top-level declarations
//! - Region annotations (@r) directly attached to the method call (no space)
//! - let! aligned with let (the ! is part of the keyword, not punctuation)
//!
//! Integration:
//! - Used by ephapax-lsp for format-on-save
//! - Can be run standalone via `ephapax fmt <file.eph>`

/// Formatter configuration.
pub struct FormatConfig {
    /// Number of spaces per indent level.
    pub indent_width: usize,
    /// Maximum line width before wrapping.
    pub max_line_width: usize,
    /// Whether to add a trailing newline.
    pub trailing_newline: bool,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            indent_width: 4,
            max_line_width: 100,
            trailing_newline: true,
        }
    }
}

/// Format a source file.
///
/// TODO: This is a stub. Full formatting requires AST integration
/// (parse → pretty-print). For now, it normalises whitespace only.
pub fn format_source(source: &str, config: &FormatConfig) -> String {
    let mut output = String::with_capacity(source.len());
    let mut prev_blank = false;

    for line in source.lines() {
        let trimmed = line.trim_end();

        // Collapse multiple blank lines into one
        if trimmed.is_empty() {
            if !prev_blank {
                output.push('\n');
            }
            prev_blank = true;
            continue;
        }
        prev_blank = false;

        // Normalise indentation: convert tabs to spaces
        let indent_count = line.len() - line.trim_start().len();
        let current_char = line.as_bytes().get(0).copied().unwrap_or(b' ');

        if current_char == b'\t' {
            // Replace tabs with spaces
            let tab_count = line.bytes().take_while(|&b| b == b'\t').count();
            let spaces = " ".repeat(tab_count * config.indent_width);
            output.push_str(&spaces);
            output.push_str(line[tab_count..].trim_end());
        } else {
            // Already space-indented — preserve but trim trailing whitespace
            output.push_str(trimmed);
        }
        output.push('\n');
    }

    // Ensure trailing newline
    if config.trailing_newline && !output.ends_with('\n') {
        output.push('\n');
    }

    // Remove trailing blank lines (keep exactly one newline at end)
    while output.ends_with("\n\n") {
        output.pop();
    }

    output
}

/// Check if a source file is already formatted.
/// Returns true if formatting would produce identical output.
pub fn is_formatted(source: &str, config: &FormatConfig) -> bool {
    format_source(source, config) == source
}
