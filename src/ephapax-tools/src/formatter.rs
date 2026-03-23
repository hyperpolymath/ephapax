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
//! The formatter works on source text directly. It re-indents, normalises
//! whitespace, fixes operator spacing, and enforces blank line conventions.

/// Formatter configuration.
#[derive(Debug, Clone)]
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

/// Format a source file according to Ephapax style conventions.
///
/// Returns the formatted source text.
pub fn format_source(source: &str, config: &FormatConfig) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let mut output = String::with_capacity(source.len());
    let mut indent_level: i32 = 0;
    let mut prev_was_blank = false;
    let mut _prev_was_decl_end = false;

    for (_i, raw_line) in lines.iter().enumerate() {
        let trimmed = raw_line.trim();

        // Handle blank lines: collapse multiples, insert between declarations
        if trimmed.is_empty() {
            if !prev_was_blank && !output.is_empty() {
                output.push('\n');
            }
            prev_was_blank = true;
            continue;
        }

        // Adjust indent level BEFORE writing the line if it starts with a
        // closing brace. This ensures '}' aligns with its opening statement.
        let leading_close_braces = trimmed.chars().take_while(|&c| c == '}').count() as i32;
        if leading_close_braces > 0 {
            indent_level -= leading_close_braces;
            if indent_level < 0 {
                indent_level = 0;
            }
        }

        // Insert a blank line between top-level declarations if not already present
        if indent_level == 0 && is_declaration_start(trimmed) && !output.is_empty() && !prev_was_blank {
            output.push('\n');
        }

        // Format the line content
        let formatted = format_line(trimmed, config);

        // Write indented line
        let indent = " ".repeat(config.indent_width * indent_level.max(0) as usize);
        output.push_str(&indent);
        output.push_str(&formatted);
        output.push('\n');

        // Adjust indent level AFTER writing: count net braces in the line
        let opens = trimmed.chars().filter(|&c| c == '{').count() as i32;
        let closes = trimmed.chars().filter(|&c| c == '}').count() as i32;
        // We already subtracted leading closes, so only count opens and
        // any non-leading closes
        indent_level += opens - (closes - leading_close_braces);
        if indent_level < 0 {
            indent_level = 0;
        }

        prev_was_blank = false;
        _prev_was_decl_end = trimmed.ends_with('}') && indent_level == 0;
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

/// Format a single line (after stripping indentation).
///
/// Applies:
/// - Binary operator spacing
/// - Colon spacing in type annotations
/// - Arrow spacing
/// - Region annotation attachment
/// - Comma spacing
fn format_line(line: &str, _config: &FormatConfig) -> String {
    // Don't format comments or string literals (too risky without a real parser)
    if line.starts_with("//") || line.starts_with("/*") {
        return line.to_string();
    }

    let mut result = String::with_capacity(line.len() + 16);
    let chars: Vec<char> = line.chars().collect();
    let len = chars.len();
    let mut i = 0;
    let mut in_string = false;

    while i < len {
        let ch = chars[i];

        // Track string literals — don't format inside them
        if ch == '"' && (i == 0 || chars[i - 1] != '\\') {
            in_string = !in_string;
            result.push(ch);
            i += 1;
            continue;
        }

        if in_string {
            result.push(ch);
            i += 1;
            continue;
        }

        // Arrow: -> with spaces
        if ch == '-' && i + 1 < len && chars[i + 1] == '>' {
            ensure_space_before(&mut result);
            result.push_str("->");
            i += 2;
            ensure_space_after(&mut result, chars.get(i));
            continue;
        }

        // Double-char operators: ==, !=, <=, >=, &&, ||
        if i + 1 < len {
            let pair = format!("{}{}", ch, chars[i + 1]);
            if matches!(pair.as_str(), "==" | "!=" | "<=" | ">=" | "&&" | "||") {
                ensure_space_before(&mut result);
                result.push_str(&pair);
                i += 2;
                ensure_space_after(&mut result, chars.get(i));
                continue;
            }
        }

        // Single-char binary operators: + - * / % (but not unary minus)
        if matches!(ch, '+' | '*' | '/' | '%') {
            ensure_space_before(&mut result);
            result.push(ch);
            i += 1;
            ensure_space_after(&mut result, chars.get(i));
            continue;
        }

        // Minus: binary if preceded by alnum/)/], unary otherwise
        if ch == '-' && i + 1 < len && chars[i + 1] != '>' {
            let prev_char = if result.is_empty() { ' ' } else {
                result.chars().last().unwrap_or(' ')
            };
            if prev_char.is_alphanumeric() || prev_char == ')' || prev_char == ']' {
                // Binary minus
                ensure_space_before(&mut result);
                result.push('-');
                i += 1;
                ensure_space_after(&mut result, chars.get(i));
                continue;
            }
            // Otherwise unary — no space before
        }

        // Equals: space around = (but not in == which was handled above)
        if ch == '=' && (i + 1 >= len || chars[i + 1] != '=')
            && (i == 0 || chars[i - 1] != '!' && chars[i - 1] != '<' && chars[i - 1] != '>')
        {
            ensure_space_before(&mut result);
            result.push('=');
            i += 1;
            ensure_space_after(&mut result, chars.get(i));
            continue;
        }

        // Colon: space after (for type annotations like x: I32)
        // But not in :: (path separator)
        if ch == ':' {
            if i + 1 < len && chars[i + 1] == ':' {
                // :: path separator — no spaces
                result.push_str("::");
                i += 2;
                continue;
            }
            result.push(':');
            i += 1;
            ensure_space_after(&mut result, chars.get(i));
            continue;
        }

        // Comma: no space before, one space after
        if ch == ',' {
            // Remove trailing space before comma
            while result.ends_with(' ') {
                result.pop();
            }
            result.push(',');
            i += 1;
            // Add space after comma (unless end of line or closing paren)
            if i < len && chars[i] != ')' && chars[i] != ']' && chars[i] != '}' {
                if !chars[i].is_whitespace() {
                    result.push(' ');
                }
            }
            continue;
        }

        // @ region annotation: attach directly (no space before @)
        if ch == '@' {
            // Remove trailing space before @
            while result.ends_with(' ') {
                result.pop();
            }
            result.push('@');
            i += 1;
            continue;
        }

        // Collapse multiple spaces into one
        if ch == ' ' {
            if !result.ends_with(' ') && !result.is_empty() {
                result.push(' ');
            }
            i += 1;
            continue;
        }

        // Everything else: pass through
        result.push(ch);
        i += 1;
    }

    // Trim trailing whitespace
    while result.ends_with(' ') {
        result.pop();
    }

    result
}

/// Ensure there's a space before the current position in the output.
fn ensure_space_before(output: &mut String) {
    if !output.is_empty() && !output.ends_with(' ') && !output.ends_with('(')
        && !output.ends_with('[') && !output.ends_with('{')
    {
        output.push(' ');
    }
}

/// Ensure there's a space after the current operator in the output.
fn ensure_space_after(output: &mut String, next_char: Option<&char>) {
    if let Some(&next) = next_char {
        if !next.is_whitespace() && next != ')' && next != ']' && next != '}'
            && next != ',' && next != ';'
        {
            output.push(' ');
        }
    }
}

/// Check if a line starts a top-level declaration.
fn is_declaration_start(line: &str) -> bool {
    line.starts_with("fn ")
        || line.starts_with("pub fn ")
        || line.starts_with("type ")
        || line.starts_with("effect ")
        || line.starts_with("region ")
        || line.starts_with("import ")
        || line.starts_with("// ---")
}

/// Check if a source file is already formatted.
/// Returns true if formatting would produce identical output.
pub fn is_formatted(source: &str, config: &FormatConfig) -> bool {
    format_source(source, config) == source
}

/// Format a source file in-place, returning whether any changes were made.
pub fn format_file(path: &std::path::Path, config: &FormatConfig) -> Result<bool, String> {
    let source = std::fs::read_to_string(path)
        .map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let formatted = format_source(&source, config);

    if formatted == source {
        return Ok(false);
    }

    std::fs::write(path, &formatted)
        .map_err(|e| format!("Cannot write {}: {}", path.display(), e))?;

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(source: &str) -> String {
        format_source(source, &FormatConfig::default())
    }

    #[test]
    fn test_trailing_whitespace_removed() {
        let result = fmt("let x = 42   \n");
        assert!(!result.contains("   \n"), "Trailing whitespace should be removed");
    }

    #[test]
    fn test_tab_to_spaces() {
        let result = fmt("\tlet x = 42");
        assert!(!result.contains('\t'), "Tabs should be converted to spaces");
        assert!(result.starts_with("let"), "Top-level should have no indent");
    }

    #[test]
    fn test_brace_indentation() {
        let source = "fn main() {\nlet x = 1\n}";
        let result = fmt(source);
        let lines: Vec<&str> = result.lines().collect();
        assert_eq!(lines[0], "fn main() {");
        assert!(lines[1].starts_with("    "), "Body should be indented: '{}'", lines[1]);
        assert_eq!(lines[2], "}");
    }

    #[test]
    fn test_operator_spacing() {
        let result = fmt("let x=1+2");
        assert!(result.contains("x = 1 + 2"), "Operators should have spaces: '{}'", result.trim());
    }

    #[test]
    fn test_arrow_spacing() {
        let result = fmt("fn f(x: I32)->I32 {");
        assert!(result.contains("-> I32"), "Arrow should have spaces: '{}'", result.trim());
    }

    #[test]
    fn test_comma_spacing() {
        let result = fmt("fn f(x: I32,y: I32) {");
        assert!(result.contains(", y"), "Comma should have space after: '{}'", result.trim());
    }

    #[test]
    fn test_blank_line_between_declarations() {
        let source = "fn a() {\n}\nfn b() {\n}";
        let result = fmt(source);
        assert!(result.contains("}\n\nfn b"), "Should have blank line between declarations");
    }

    #[test]
    fn test_collapse_blank_lines() {
        let source = "let x = 1\n\n\n\nlet y = 2";
        let result = fmt(source);
        assert!(!result.contains("\n\n\n"), "Multiple blank lines should collapse");
    }

    #[test]
    fn test_region_annotation_attached() {
        let result = fmt("String.new @r(\"hello\")");
        assert!(result.contains("@r"), "Region annotation should be attached: '{}'", result.trim());
        assert!(!result.contains(" @"), "No space before @: '{}'", result.trim());
    }

    #[test]
    fn test_string_literals_preserved() {
        let result = fmt("let x = \"hello   world\"");
        assert!(result.contains("\"hello   world\""), "String content should not be modified");
    }

    #[test]
    fn test_comments_preserved() {
        let result = fmt("// this is a comment with  extra  spaces");
        assert!(result.contains("extra  spaces"), "Comment content should not be modified");
    }

    #[test]
    fn test_is_formatted_idempotent() {
        let source = "fn main() {\n    let x = 1\n}\n";
        let formatted = fmt(source);
        let config = FormatConfig::default();
        assert!(is_formatted(&formatted, &config), "Formatted output should be idempotent");
    }

    #[test]
    fn test_nested_indentation() {
        let source = "fn main() {\nif true {\nlet x = 1\n}\n}";
        let result = fmt(source);
        let lines: Vec<&str> = result.lines().collect();
        assert!(lines[1].starts_with("    if"), "if should be 4-space indent");
        assert!(lines[2].starts_with("        let"), "nested should be 8-space indent");
        assert!(lines[3].starts_with("    }"), "closing brace should be 4-space indent");
        assert_eq!(lines[4], "}");
    }
}
