// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Documentation Generator — extracts doc comments and generates
//! API documentation in Markdown.
//!
//! Parses `///` doc comments attached to declarations and generates
//! structured documentation showing:
//! - Function signatures with qualifiers (● linear, ○ affine)
//! - Parameter types and region annotations
//! - Module structure
//! - Type definitions

use std::path::Path;

/// A documented item extracted from source.
#[derive(Debug, Clone)]
pub struct DocItem {
    /// Item kind (function, type, effect, region).
    pub kind: DocKind,
    /// Item name.
    pub name: String,
    /// Doc comment lines (without the /// prefix).
    pub doc_lines: Vec<String>,
    /// Full signature line.
    pub signature: String,
    /// Whether the item is public.
    pub is_public: bool,
    /// Source line number (1-indexed).
    pub line: usize,
}

/// Kind of documented item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DocKind {
    Function,
    Type,
    Effect,
    Region,
    Module,
}

impl std::fmt::Display for DocKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DocKind::Function => write!(f, "function"),
            DocKind::Type => write!(f, "type"),
            DocKind::Effect => write!(f, "effect"),
            DocKind::Region => write!(f, "region"),
            DocKind::Module => write!(f, "module"),
        }
    }
}

/// Documentation output configuration.
#[derive(Debug, Clone)]
pub struct DocConfig {
    /// Include private items in documentation.
    pub include_private: bool,
    /// Include source line numbers.
    pub show_line_numbers: bool,
    /// Module name override (default: filename).
    pub module_name: Option<String>,
}

impl Default for DocConfig {
    fn default() -> Self {
        Self {
            include_private: false,
            show_line_numbers: false,
            module_name: None,
        }
    }
}

/// Extract documented items from an Ephapax source file.
pub fn extract_docs(source: &str) -> Vec<DocItem> {
    let lines: Vec<&str> = source.lines().collect();
    let mut items = Vec::new();
    let mut pending_docs: Vec<String> = Vec::new();

    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let line_1 = line_num + 1;

        // Accumulate doc comments
        if let Some(doc) = trimmed.strip_prefix("///") {
            pending_docs.push(doc.trim_start().to_string());
            continue;
        }

        // Check if this line is a declaration that the pending docs attach to
        if !pending_docs.is_empty() || is_documentable(trimmed) {
            if let Some(item) = parse_declaration(trimmed, line_1, &pending_docs) {
                items.push(item);
            }
            pending_docs.clear();
        } else {
            // Non-doc, non-declaration line clears pending docs
            if !trimmed.is_empty() && !trimmed.starts_with("//") {
                pending_docs.clear();
            }
        }
    }

    items
}

/// Generate Markdown documentation from a source file.
pub fn generate_markdown(source: &str, config: &DocConfig) -> String {
    let items = extract_docs(source);
    let module_name = config.module_name.as_deref().unwrap_or("Module");

    let mut md = String::new();

    // Module header
    md.push_str(&format!("# {}\n\n", module_name));

    // Table of contents
    let visible_items: Vec<&DocItem> = items.iter()
        .filter(|item| config.include_private || item.is_public)
        .collect();

    if !visible_items.is_empty() {
        md.push_str("## Contents\n\n");

        // Group by kind
        let functions: Vec<_> = visible_items.iter()
            .filter(|i| i.kind == DocKind::Function)
            .collect();
        let types: Vec<_> = visible_items.iter()
            .filter(|i| i.kind == DocKind::Type)
            .collect();
        let effects: Vec<_> = visible_items.iter()
            .filter(|i| i.kind == DocKind::Effect)
            .collect();

        if !functions.is_empty() {
            md.push_str("### Functions\n\n");
            for item in &functions {
                md.push_str(&format!("- [`{}`](#{})\n", item.name, anchor(&item.name)));
            }
            md.push('\n');
        }

        if !types.is_empty() {
            md.push_str("### Types\n\n");
            for item in &types {
                md.push_str(&format!("- [`{}`](#{})\n", item.name, anchor(&item.name)));
            }
            md.push('\n');
        }

        if !effects.is_empty() {
            md.push_str("### Effects\n\n");
            for item in &effects {
                md.push_str(&format!("- [`{}`](#{})\n", item.name, anchor(&item.name)));
            }
            md.push('\n');
        }

        md.push_str("---\n\n");
    }

    // Item documentation
    for item in &visible_items {
        md.push_str(&format!("## `{}`\n\n", item.name));

        // Signature
        md.push_str(&format!("```ephapax\n{}\n```\n\n", item.signature));

        // Source location
        if config.show_line_numbers {
            md.push_str(&format!("*Defined at line {}*\n\n", item.line));
        }

        // Qualifier badge
        if item.kind == DocKind::Function {
            let has_linear = item.signature.contains("let!") || item.signature.contains("!");
            if has_linear {
                md.push_str("**Qualifier:** ● linear\n\n");
            }
        }

        // Visibility
        if item.is_public {
            md.push_str("**Visibility:** public\n\n");
        }

        // Doc comment body
        if !item.doc_lines.is_empty() {
            for doc_line in &item.doc_lines {
                md.push_str(doc_line);
                md.push('\n');
            }
            md.push('\n');
        }

        md.push_str("---\n\n");
    }

    md
}

/// Generate documentation for a file, writing output to a Markdown file.
pub fn generate_doc_file(
    source_path: &Path,
    output_path: &Path,
    config: &DocConfig,
) -> Result<(), String> {
    let source = std::fs::read_to_string(source_path)
        .map_err(|e| format!("Cannot read {}: {}", source_path.display(), e))?;

    let module_name = config.module_name.clone().unwrap_or_else(|| {
        source_path.file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "Module".to_string())
    });

    let effective_config = DocConfig {
        module_name: Some(module_name),
        ..config.clone()
    };

    let markdown = generate_markdown(&source, &effective_config);

    std::fs::write(output_path, &markdown)
        .map_err(|e| format!("Cannot write {}: {}", output_path.display(), e))?;

    Ok(())
}

// ============================================================================
// Internal helpers
// ============================================================================

/// Check if a line is a documentable declaration.
fn is_documentable(line: &str) -> bool {
    line.starts_with("fn ")
        || line.starts_with("pub fn ")
        || line.starts_with("type ")
        || line.starts_with("pub type ")
        || line.starts_with("effect ")
        || line.starts_with("pub effect ")
        || line.starts_with("region ")
}

/// Parse a declaration line into a DocItem.
fn parse_declaration(line: &str, line_num: usize, docs: &[String]) -> Option<DocItem> {
    let is_public = line.starts_with("pub ");
    let stripped = if is_public { &line[4..] } else { line };

    if let Some(rest) = stripped.strip_prefix("fn ") {
        let name = rest.chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>();
        if name.is_empty() { return None; }
        let sig = line.split('{').next().unwrap_or(line).trim().to_string();
        Some(DocItem {
            kind: DocKind::Function,
            name,
            doc_lines: docs.to_vec(),
            signature: sig,
            is_public,
            line: line_num,
        })
    } else if let Some(rest) = stripped.strip_prefix("type ") {
        let name = rest.chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>();
        if name.is_empty() { return None; }
        let sig = line.split('{').next().unwrap_or(line).trim().to_string();
        Some(DocItem {
            kind: DocKind::Type,
            name,
            doc_lines: docs.to_vec(),
            signature: sig,
            is_public,
            line: line_num,
        })
    } else if let Some(rest) = stripped.strip_prefix("effect ") {
        let name = rest.chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>();
        if name.is_empty() { return None; }
        let sig = line.split('{').next().unwrap_or(line).trim().to_string();
        Some(DocItem {
            kind: DocKind::Effect,
            name,
            doc_lines: docs.to_vec(),
            signature: sig,
            is_public,
            line: line_num,
        })
    } else if let Some(rest) = stripped.strip_prefix("region ") {
        let name = rest.chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>();
        if name.is_empty() { return None; }
        Some(DocItem {
            kind: DocKind::Region,
            name,
            doc_lines: docs.to_vec(),
            signature: line.trim().to_string(),
            is_public: false,
            line: line_num,
        })
    } else {
        None
    }
}

/// Generate a Markdown anchor from a name.
fn anchor(name: &str) -> String {
    name.to_lowercase().replace(' ', "-")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_function_doc() {
        let source = "/// Adds two numbers.\n/// Returns the sum.\npub fn add(x: I32, y: I32) -> I32 {";
        let items = extract_docs(source);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "add");
        assert_eq!(items[0].kind, DocKind::Function);
        assert!(items[0].is_public);
        assert_eq!(items[0].doc_lines.len(), 2);
        assert_eq!(items[0].doc_lines[0], "Adds two numbers.");
    }

    #[test]
    fn test_extract_type_doc() {
        let source = "/// A 2D point.\ntype Point = { x: I32, y: I32 }";
        let items = extract_docs(source);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "Point");
        assert_eq!(items[0].kind, DocKind::Type);
    }

    #[test]
    fn test_extract_effect_doc() {
        let source = "/// Console I/O effect.\neffect Console {";
        let items = extract_docs(source);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "Console");
        assert_eq!(items[0].kind, DocKind::Effect);
    }

    #[test]
    fn test_undocumented_public_function() {
        let source = "pub fn main() {";
        let items = extract_docs(source);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "main");
        assert!(items[0].doc_lines.is_empty());
    }

    #[test]
    fn test_private_function_excluded() {
        let source = "fn helper() {";
        let items = extract_docs(source);
        let config = DocConfig::default(); // include_private = false
        let md = generate_markdown(source, &config);
        assert!(!md.contains("helper"), "Private items should be excluded by default");
    }

    #[test]
    fn test_markdown_generation() {
        let source = "/// Main entry point.\npub fn main() -> () {";
        let config = DocConfig {
            module_name: Some("test".to_string()),
            ..Default::default()
        };
        let md = generate_markdown(source, &config);
        assert!(md.contains("# test"));
        assert!(md.contains("```ephapax"));
        assert!(md.contains("Main entry point."));
    }

    #[test]
    fn test_region_doc() {
        let source = "/// Temporary buffer region.\nregion buf {";
        let items = extract_docs(source);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "buf");
        assert_eq!(items[0].kind, DocKind::Region);
    }
}
