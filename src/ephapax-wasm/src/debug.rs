// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! DWARF debug information generation for Ephapax WASM modules
//!
//! This module generates DWARF sections (.debug_info, .debug_abbrev, .debug_line)
//! that map WASM bytecode offsets to Ephapax source locations.
//!
//! ## Mode-Aware Debugging
//!
//! Ephapax's dyadic type system (affine + linear modes) requires special
//! metadata to enable mode-aware variable inspection:
//!
//! - Custom section `ephapax.debug.mode` contains JSON metadata
//! - Variable linearity tracked per function scope
//! - Debugger can filter variables by mode (affine/linear/both)

use ephapax_syntax::Span;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

// DWARF support temporarily disabled - gimli 0.31 API requires more complex usage
// Future enhancement: Implement proper DWARF generation for standard debugger support
#[allow(unused_imports)]
use gimli::write::{Address, AttributeValue, DwarfUnit, EndianVec, LineProgram, LineString, Sections};
#[allow(unused_imports)]
use gimli::{Encoding, Format, LineEncoding};

/// Debug information collected during compilation
#[derive(Debug, Clone)]
pub struct DebugInfo {
    /// Source file path
    pub file_path: String,

    /// Compilation mode (affine or linear)
    pub mode: String,

    /// Mapping from WASM instruction offset to source span
    pub instruction_spans: Vec<(u32, Span)>,

    /// Function names indexed by WASM function index
    pub fn_names: HashMap<u32, String>,

    /// Variable metadata for mode-aware debugging
    pub variables: Vec<VariableMetadata>,
}

/// Metadata for a single variable (for mode-aware debugging)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariableMetadata {
    /// Variable name
    pub name: String,

    /// Type name
    pub ty: String,

    /// Is this a linear (use-once) variable?
    pub is_linear: bool,

    /// Function index where this variable is declared
    pub fn_index: u32,

    /// Local variable index within the function
    pub local_index: u32,
}

// DWARF builder temporarily removed - gimli 0.31 API requires significant rework
// This will be added back in a future enhancement with proper API usage
// For now, ephapax uses JSON source maps for debugging

/// Generate source map (JSON format for external debuggers)
pub fn generate_source_map(debug_info: &DebugInfo) -> String {
    #[derive(Serialize)]
    struct SourceMap {
        file: String,
        mode: String,
        mappings: Vec<Mapping>,
    }

    #[derive(Serialize)]
    struct Mapping {
        wasm_offset: u32,
        line: usize,
        col: usize,
    }

    let mappings: Vec<Mapping> = debug_info
        .instruction_spans
        .iter()
        .map(|(offset, span)| Mapping {
            wasm_offset: *offset,
            line: span.start,
            col: 0, // Column tracking not implemented yet
        })
        .collect();

    let source_map = SourceMap {
        file: debug_info.file_path.clone(),
        mode: debug_info.mode.clone(),
        mappings,
    };

    serde_json::to_string_pretty(&source_map).expect("Failed to serialize source map")
}

/// Generate mode metadata custom section (for mode-aware debugging)
pub fn generate_mode_metadata(debug_info: &DebugInfo) -> Vec<u8> {
    #[derive(Serialize)]
    struct ModeMetadata {
        mode: String,
        variables: Vec<VariableMetadata>,
    }

    let metadata = ModeMetadata {
        mode: debug_info.mode.clone(),
        variables: debug_info.variables.clone(),
    };

    serde_json::to_vec(&metadata).expect("Failed to serialize mode metadata")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_map_generation() {
        let debug_info = DebugInfo {
            file_path: "test.eph".to_string(),
            mode: "linear".to_string(),
            instruction_spans: vec![
                (0, Span { start: 1, end: 2 }),
                (10, Span { start: 3, end: 4 }),
            ],
            fn_names: HashMap::new(),
            variables: vec![],
        };

        let source_map = generate_source_map(&debug_info);
        assert!(source_map.contains("test.eph"));
        assert!(source_map.contains("linear"));
        assert!(source_map.contains("wasm_offset"));
    }

    #[test]
    fn test_mode_metadata_generation() {
        let debug_info = DebugInfo {
            file_path: "test.eph".to_string(),
            mode: "affine".to_string(),
            instruction_spans: vec![],
            fn_names: HashMap::new(),
            variables: vec![
                VariableMetadata {
                    name: "x".to_string(),
                    ty: "i32".to_string(),
                    is_linear: true,
                    fn_index: 0,
                    local_index: 0,
                },
            ],
        };

        let metadata = generate_mode_metadata(&debug_info);
        assert!(!metadata.is_empty());

        let decoded: serde_json::Value = serde_json::from_slice(&metadata).unwrap();
        assert_eq!(decoded["mode"], "affine");
        assert_eq!(decoded["variables"][0]["name"], "x");
    }
}
