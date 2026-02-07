# Debug Support in Ephapax

**Status**: ✅ Implemented (Phase 1)

## Overview

Ephapax now supports generating debug information during compilation, enabling better debugging experience for developers. This feature is particularly important for Ephapax's dyadic type system (affine + linear modes), as it allows debuggers to display mode-aware variable information.

## Features Implemented

### 1. Source Map Generation (JSON Format)

- Maps WASM instruction offsets to source file line numbers
- Stores mode information (affine vs linear)
- JSON format for easy parsing by external tools
- Automatically generated with `--debug` flag

**Example output** (`test.wasm.map`):
```json
{
  "file": "test.eph",
  "mode": "linear",
  "mappings": [
    { "wasm_offset": 0, "line": 21, "col": 0 },
    { "wasm_offset": 1, "line": 29, "col": 0 }
  ]
}
```

### 2. Mode Metadata Custom Section

- Custom WASM section: `ephapax.debug.mode`
- Contains JSON metadata about compilation mode
- Includes variable linearity information
- Can be read by mode-aware debuggers

### 3. CLI Support

New flags added to `ephapax compile`:
- `--debug`: Enable debug information generation
- `--mode <linear|affine>`: Specify compilation mode (affects debug output)

**Usage:**
```bash
# Compile with debug info in linear mode
ephapax compile program.eph --debug --mode linear -o program.wasm

# This generates:
# - program.wasm (WASM bytecode with custom debug sections)
# - program.wasm.map (JSON source map)
```

## Architecture

### Code Organization

| Module | Purpose |
|--------|---------|
| `ephapax-wasm/src/debug.rs` | Debug info structures and generation |
| `ephapax-wasm/src/lib.rs` | Integration with codegen (span tracking, section emission) |
| `ephapax-cli/src/main.rs` | CLI flag handling and file output |

### Debug Information Flow

```
Ephapax Source
     ↓
AST (with Spans)
     ↓
Type Checker (mode: linear/affine)
     ↓
WASM Codegen (tracks instruction → span mappings)
     ↓
  ╔══════════════════════════════════╗
  ║  Debug Info Emission             ║
  ║  • Custom section: mode metadata ║
  ║  • Source map: instruction→line  ║
  ╚══════════════════════════════════╝
     ↓
WASM Module + Source Map (JSON)
```

### Span Tracking

During compilation, `compile_expr` records:
- WASM instruction offset (approximated by instruction count)
- Source span (start line, end line) from AST

This mapping enables debuggers to highlight source code as WASM executes.

## Future Enhancements

### Phase 2: DWARF Support (Planned)

**Status**: Started but disabled (gimli 0.31 API complexity)

DWARF generation would enable compatibility with standard debuggers (lldb, gdb). The implementation is partially written but disabled due to gimli API changes.

**TODO:**
- Fix gimli 0.31 API usage in `DwarfBuilder`
- Emit `.debug_info`, `.debug_abbrev`, `.debug_line` sections
- Test with lldb/gdb

### Phase 3: Debug Adapter Protocol (DAP) Server

**Status**: Not started

Create a DAP server (`ephapax-debug` crate) to enable VS Code debugging:

**Features:**
- Mode-aware variable display (affine/linear/both views)
- Breakpoint support (map source lines to WASM offsets)
- Step-through execution
- Variable inspection with linearity annotations

**Components:**
```
ephapax-debug/
├── Cargo.toml         # DAP dependencies
├── src/
│   ├── lib.rs         # DAP adapter implementation
│   ├── mode_view.rs   # Mode-aware variable formatting
│   └── wasm_state.rs  # WASM runtime state tracking
└── .vscode/
    └── launch.json    # VS Code debug configuration
```

### Phase 4: VS Code Extension Integration

Integrate debugger with VS Code extension (task #4):
- Debugger command palette actions
- Mode switcher UI
- Inline variable annotations (shows linearity)
- Breakpoint gutter icons

## Testing

### Unit Tests

```bash
# Test source map generation
cargo test --package ephapax-wasm test_source_map_generation

# Test mode metadata
cargo test --package ephapax-wasm test_mode_metadata_generation
```

### Integration Test

```bash
# Compile with debug
ephapax compile test.eph --debug --mode linear

# Verify outputs
ls test.wasm test.wasm.map

# Check source map content
cat test.wasm.map
```

## Implementation Notes

### Why JSON Source Maps?

1. **Simplicity**: Easy to parse in any language
2. **Debugger-agnostic**: Works with custom tools, not just DWARF-compatible debuggers
3. **Mode metadata**: Can include Ephapax-specific info (linearity, modes)
4. **Incremental deployment**: DWARF can be added later without breaking existing tools

### Span Approximation

Currently, WASM offsets are approximated by instruction count. This is sufficient for line-level debugging but not byte-perfect. Future enhancement: track actual byte offsets during emission.

### Mode-Aware Debugging

The debug system preserves Ephapax's dyadic nature:
- Source maps tagged with mode (linear/affine)
- Variable metadata includes `is_linear` flag
- Future DAP server will display variables differently based on mode

## Related Tasks

- [ ] Task #1: Complete DWARF support (fix gimli API usage)
- [ ] Task #4: VS Code extension (integrate debugger UI)
- [ ] Add end-to-end debugging guide to documentation
- [ ] Create debugging examples showing affine vs linear behavior

## References

- [Debug Adapter Protocol (DAP)](https://microsoft.github.io/debug-adapter-protocol/)
- [DWARF Debugging Format](https://dwarfstd.org/)
- [Source Maps v3 Spec](https://sourcemaps.info/spec.html) (inspiration, not directly used)
- [gimli DWARF library](https://github.com/gimli-rs/gimli)
