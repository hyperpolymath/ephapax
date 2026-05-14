// SPDX-License-Identifier: PMPL-1.0-or-later
//
// Phase C regressions for hyperpolymath/ephapax#43. These tests prove
// that an `extern "abi" { fn name(..): R }` block doesn't just parse
// + typecheck (Phase A + B) but compiles all the way to a valid wasm
// module: each extern fn emits a `(import "abi" "name" (func type))`
// directive, runtime helpers shift accordingly, and callsites for the
// extern resolve to the import's function index.

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::type_check_module;
use wasmparser::{Parser as WasmParser, Payload};

const EXTERN_CALLSITE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/extern-callsite.eph"
));

fn compile(source: &str, name: &str) -> Vec<u8> {
    let surface = parse_surface_module(source, name).expect("must parse");
    let module = desugar(&surface).expect("must desugar");
    type_check_module(&module).expect("must type-check");
    ephapax_wasm::compile_module(&module).expect("must codegen")
}

#[test]
fn extern_callsite_emits_valid_wasm() {
    let wasm = compile(EXTERN_CALLSITE, "extern-callsite");

    // Validate the bytes are a well-formed wasm module.
    wasmparser::validate(&wasm).expect("wasm must validate");
}

#[test]
fn extern_callsite_emits_import_directive() {
    let wasm = compile(EXTERN_CALLSITE, "extern-callsite");

    // Walk the import section and look for an entry whose module is
    // the extern's ABI ("wasm") and whose name is "host_identity".
    let mut found_extern = false;
    let mut total_imports = 0;
    for payload in WasmParser::new(0).parse_all(&wasm) {
        if let Ok(Payload::ImportSection(reader)) = payload {
            for import in reader {
                let import = import.expect("valid import entry");
                total_imports += 1;
                if import.module == "wasm" && import.name == "host_identity" {
                    found_extern = true;
                }
            }
        }
    }

    assert!(
        found_extern,
        "expected an `(import \"wasm\" \"host_identity\" (func ...))` directive in the wasm module"
    );
    // Sanity: should be exactly 3 — the 2 host imports (print_i32, print_string)
    // plus the 1 user-declared extern.
    assert_eq!(
        total_imports, 3,
        "expected 3 import entries (2 host + 1 user extern), got {}",
        total_imports
    );
}
