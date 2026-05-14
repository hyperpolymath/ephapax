// SPDX-License-Identifier: PMPL-1.0-or-later
//
// Phase G + H regressions for hyperpolymath/ephapax#43:
//
//   G — `extern "abi" { type Foo }` items register as opaque types in the
//       desugar registry; `SurfaceTy::Named { name: "Foo" }` resolves to
//       `Ty::Base(I32)` (host handle representation).
//
//   H — `Unit` and `Bytes` are built-in type-name aliases. `Unit` is the
//       type-position spelling of the literal `()`; `Bytes` resolves to
//       `I32` until a stdlib `Bytes` ADT lands.

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::type_check_module;

const EXTERN_ABSTRACT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/extern-abstract-types.eph"
));

#[test]
fn extern_abstract_types_desugar_to_i32_handles() {
    let surface = parse_surface_module(EXTERN_ABSTRACT, "extern-abstract").expect("must parse");
    let core = desugar(&surface).expect("must desugar");
    type_check_module(&core).expect("must type-check");
    let wasm = ephapax_wasm::compile_module(&core).expect("must codegen");
    wasmparser::validate(&wasm).expect("wasm validates");
}

#[test]
fn unit_alias_resolves_to_base_unit() {
    let source = "module test\n\
                  fn noop(): Unit = ()\n";
    let surface = parse_surface_module(source, "unit-alias").expect("must parse");
    let _ = desugar(&surface).expect("Unit must alias to ()");
}

#[test]
fn bytes_alias_resolves_to_i32() {
    let source = "module test\n\
                  fn id(b: Bytes): Bytes = b\n";
    let surface = parse_surface_module(source, "bytes-alias").expect("must parse");
    let core = desugar(&surface).expect("Bytes must alias to I32");
    type_check_module(&core).expect("must type-check");
}
