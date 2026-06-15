// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Phase E regressions for hyperpolymath/ephapax#43. Bridge.eph
// integration prep — adds the two grammar pieces it depends on:
//
//   1. `@identifier` decorator annotations on top-level decls
//   2. Tuple destructuring in `let` / `let!` binders
//
// Plus the type-side fix that makes `(I32, I32)` resolve to
// `SurfaceTy::Prod` (binary product) instead of `SurfaceTy::Tuple`, so
// value `(1, 2)` and type `(I32, I32)` agree.
//
// What's *not* covered yet (still blocks full bridge.eph compile):
//   - Implicit `in` between sequential let bindings inside a fn body
//   - Abstract extern type registration (Window, IpcChannel)
//   - `Unit` as a type-name alias for `()`

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::type_check_module;

const LET_PAIR: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/let-pair-explicit-in.eph"
));

#[test]
fn annotation_on_fn_decl_parses() {
    let source = "module test\n@tail_recursive\nfn run(): I32 = 0\n";
    let _ = parse_surface_module(source, "annotation-test")
        .expect("@annotation prefix must parse");
}

#[test]
fn multiple_annotations_on_fn_decl_parse() {
    let source = "module test\n@inline @no_mangle\nfn run(): I32 = 0\n";
    let _ = parse_surface_module(source, "multi-annotation-test")
        .expect("multiple @annotations must parse");
}

#[test]
fn let_pair_binder_compiles_end_to_end() {
    let surface = parse_surface_module(LET_PAIR, "let-pair").expect("must parse");
    let core = desugar(&surface).expect("must desugar (1-arm match fast-path)");
    type_check_module(&core).expect("must type-check");
    let wasm = ephapax_wasm::compile_module(&core).expect("must codegen");
    wasmparser::validate(&wasm).expect("wasm validates");
}

#[test]
fn let_pair_lin_binder_parses() {
    // `let!` with tuple binder — exercised by bridge.eph's
    // `let! (ch2, msg_bytes) = ipc_recv(ch) in ...` form. We only assert
    // parse here (the typing depends on host-provided extern fns that
    // bridge.eph imports).
    let source = "module test\n\
                  fn snd_of_pair(p: (I32, I32)): I32 =\n\
                    let! (a, b) = p in\n\
                    b\n";
    let _ = parse_surface_module(source, "let-lin-pair").expect("must parse");
}
