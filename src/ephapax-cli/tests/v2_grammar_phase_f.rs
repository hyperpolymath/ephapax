// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Phase F regressions for hyperpolymath/ephapax#43. Implicit-`in` between
// sequential `let` bindings — the deepest grammar gap bridge.eph relied
// on.
//
// The grammar adds a new `block_expr` form, tried *before* the legacy
// `let_expr` in the `single_expr` choice. A `block_expr` is
// `sequential_let+ ~ expression`, where each `sequential_let` has the
// shape `("let" | "let!") ~ let_binder ~ (":" ~ ty)? ~ "=" ~ block_rhs`
// without a trailing `in` keyword. The parser folds them at parse time:
//
//   let a = 10
//   let b = 20
//   a + b
//
// becomes
//
//   Let { name: a, value: 10, body:
//     Let { name: b, value: 20, body:
//       a + b } }

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::type_check_module;

const IMPLICIT_IN: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/implicit-in.eph"
));

const IMPLICIT_IN_TUPLE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/implicit-in-tuple.eph"
));

fn compile_to_wasm(source: &str, name: &str) -> Vec<u8> {
    let surface = parse_surface_module(source, name).expect("must parse");
    let core = desugar(&surface).expect("must desugar");
    type_check_module(&core).expect("must type-check");
    ephapax_wasm::compile_module(&core).expect("must codegen")
}

#[test]
fn implicit_in_chain_compiles() {
    let wasm = compile_to_wasm(IMPLICIT_IN, "implicit-in");
    wasmparser::validate(&wasm).expect("wasm validates");
}

#[test]
fn implicit_in_with_tuple_binders_compiles() {
    let wasm = compile_to_wasm(IMPLICIT_IN_TUPLE, "implicit-in-tuple");
    wasmparser::validate(&wasm).expect("wasm validates");
}

#[test]
fn legacy_explicit_in_still_compiles() {
    // Regression: don't break the legacy form. The grammar tries
    // `block_expr` first, fails on the `in` keyword after the rhs, rolls
    // back, then `let_expr` matches.
    let source = "module test\n\
                  fn entry(): I32 = let x = 1 in let y = 2 in x\n";
    let wasm = compile_to_wasm(source, "legacy-in");
    wasmparser::validate(&wasm).expect("wasm validates");
}

#[test]
fn implicit_in_let_lin_chain_parses() {
    // `let!` (linear) form bridge.eph uses — `let! (ch2, msg) = ipc_recv(ch)`
    // followed by more lets. We only assert PARSE here; typing the linear
    // form requires extern fns this fixture doesn't have.
    let source = "module test\n\
                  fn use_pair(p: (I32, I32)): I32 =\n\
                    let! (a, b) = p\n\
                    let c = a\n\
                    c\n";
    let _ = parse_surface_module(source, "let-lin-block").expect("must parse");
}
