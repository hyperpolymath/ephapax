// SPDX-License-Identifier: PMPL-1.0-or-later
//
// Phase B regressions for hyperpolymath/ephapax#43. These tests prove
// that an `extern "abi" { fn name(..): R }` block doesn't just parse
// (Phase A — see ephapax-parser/tests/v2_grammar.rs) but also desugars
// to a core `Decl::Extern` and registers the name in the typechecker
// env, so a callsite for the extern fn type-checks successfully.

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::type_check_module;

const EXTERN_CALLSITE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/extern-callsite.eph"
));

#[test]
fn extern_callsite_typechecks() {
    let surface = parse_surface_module(EXTERN_CALLSITE, "extern-callsite")
        .expect("extern-callsite.eph must parse");
    let module = desugar(&surface).expect("desugar must succeed");

    // Sanity: the extern fn lowered to a Decl::Extern; the user fn `entry`
    // lowered to a Decl::Fn. Both share the core module's decl list.
    let mut extern_count = 0;
    let mut fn_count = 0;
    for d in &module.decls {
        match d {
            ephapax_syntax::Decl::Extern { name, abi, .. } => {
                assert_eq!(abi.as_str(), "wasm");
                assert_eq!(name.as_str(), "host_identity");
                extern_count += 1;
            }
            ephapax_syntax::Decl::Fn { name, .. } => {
                assert_eq!(name.as_str(), "entry");
                fn_count += 1;
            }
            _ => {}
        }
    }
    assert_eq!(extern_count, 1, "expected exactly one Decl::Extern");
    assert_eq!(fn_count, 1, "expected exactly one Decl::Fn");

    // The whole module must type-check — this is what Phase B unlocks. If
    // the extern signature weren't registered in the env, `host_identity(7)`
    // in `entry`'s body would fail with UnboundVariable.
    type_check_module(&module).expect("module must type-check");
}
