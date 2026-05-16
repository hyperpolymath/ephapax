// SPDX-License-Identifier: PMPL-1.0-or-later
//
// Parser regressions for the v2 grammar pieces tracked in #43:
//   - slash-segmented module paths (`module a/b/c`, `import a/b/c`)
//   - `extern "abi" { type T  fn name(..): R }` blocks
//
// These fixtures live alongside the parser crate (rather than in the
// repo-root `tests/v2-grammar/` directory) so `cargo test -p ephapax-parser`
// runs them without extra wiring. The repo-root fixtures directory keeps
// the canonical source-of-truth `.eph` files; we just point at them.

use ephapax_parser::parse_surface_module;
use ephapax_surface::{ExternItem, SurfaceDecl};

const MINIMAL_MODULE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/minimal-module.eph"
));

const MINIMAL_EXTERN: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/v2-grammar/fixtures/minimal-extern.eph"
));

#[test]
fn parses_slash_segmented_module_path() {
    let module = parse_surface_module(MINIMAL_MODULE, "minimal-module")
        .expect("minimal-module.eph must parse");

    // We did not yet wire the module name back through parse_surface_module
    // (it still uses the user-provided `name` argument). The salient check
    // is that the `module hyperpolymath/ephapax/test` line did not trip the
    // grammar — i.e. parse returned Ok.
    assert_eq!(module.decls.len(), 1, "expected exactly one decl (fn answer)");
}

#[test]
fn parses_extern_block_with_type_and_fn_items() {
    let module = parse_surface_module(MINIMAL_EXTERN, "minimal-extern")
        .expect("minimal-extern.eph must parse");

    // Find the Extern decl.
    let externs: Vec<_> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Extern(b) => Some(b),
            _ => None,
        })
        .collect();
    assert_eq!(externs.len(), 1, "expected exactly one extern block");

    let block = externs[0];
    assert_eq!(block.abi.as_str(), "gossamer");
    assert_eq!(block.items.len(), 3, "expected 1 type + 2 fn items");

    // First item: opaque type Window
    match &block.items[0] {
        ExternItem::Type(name) => assert_eq!(name.as_str(), "Window"),
        other => panic!("expected ExternItem::Type, got {:?}", other),
    }

    // Second item: fn window_open(title: String, body: String): Window
    match &block.items[1] {
        ExternItem::Fn { name, params, .. } => {
            assert_eq!(name.as_str(), "window_open");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0.as_str(), "title");
            assert_eq!(params[1].0.as_str(), "body");
        }
        other => panic!("expected ExternItem::Fn, got {:?}", other),
    }

    // Third item: fn window_close(w: Window): ()
    match &block.items[2] {
        ExternItem::Fn { name, params, .. } => {
            assert_eq!(name.as_str(), "window_close");
            assert_eq!(params.len(), 1);
        }
        other => panic!("expected ExternItem::Fn, got {:?}", other),
    }
}
