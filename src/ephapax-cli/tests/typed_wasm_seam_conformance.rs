// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//
// Cross-seam conformance between ephapax and the typed-wasm sibling.
//
// ephapax owns an in-tree mirror of the `typedwasm.ownership`
// custom-section codec (`ephapax_wasm::ownership`) and deliberately does
// NOT depend on typed-wasm-verify in the codegen crate (see the boundary
// note in `src/ephapax-wasm/Cargo.toml`). typed-wasm-verify maintains the
// authoritative codec independently. Every existing test round-trips one
// codec against ITSELF, so the two could silently drift.
//
// This test crosses the real seam: it feeds ephapax-built bytes into
// typed-wasm's decoder (and vice-versa), proving the two independently-
// maintained codecs agree on the wire format, and that the section-name
// constants match so a future rename on either side fails CI rather than
// producing a silently-unread section. It also extracts the section from
// an actual ephapax-emitted module and decodes it with typed-wasm.
//
// Gated on the `typed-wasm-verify` feature (default-on): ephapax-cli is
// the only ephapax crate allowed to see typed-wasm-verify, so this lives
// here, not in ephapax-wasm.

#![cfg(feature = "typed-wasm-verify")]

use ephapax_wasm::ownership as eph;
use std::process::Command;
use typed_wasm_verify as tw;

// --- normalisation: compare entries by their wire bytes, independent of
// --- each crate's enum variant identity.

fn eph_norm(e: &eph::OwnershipEntry) -> (u32, Vec<u8>, u8) {
    (
        e.func_idx,
        e.param_kinds.iter().map(|k| k.to_byte()).collect(),
        e.ret_kind.to_byte(),
    )
}

fn tw_norm(e: &tw::OwnershipEntry) -> (u32, Vec<u8>, u8) {
    (
        e.func_idx,
        e.param_kinds.iter().map(|k| k.to_byte()).collect(),
        e.ret_kind.to_byte(),
    )
}

fn eph_entry(func_idx: u32, params: &[u8], ret: u8) -> eph::OwnershipEntry {
    eph::OwnershipEntry {
        func_idx,
        param_kinds: params
            .iter()
            .map(|&b| eph::OwnershipKind::from_byte(b))
            .collect(),
        ret_kind: eph::OwnershipKind::from_byte(ret),
    }
}

fn tw_entry(func_idx: u32, params: &[u8], ret: u8) -> tw::OwnershipEntry {
    tw::OwnershipEntry {
        func_idx,
        param_kinds: params
            .iter()
            .map(|&b| tw::OwnershipKind::from_byte(b))
            .collect(),
        ret_kind: tw::OwnershipKind::from_byte(ret),
    }
}

/// The section-name constants must be identical, or a rename on one side
/// emits a section the other side never reads. This guard turns the
/// "must be coordinated" comment in `ownership.rs` into a CI invariant.
#[test]
fn section_name_constants_agree() {
    assert_eq!(eph::OWNERSHIP_SECTION_NAME, tw::OWNERSHIP_SECTION_NAME);
    assert_eq!(eph::OWNERSHIP_SECTION_NAME, "typedwasm.ownership");
}

/// ephapax encodes; typed-wasm decodes. The decoded entries must match
/// what ephapax intended, byte-for-byte.
#[test]
fn eph_build_decoded_by_tw_parse() {
    let entries = vec![
        eph_entry(0, &[1], 0),          // (Linear) -> Unrestricted
        eph_entry(7, &[0, 2, 3], 1),    // (Unrestricted, SharedBorrow, ExclBorrow) -> Linear
        eph_entry(42, &[], 0),          // nullary -> Unrestricted
    ];
    let payload = eph::build_ownership_section_payload(&entries);
    let decoded = tw::parse_ownership_section_payload(&payload);

    let want: Vec<_> = entries.iter().map(eph_norm).collect();
    let got: Vec<_> = decoded.iter().map(tw_norm).collect();
    assert_eq!(got, want, "typed-wasm decoded ephapax-built payload differently");
}

/// typed-wasm encodes; ephapax decodes. Symmetric agreement.
#[test]
fn tw_build_decoded_by_eph_parse() {
    let entries = vec![
        tw_entry(1, &[2, 2], 3),
        tw_entry(9, &[1], 1),
        tw_entry(255, &[0], 0),
    ];
    let payload = tw::build_ownership_section_payload(&entries);
    let decoded = eph::parse_ownership_section_payload(&payload);

    let want: Vec<_> = entries.iter().map(tw_norm).collect();
    let got: Vec<_> = decoded.iter().map(eph_norm).collect();
    assert_eq!(got, want, "ephapax decoded typed-wasm-built payload differently");
}

/// Exhaustive cross-codec round-trip over every ownership kind byte and a
/// range of parameter counts, in both directions. This is the dependency-
/// free analogue of the in-crate P59 proptest, but spanning the seam.
#[test]
fn cross_codec_exhaustive_roundtrip() {
    for ret in 0u8..=3 {
        for n_params in 0usize..=5 {
            // Deterministic param pattern covering all kinds.
            let params: Vec<u8> = (0..n_params).map(|i| (i as u8) % 4).collect();
            let func_idx = (n_params as u32) * 100 + ret as u32;

            // eph -> tw -> compare
            let e = eph_entry(func_idx, &params, ret);
            let payload = eph::build_ownership_section_payload(std::slice::from_ref(&e));
            let back = tw::parse_ownership_section_payload(&payload);
            assert_eq!(back.len(), 1);
            assert_eq!(tw_norm(&back[0]), eph_norm(&e), "eph->tw mismatch n={n_params} ret={ret}");

            // tw -> eph -> compare
            let t = tw_entry(func_idx, &params, ret);
            let payload2 = tw::build_ownership_section_payload(std::slice::from_ref(&t));
            let back2 = eph::parse_ownership_section_payload(&payload2);
            assert_eq!(back2.len(), 1);
            assert_eq!(eph_norm(&back2[0]), tw_norm(&t), "tw->eph mismatch n={n_params} ret={ret}");
        }
    }
}

/// Extract the `typedwasm.ownership` section from a REAL ephapax-emitted
/// module and decode it with typed-wasm's parser. `fn echo(s: String)`
/// takes a linear String, so the emitted section pins param_kinds=[Linear].
#[test]
fn real_ephapax_module_section_decoded_by_typed_wasm() {
    let src = tempfile::NamedTempFile::with_suffix(".eph").expect("tempfile");
    std::fs::write(src.path(), "fn echo(s: String): String = s\n").expect("write source");
    let out = tempfile::NamedTempFile::new().expect("output tempfile");

    let status = Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .arg("compile")
        .arg(src.path())
        .arg("-o")
        .arg(out.path())
        .output()
        .expect("ephapax must run");
    assert!(
        status.status.success(),
        "compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&status.stdout),
        String::from_utf8_lossy(&status.stderr)
    );

    let wasm = std::fs::read(out.path()).expect("read emitted wasm");
    let payload = extract_ownership_section(&wasm)
        .expect("emitted module must carry a typedwasm.ownership section for a linear param");

    // Decode ephapax's real output with typed-wasm's independent decoder.
    let entries = tw::parse_ownership_section_payload(&payload);
    assert!(!entries.is_empty(), "decoded ownership section was empty");
    // Some function in the module takes exactly one Linear param (echo's `s`).
    let has_linear_param = entries.iter().any(|e| {
        e.param_kinds
            .iter()
            .any(|k| k.to_byte() == eph::OwnershipKind::Linear.to_byte())
    });
    assert!(
        has_linear_param,
        "typed-wasm decoded no Linear param from ephapax's emitted section: {entries:?}"
    );
}

/// Find the `typedwasm.ownership` custom section in a wasm module.
fn extract_ownership_section(wasm: &[u8]) -> Option<Vec<u8>> {
    use wasmparser::{Parser, Payload};
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(c)) = payload {
            if c.name() == tw::OWNERSHIP_SECTION_NAME {
                return Some(c.data().to_vec());
            }
        }
    }
    None
}
