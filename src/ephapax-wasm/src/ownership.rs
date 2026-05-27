// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell
//
//! In-tree codec for the `typedwasm.ownership` wasm custom section.
//!
//! This module is the source-of-truth for ephapax's own emission of
//! ownership annotations. It mirrors `typed_wasm_verify::section` byte-
//! for-byte, but lives here so ephapax can compile + emit a valid wasm
//! module **without** depending on the typed-wasm-verify crate.
//!
//! The split between "ephapax emits, typed-wasm verifies" is the
//! architectural disentangle: ownership is ephapax's own discipline
//! (its core feature is linear types); the typed-wasm crate is an
//! optional post-codegen verifier. Both sides must agree on the wire
//! format — any change here must be coordinated with
//! `hyperpolymath/typed-wasm:crates/typed-wasm-verify/src/section.rs`.
//!
//! Wire format (little-endian, byte-aligned):
//!
//! ```text
//!   u32le  count
//!   for each entry:
//!     u32le  func_idx
//!     u8     n_params
//!     u8[n]  param_kinds  (0=Unrestricted, 1=Linear,
//!                          2=SharedBorrow, 3=ExclBorrow)
//!     u8     ret_kind
//! ```
//!
//! Reading is lenient on truncation (past-EOF bytes read as 0); matches
//! the original OCaml `Tw_verify.parse_ownership_section_payload`
//! behaviour and the Rust port in typed-wasm-verify.

/// Custom-section name carrying ownership annotations. Producer-neutral
/// since the 2026-05-26 rename. Both AffineScript and Ephapax emit and
/// read this name; the typed-wasm verifier crate publishes the same
/// constant value.
pub const OWNERSHIP_SECTION_NAME: &str = "typedwasm.ownership";

/// Per-parameter / per-return ownership classification. u8 wire byte
/// per kind; values 0/1/2/3 as below. Mirrors
/// `typed_wasm_verify::OwnershipKind` exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OwnershipKind {
    Unrestricted = 0,
    Linear = 1,
    SharedBorrow = 2,
    ExclBorrow = 3,
}

impl OwnershipKind {
    /// Decode a wire byte. Any value outside 0..=3 maps to
    /// `Unrestricted` — matches the OCaml `kind_of_byte` fallback and
    /// the typed-wasm-verify port.
    pub fn from_byte(b: u8) -> Self {
        match b {
            1 => OwnershipKind::Linear,
            2 => OwnershipKind::SharedBorrow,
            3 => OwnershipKind::ExclBorrow,
            _ => OwnershipKind::Unrestricted,
        }
    }

    /// Encode to the single-byte wire value.
    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

/// One entry in the ownership section: a function's index plus its
/// ownership-annotated signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipEntry {
    pub func_idx: u32,
    pub param_kinds: Vec<OwnershipKind>,
    pub ret_kind: OwnershipKind,
}

/// Encode entries to the `typedwasm.ownership` custom-section payload.
///
/// # Panics
///
/// Panics if any entry has more than 255 params (the n_params field is
/// a single byte). Real wasm modules don't have functions with that
/// many params (engine limit is far lower).
pub fn build_ownership_section_payload(entries: &[OwnershipEntry]) -> Vec<u8> {
    let count: u32 = entries
        .len()
        .try_into()
        .expect("entry count must fit in u32");
    let mut out = Vec::with_capacity(4 + entries.len() * 8);
    out.extend_from_slice(&count.to_le_bytes());
    for entry in entries {
        out.extend_from_slice(&entry.func_idx.to_le_bytes());
        let n_params: u8 = entry
            .param_kinds
            .len()
            .try_into()
            .expect("param count must fit in u8");
        out.push(n_params);
        for k in &entry.param_kinds {
            out.push(k.to_byte());
        }
        out.push(entry.ret_kind.to_byte());
    }
    out
}

/// Parse a `typedwasm.ownership` payload back into structured entries.
///
/// Lenient on truncation: a truncated payload yields zeros for the
/// missing bytes (interpreted as `Unrestricted` kinds and
/// `func_idx = 0`). A properly-emitted section will never be
/// truncated; this matches typed-wasm-verify byte-for-byte.
pub fn parse_ownership_section_payload(payload: &[u8]) -> Vec<OwnershipEntry> {
    let mut r = LenientReader::new(payload);
    let count = r.read_u32_le();
    (0..count)
        .map(|_| {
            let func_idx = r.read_u32_le();
            let n_params = r.read_u8();
            let param_kinds = (0..n_params)
                .map(|_| OwnershipKind::from_byte(r.read_u8()))
                .collect();
            let ret_kind = OwnershipKind::from_byte(r.read_u8());
            OwnershipEntry {
                func_idx,
                param_kinds,
                ret_kind,
            }
        })
        .collect()
}

struct LenientReader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> LenientReader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    fn read_u32_le(&mut self) -> u32 {
        if self.pos + 4 > self.buf.len() {
            return 0;
        }
        let b = &self.buf[self.pos..self.pos + 4];
        self.pos += 4;
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    fn read_u8(&mut self) -> u8 {
        if self.pos >= self.buf.len() {
            return 0;
        }
        let v = self.buf[self.pos];
        self.pos += 1;
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(func_idx: u32, params: Vec<OwnershipKind>, ret: OwnershipKind) -> OwnershipEntry {
        OwnershipEntry {
            func_idx,
            param_kinds: params,
            ret_kind: ret,
        }
    }

    #[test]
    fn empty_roundtrip() {
        let bytes = build_ownership_section_payload(&[]);
        assert_eq!(bytes, vec![0, 0, 0, 0]);
        assert_eq!(parse_ownership_section_payload(&bytes), vec![]);
    }

    #[test]
    fn single_linear_param_roundtrip() {
        let e = entry(7, vec![OwnershipKind::Linear], OwnershipKind::Unrestricted);
        let bytes = build_ownership_section_payload(&[e.clone()]);
        assert_eq!(parse_ownership_section_payload(&bytes), vec![e]);
    }

    #[test]
    fn mixed_kinds_roundtrip() {
        let e = entry(
            42,
            vec![
                OwnershipKind::Linear,
                OwnershipKind::ExclBorrow,
                OwnershipKind::SharedBorrow,
                OwnershipKind::Unrestricted,
            ],
            OwnershipKind::Linear,
        );
        let bytes = build_ownership_section_payload(&[e.clone()]);
        assert_eq!(parse_ownership_section_payload(&bytes), vec![e]);
    }

    #[test]
    fn truncated_payload_yields_zeros() {
        // count claims 1 entry but we only give 2 bytes — should not panic
        let parsed = parse_ownership_section_payload(&[1, 0, 0, 0]);
        // count=1, then 0 bytes for the entry; reader returns 0s
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].func_idx, 0);
        assert_eq!(parsed[0].param_kinds, vec![]);
        assert_eq!(parsed[0].ret_kind, OwnershipKind::Unrestricted);
    }

    #[test]
    fn unknown_byte_maps_to_unrestricted() {
        // The OCaml/typed-wasm-verify parity quirk.
        assert_eq!(OwnershipKind::from_byte(99), OwnershipKind::Unrestricted);
        assert_eq!(OwnershipKind::from_byte(0), OwnershipKind::Unrestricted);
        assert_eq!(OwnershipKind::from_byte(1), OwnershipKind::Linear);
        assert_eq!(OwnershipKind::from_byte(2), OwnershipKind::SharedBorrow);
        assert_eq!(OwnershipKind::from_byte(3), OwnershipKind::ExclBorrow);
    }
}
