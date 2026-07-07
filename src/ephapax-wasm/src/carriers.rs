// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! In-tree codecs for the `typedwasm.regions` and
//! `typedwasm.access-sites` wasm custom sections (typed-wasm proposals
//! 0001 + 0002, both `[accepted]` and promoted to ADR-0002 / ADR-0003).
//!
//! Like `ownership.rs`, this module deliberately does NOT depend on
//! `typed-wasm-verify`: the producer and the verifier implement the
//! shared wire contract independently, and the seam-conformance tests
//! keep them honest.
//!
//! ## The ephapax v1 schema
//!
//! Ephapax's only region-allocated runtime values are strings, laid out
//! as an 8-byte header: `ptr: u32` at +0 (address of the byte buffer)
//! and `len: u32` at +4. The v1 `typedwasm.regions` table therefore
//! declares a single region:
//!
//! ```text
//! region 0 "ephapax.string" { field 0 "ptr": U32, field 1 "len": U32 }
//! ```
//!
//! Both fields are wire-kind Scalar (the byte buffer the `ptr` value
//! addresses is bump-allocated and not itself a declared region, so the
//! pointer kinds — which require a valid `target_region` — do not
//! apply). Every string-header `i32.load` / `i32.store` the codegen
//! emits is a typed access against one of these two fields; the raw
//! byte-buffer copies (`memory.copy`) and the allocator's own
//! bump-pointer bookkeeping at `mem[0]` / `mem[8]` are NOT typed
//! accesses and are deliberately unlisted (proposal 0002 §"Producer
//! obligations" ¶5).

pub const REGIONS_SECTION_NAME: &str = "typedwasm.regions";
pub const ACCESS_SITES_SECTION_NAME: &str = "typedwasm.access-sites";

pub const REGIONS_VERSION: u16 = 1;
pub const ACCESS_SITES_VERSION: u16 = 1;

/// Region index of `ephapax.string` in the v1 table.
pub const REGION_STRING: u32 = 0;
/// Field indices within `ephapax.string`.
pub const FIELD_PTR: u32 = 0;
pub const FIELD_LEN: u32 = 1;

/// Wire codepoints from proposal 0001 (kind / wasm_ty tables).
const KIND_SCALAR: u8 = 0;
const WASM_TY_U32: u8 = 2;
const NO_TARGET_REGION: u32 = 0xFFFF_FFFF;
const NON_NULL: u8 = 0;

/// One `typedwasm.access-sites` entry: the producer's assertion that
/// the instruction at `byte_offset` within function `func_idx`'s body
/// is a typed access against `(region_id, field_id)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AccessSite {
    /// Index in the module's function index space (imports included —
    /// the same space `call` immediates and `typedwasm.ownership`
    /// entries use).
    pub func_idx: u32,
    /// Byte offset of the access opcode's first byte within the
    /// function body (counting from the byte after the body's size
    /// prefix, i.e. the start of the locals vector).
    pub byte_offset: u32,
    pub region_id: u32,
    pub field_id: u32,
}

fn write_leb128_u32(out: &mut Vec<u8>, mut v: u32) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn read_leb128_u32(bytes: &[u8], pos: &mut usize) -> Option<u32> {
    let mut result: u32 = 0;
    let mut shift = 0u32;
    loop {
        let byte = *bytes.get(*pos)?;
        *pos += 1;
        if shift == 28 && (byte & 0x70) != 0 {
            return None; // overflows u32
        }
        result |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            // Reject overlong encodings (proposal 0002: consumers MUST
            // reject non-shortest forms).
            if byte == 0 && shift != 0 {
                return None;
            }
            return Some(result);
        }
        shift += 7;
        if shift > 28 {
            return None;
        }
    }
}

fn write_str(out: &mut Vec<u8>, s: &str) {
    out.extend_from_slice(&(s.len() as u32).to_le_bytes());
    out.extend_from_slice(s.as_bytes());
}

/// Build the fixed ephapax v1 `typedwasm.regions` payload (proposal
/// 0001 wire format).
pub fn build_regions_section_payload() -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&REGIONS_VERSION.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes()); // region_count
    write_str(&mut out, "ephapax.string");
    out.extend_from_slice(&2u32.to_le_bytes()); // field_count
    for name in ["ptr", "len"] {
        write_str(&mut out, name);
        out.push(KIND_SCALAR);
        out.push(WASM_TY_U32);
        out.extend_from_slice(&NO_TARGET_REGION.to_le_bytes());
        out.push(NON_NULL);
        out.extend_from_slice(&1u32.to_le_bytes()); // cardinality
    }
    out.extend_from_slice(&8u32.to_le_bytes()); // region_byte_size
    out
}

/// Encode entries to the `typedwasm.access-sites` payload (proposal
/// 0002 wire format — encoding B, LEB128 per field).
pub fn build_access_sites_payload(entries: &[AccessSite]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&ACCESS_SITES_VERSION.to_le_bytes());
    write_leb128_u32(&mut out, entries.len() as u32);
    for e in entries {
        write_leb128_u32(&mut out, e.func_idx);
        write_leb128_u32(&mut out, e.byte_offset);
        write_leb128_u32(&mut out, e.region_id);
        write_leb128_u32(&mut out, e.field_id);
    }
    out
}

/// Parse a `typedwasm.access-sites` payload. Returns `None` on a
/// malformed payload (wrong version, truncation, overlong LEB128).
pub fn parse_access_sites_payload(bytes: &[u8]) -> Option<Vec<AccessSite>> {
    if bytes.len() < 2 {
        return None;
    }
    let version = u16::from_le_bytes([bytes[0], bytes[1]]);
    if version != ACCESS_SITES_VERSION {
        return None;
    }
    let mut pos = 2usize;
    let count = read_leb128_u32(bytes, &mut pos)?;
    let mut entries = Vec::with_capacity(count as usize);
    for _ in 0..count {
        entries.push(AccessSite {
            func_idx: read_leb128_u32(bytes, &mut pos)?,
            byte_offset: read_leb128_u32(bytes, &mut pos)?,
            region_id: read_leb128_u32(bytes, &mut pos)?,
            field_id: read_leb128_u32(bytes, &mut pos)?,
        });
    }
    if pos != bytes.len() {
        return None; // trailing garbage
    }
    Some(entries)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn access_sites_round_trip() {
        let entries = vec![
            AccessSite { func_idx: 3, byte_offset: 12, region_id: 0, field_id: 0 },
            AccessSite { func_idx: 3, byte_offset: 19, region_id: 0, field_id: 1 },
            AccessSite { func_idx: 300, byte_offset: 70_000, region_id: 0, field_id: 1 },
        ];
        let payload = build_access_sites_payload(&entries);
        assert_eq!(parse_access_sites_payload(&payload), Some(entries));
    }

    #[test]
    fn access_sites_empty_round_trip() {
        let payload = build_access_sites_payload(&[]);
        assert_eq!(payload, vec![1, 0, 0]); // version u16le + count 0
        assert_eq!(parse_access_sites_payload(&payload), Some(vec![]));
    }

    #[test]
    fn rejects_wrong_version_and_truncation() {
        let mut payload = build_access_sites_payload(&[AccessSite {
            func_idx: 1,
            byte_offset: 2,
            region_id: 0,
            field_id: 1,
        }]);
        assert!(parse_access_sites_payload(&payload[..payload.len() - 1]).is_none());
        payload[0] = 9;
        assert!(parse_access_sites_payload(&payload).is_none());
    }

    #[test]
    fn rejects_overlong_leb128() {
        // count = 0 encoded overlong as [0x80, 0x00]
        let payload = vec![1, 0, 0x80, 0x00];
        assert!(parse_access_sites_payload(&payload).is_none());
    }

    #[test]
    fn regions_payload_shape() {
        let p = build_regions_section_payload();
        assert_eq!(&p[0..2], &1u16.to_le_bytes()); // version
        assert_eq!(&p[2..6], &1u32.to_le_bytes()); // one region
        assert_eq!(&p[6..10], &14u32.to_le_bytes()); // name len
        assert_eq!(&p[10..24], b"ephapax.string");
        assert_eq!(&p[24..28], &2u32.to_le_bytes()); // two fields
        // trailing region_byte_size == 8
        assert_eq!(&p[p.len() - 4..], &8u32.to_le_bytes());
    }
}
