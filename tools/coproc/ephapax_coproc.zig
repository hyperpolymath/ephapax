// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// libephapax_coproc — the thin shared seam between ephapax and Axiom.jl's
// coprocessor suite.
//
// This is the ONE place ephapax and Axiom meet for coprocessor dispatch. It
// exports a flat C ABI (`eph_coproc_*`, all `i64 (...)-> i64`) that ephapax
// reaches through its ordinary `__ffi(...)` path (see `stdlib/Coproc.eph`),
// and that — in a full build — forwards to Axiom's already-public
// `backend_coprocessor_*` generics via the Julia C-embedding API
// (jl_init / jl_eval_string / jl_call), selecting the Axiom
// CoprocessorBackend struct from the capability tag. It mirrors how Axiom
// itself already links Zig (`Axiom.jl/src/backends/zig_ffi.jl`).
//
// BOUNDARY (locked): this shim copies NO kernel out of Axiom. ephapax holds
// a typed dispatch surface + a linear safety gate; all routing, fallback,
// and benchmarking stay in Axiom.
//
// This file is the STUB build: with no Axiom runtime linked it reports every
// capability as unavailable and returns benign stub statuses, so ephapax's
// `Coproc` surface type-checks and runs (falling through to the host path)
// with no coprocessor present. The `// TODO(axiom)` markers are the exact
// points where the Julia-embedding forwarder is wired in the full build.
//
// Build (stub):
//   zig build-lib -dynamic -O ReleaseSafe tools/coproc/ephapax_coproc.zig \
//       -femit-bin=libephapax_coproc.so
// Use from ephapax:
//   ephapax run myprog.eph -L libephapax_coproc.so

const std = @import("std");

/// Capability tags — MUST match `cap_tag` in `stdlib/Coproc.eph`.
pub const Capability = enum(i64) {
    audio = 0, // Axiom DSPBackend
    crypto = 1, // Axiom CryptoBackend
    maths = 2, // Axiom MathBackend
    physics = 3, // Axiom PPUBackend
    gpu = 4, // Axiom CUDA/Metal/ROCm
    vector = 5, // Axiom VPUBackend
    tensor = 6, // Axiom TPUBackend
    quantum = 7, // Axiom QPUBackend
    io = 8, // Axiom NPUBackend / host
    fpga = 9, // Axiom FPGABackend
};

/// Status codes shared with `stdlib/Coproc.eph` (and, in the full build, the
/// `CoprocResult` round-trip proof in `src/abi/Ephapax/ABI/Foreign.idr`).
pub const STATUS_OK: i64 = 0;
pub const STATUS_UNAVAILABLE: i64 = -1;

/// Is the coprocessor for `cap_tag` reachable? Returns 1 if available, 0 if
/// not. The stub always returns 0 (no Axiom backend linked).
export fn eph_coproc_available(cap_tag: i64) i64 {
    // TODO(axiom): jl_call Axiom._coprocessor_required / backend probe for
    // the CoprocessorBackend selected by `cap_tag`; return 1 when live.
    _ = cap_tag;
    return 0;
}

/// Upload a host buffer to a coprocessor; returns an opaque device-buffer id.
export fn eph_coproc_upload(cap_tag: i64, data_ptr: i64, len: i64) i64 {
    // TODO(axiom): marshal the host buffer to Axiom and reserve a device
    // buffer on the backend selected by `cap_tag`; return its handle.
    _ = cap_tag;
    _ = data_ptr;
    _ = len;
    return 0;
}

/// Dispatch op `op` (two i64 operands) on a device buffer, returning a fresh
/// device-buffer id for the result (consume-and-reborrow).
export fn eph_coproc_dispatch(buf_id: i64, op: i64, arg0: i64, arg1: i64) i64 {
    // TODO(axiom): route (buf_id, op, arg0, arg1) to the matching
    // Axiom.backend_coprocessor_<op> generic; return the result handle.
    //
    // Stub loopback: a no-op "coprocessor" that returns arg0 + arg1. This is
    // a benign placeholder AND the oracle for the end-to-end seam test
    // (`-L libephapax_coproc.so` then dispatch(_, _, 20, 22) == 42), proving
    // ephapax's `__ffi` path reaches THIS shim rather than the built-in
    // `[ffi:stub] -> 0` fallback.
    _ = buf_id;
    _ = op;
    return arg0 + arg1;
}

/// Download a device buffer's contents to the host buffer at `out_ptr`;
/// terminal consumer. Returns a status code (0 = ok).
export fn eph_coproc_download(buf_id: i64, out_ptr: i64) i64 {
    // TODO(axiom): copy the Axiom-side result back to `out_ptr`, free the
    // device buffer, return STATUS_OK.
    _ = buf_id;
    _ = out_ptr;
    return STATUS_OK;
}

/// Free a device buffer without downloading; terminal abort consumer.
/// Returns a status code (0 = ok).
export fn eph_coproc_release(buf_id: i64) i64 {
    // TODO(axiom): free the Axiom-side device buffer for `buf_id`.
    _ = buf_id;
    return STATUS_OK;
}

test "capability tags match the Coproc.eph contract" {
    try std.testing.expectEqual(@as(i64, 0), @intFromEnum(Capability.audio));
    try std.testing.expectEqual(@as(i64, 9), @intFromEnum(Capability.fpga));
}

test "stub reports unavailable and benign statuses" {
    try std.testing.expectEqual(@as(i64, 0), eph_coproc_available(0));
    try std.testing.expectEqual(STATUS_OK, eph_coproc_download(0, 0));
    try std.testing.expectEqual(STATUS_OK, eph_coproc_release(0));
}
