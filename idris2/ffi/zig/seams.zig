// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// seams.zig — integration-contract tests for the ephapax idris2 <-> zig token
// buffer ABI: tokbuf.zig <-> tokbuf.h <-> the %foreign bindings in
// src/Ephapax/Parse/ZigBuffer.idr. Pattern adapted from
// boj-server/ffi/zig/src/seams.zig (the estate trusted-base reference impl).
//
// Each `test "seam: ..."` pins one promise the Idris2 side relies on across the
// C-ABI boundary. A failure here is a genuine ABI/contract defect, not a flaky
// test. In particular, the str_ptr seams EXERCISE the @ptrCast at tokbuf.zig:99
// and assert the NUL-sentinel invariant that the `// SAFETY:` comment there only
// *asserts* — turning asserted-safe into tested-safe (see METHODOLOGY below).
//
// Run:  zig test -lc idris2/ffi/zig/seams.zig
// (-lc is required because tokbuf.zig allocates via std.heap.c_allocator.)
// CI: .github/workflows/ffi-seams.yml (setup-zig 0.15.2).
//
// ── METHODOLOGY ────────────────────────────────────────────────────────────
// Adapted from boj-server/ffi/zig/src/seams.zig + its docs/proof-debt.md
// "axiom + external-validation" discipline (estate trusted-base reference,
// standards#203). `eph_tokbuf_str_ptr` ends in a @ptrCast that ASSERTS (does
// not check) the NUL sentinel; the sentinel holds because the producer
// `copyStr` allocates len+1 and writes a trailing 0. That is a class-(J)-style
// assumption (true by construction, not provable at the cast site). These seams
// are its external validation: a regression in copyStr fails a seam loudly
// instead of becoming UB at an Idris `String` read.
//
// ── FINDING: integer type-width drift across the three contract layers ──────
// The seams pass (tokbuf.zig is internally consistent) but the DECLARED types
// drift:   field      ZigBuffer.idr   tokbuf.h    tokbuf.zig
//          tag        Int (64-bit)    int32_t     u32
//          bool_val   Int (64-bit)    int32_t     u8
//          kind (ret) Int (64-bit)    int32_t     u32
// It functions for the value ranges used (small token kinds, 0/1 booleans)
// because each callee reads the width it declares, but it is not type-clean
// (most sharply bool_val: 1-byte u8 vs declared 4-byte int32_t). Recommended
// follow-up (NOT done here, to keep this test-only): regenerate tokbuf.h from
// the Zig signatures and consider Bits32/Bits8 in ZigBuffer.idr. Left for owner
// triage — an FFI signature edit can shift the binding.
//
// OUT OF SCOPE: the Rust-side from_raw (ephapax-runtime / -vram-cache) and
// ephapax-interp unsafe/as_ptr are a different boundary (Rust FFI / dlopen),
// documented with // SAFETY: comments at their call sites; not exercised here.

const std = @import("std");
const tb = @import("tokbuf.zig");

// ─── @ptrCast / NUL-sentinel invariant (the headline) ──────────────────────

test "seam: str_ptr returns a NUL-terminated copy equal to the pushed string" {
    const buf = tb.eph_tokbuf_new(4);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 7, "hello", 5, 0, 1, 1);
    // eph_tokbuf_str_ptr performs the @ptrCast under test (tokbuf.zig:99).
    const p = tb.eph_tokbuf_str_ptr(buf, 0);
    try std.testing.expectEqualStrings("hello", std.mem.span(p));
    try std.testing.expectEqual(@as(i32, 5), tb.eph_tokbuf_str_len(buf, 0));
}

test "seam: str_ptr is independently NUL-terminated for each of several tokens" {
    const buf = tb.eph_tokbuf_new(0);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 1, "a", 1, 0, 1, 1);
    tb.eph_tokbuf_push(buf, 2, "bb", 2, 0, 1, 2);
    tb.eph_tokbuf_push(buf, 3, "ccc", 3, 0, 1, 3);
    try std.testing.expectEqualStrings("a", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 0)));
    try std.testing.expectEqualStrings("bb", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 1)));
    try std.testing.expectEqualStrings("ccc", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 2)));
}

test "seam: empty string yields the \"\" sentinel, never a dangling cast" {
    const buf = tb.eph_tokbuf_new(2);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 0, "", 0, 0, 1, 1);
    // str_ptr falls through the optional-null branch to the "" literal.
    try std.testing.expectEqualStrings("", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 0)));
    try std.testing.expectEqual(@as(i32, 0), tb.eph_tokbuf_str_len(buf, 0));
}

// ─── marshalling round-trips ───────────────────────────────────────────────

test "seam: tag (u32) round-trips through kind" {
    const buf = tb.eph_tokbuf_new(1);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 0xABCD_1234, "x", 1, 0, 1, 1);
    try std.testing.expectEqual(@as(u32, 0xABCD_1234), tb.eph_tokbuf_kind(buf, 0));
}

test "seam: bool_val round-trips (truthy + falsy)" {
    const buf = tb.eph_tokbuf_new(2);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 0, "t", 1, 1, 1, 1);
    tb.eph_tokbuf_push(buf, 0, "f", 1, 0, 1, 1);
    try std.testing.expectEqual(@as(u8, 1), tb.eph_tokbuf_bool(buf, 0));
    try std.testing.expectEqual(@as(u8, 0), tb.eph_tokbuf_bool(buf, 1));
}

test "seam: line/col round-trip including negatives" {
    const buf = tb.eph_tokbuf_new(1);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 0, "x", 1, 0, -3, 42);
    try std.testing.expectEqual(@as(i32, -3), tb.eph_tokbuf_line(buf, 0));
    try std.testing.expectEqual(@as(i32, 42), tb.eph_tokbuf_col(buf, 0));
}

// ─── i32 <-> usize clamping at the boundary ────────────────────────────────

test "seam: new(cap <= 0) yields a usable empty buffer that grows on push" {
    const buf = tb.eph_tokbuf_new(-5);
    defer tb.eph_tokbuf_free(buf);
    try std.testing.expectEqual(@as(i32, 0), tb.eph_tokbuf_len(buf));
    tb.eph_tokbuf_push(buf, 9, "g", 1, 0, 1, 1);
    try std.testing.expectEqual(@as(i32, 1), tb.eph_tokbuf_len(buf));
    try std.testing.expectEqual(@as(u32, 9), tb.eph_tokbuf_kind(buf, 0));
}

test "seam: negative str_len clamps to 0 and a \"\" sentinel (no over-read)" {
    const buf = tb.eph_tokbuf_new(1);
    defer tb.eph_tokbuf_free(buf);
    tb.eph_tokbuf_push(buf, 0, "ignored", -1, 0, 1, 1);
    try std.testing.expectEqual(@as(i32, 0), tb.eph_tokbuf_str_len(buf, 0));
    try std.testing.expectEqualStrings("", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 0)));
}

// ─── lifecycle / growth ────────────────────────────────────────────────────

test "seam: push beyond initial cap reallocs and preserves every token" {
    const buf = tb.eph_tokbuf_new(2); // cap 2; push 100 to force realloc growth
    defer tb.eph_tokbuf_free(buf);
    var i: i32 = 0;
    while (i < 100) : (i += 1) {
        tb.eph_tokbuf_push(buf, @as(u32, @intCast(i)), "n", 1, 0, i, i);
    }
    try std.testing.expectEqual(@as(i32, 100), tb.eph_tokbuf_len(buf));
    try std.testing.expectEqual(@as(u32, 0), tb.eph_tokbuf_kind(buf, 0));
    try std.testing.expectEqual(@as(u32, 99), tb.eph_tokbuf_kind(buf, 99));
    try std.testing.expectEqual(@as(i32, 99), tb.eph_tokbuf_col(buf, 99));
    try std.testing.expectEqualStrings("n", std.mem.span(tb.eph_tokbuf_str_ptr(buf, 99)));
}

test "seam: repeated new/free cycles leave a clean state (no crash, fresh len)" {
    var c: usize = 0;
    while (c < 3) : (c += 1) {
        const buf = tb.eph_tokbuf_new(1);
        tb.eph_tokbuf_push(buf, 1, "x", 1, 0, 1, 1);
        try std.testing.expectEqual(@as(i32, 1), tb.eph_tokbuf_len(buf));
        tb.eph_tokbuf_free(buf);
    }
}
