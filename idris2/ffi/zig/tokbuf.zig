const std = @import("std");

const Tok = struct {
    tag: u32,
    str_ptr: ?[*]u8,
    str_len: u32,
    bool_val: u8,
    line: i32,
    col: i32,
};

const TokBuf = struct {
    items: []Tok,
    len: usize,
    cap: usize,
    allocator: std.mem.Allocator,
};

fn ensureCap(buf: *TokBuf, needed: usize) void {
    if (needed <= buf.cap) return;
    var new_cap = if (buf.cap == 0) @max(needed, 64) else buf.cap * 2;
    if (new_cap < needed) new_cap = needed;
    const new_items = buf.allocator.realloc(buf.items, new_cap) catch @panic("realloc failed");
    buf.items = new_items;
    buf.cap = new_cap;
}

fn copyStr(alloc: std.mem.Allocator, ptr: [*:0]const u8, len: i32) ?[*]u8 {
    if (len <= 0) return null;
    const slice = ptr[0..@as(usize, @intCast(len))];
    const out = alloc.alloc(u8, slice.len + 1) catch @panic("alloc failed");
    std.mem.copyForwards(u8, out[0..slice.len], slice);
    out[slice.len] = 0;
    return out.ptr;
}

export fn eph_tokbuf_new(cap: i32) *TokBuf {
    const alloc = std.heap.c_allocator;
    const cap_usize = if (cap <= 0) 0 else @as(usize, @intCast(cap));
    const items = alloc.alloc(Tok, cap_usize) catch @panic("alloc failed");
    const buf = alloc.create(TokBuf) catch @panic("alloc failed");
    buf.* = TokBuf{ .items = items, .len = 0, .cap = cap_usize, .allocator = alloc };
    return buf;
}

export fn eph_tokbuf_free(buf: *TokBuf) void {
    const alloc = buf.allocator;
    var i: usize = 0;
    while (i < buf.len) : (i += 1) {
        const t = buf.items[i];
        if (t.str_ptr) |p| {
            alloc.free(p[0..t.str_len]);
        }
    }
    if (buf.cap > 0) {
        alloc.free(buf.items);
    }
    alloc.destroy(buf);
}

export fn eph_tokbuf_push(buf: *TokBuf, tag: u32, str_ptr: [*:0]const u8, str_len: i32, bool_val: u8, line: i32, col: i32) void {
    ensureCap(buf, buf.len + 1);
    const s_ptr = copyStr(buf.allocator, str_ptr, str_len);
    buf.items[buf.len] = Tok{
        .tag = tag,
        .str_ptr = s_ptr,
        .str_len = if (str_len <= 0) 0 else @as(u32, @intCast(str_len)),
        .bool_val = bool_val,
        .line = line,
        .col = col,
    };
    buf.len += 1;
}

export fn eph_tokbuf_len(buf: *TokBuf) i32 {
    return @as(i32, @intCast(buf.len));
}

export fn eph_tokbuf_kind(buf: *TokBuf, idx: i32) u32 {
    const i = @as(usize, @intCast(idx));
    return buf.items[i].tag;
}

export fn eph_tokbuf_str_ptr(buf: *TokBuf, idx: i32) [*:0]const u8 {
    const i = @as(usize, @intCast(idx));
    const t = buf.items[i];
    if (t.str_ptr) |p| {
        return @ptrCast(p);
    }
    return "";
}

export fn eph_tokbuf_str_len(buf: *TokBuf, idx: i32) i32 {
    const i = @as(usize, @intCast(idx));
    return @as(i32, @intCast(buf.items[i].str_len));
}

export fn eph_tokbuf_bool(buf: *TokBuf, idx: i32) u8 {
    const i = @as(usize, @intCast(idx));
    return buf.items[i].bool_val;
}

export fn eph_tokbuf_line(buf: *TokBuf, idx: i32) i32 {
    const i = @as(usize, @intCast(idx));
    return buf.items[i].line;
}

export fn eph_tokbuf_col(buf: *TokBuf, idx: i32) i32 {
    const i = @as(usize, @intCast(idx));
    return buf.items[i].col;
}
