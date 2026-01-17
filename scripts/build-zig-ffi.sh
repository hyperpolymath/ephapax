#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ZIG_DIR="$ROOT_DIR/idris2/ffi/zig"
ZIG_CACHE_DIR="$ROOT_DIR/.zig-cache"
ZIG_GLOBAL_CACHE_DIR="$ROOT_DIR/.zig-cache-global"

mkdir -p "$ZIG_CACHE_DIR" "$ZIG_GLOBAL_CACHE_DIR"
export ZIG_CACHE_DIR
export ZIG_GLOBAL_CACHE_DIR

pushd "$ZIG_DIR" >/dev/null

zig build-lib -OReleaseFast -static -fPIC -lc \
  -femit-bin=libephapax_tokbuf.a \
  tokbuf.zig

popd >/dev/null

echo "Built $ZIG_DIR/libephapax_tokbuf.a"
