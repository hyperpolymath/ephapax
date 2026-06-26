#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# install-zig.sh — provision Zig for ephapax's coprocessor seam
# (`just build-coproc`, tools/coproc/*.zig; pixi.toml wants zig >= 0.13).
#
# Ported from hyperpolymath/iseriser/scripts/install-zig.sh. The doctrine:
#   * fetch a PINNED prebuilt binary by curl+tar straight from the vendor
#     (ziglang.org) — never a package manager, never git;
#   * idempotent (early-exit if the pinned version is already on PATH);
#   * fail-soft: a missing Zig must NOT block setup or session start.
#
# Egress note: github.com is allowlisted by the agent/CI proxy by default,
# but ziglang.org must be added to the HTTPS egress allowlist explicitly.
# If it is not reachable, this script logs and exits 0 (non-blocking).

set -uo pipefail

ZIG_VERSION="${ZIG_VERSION:-0.14.0}"
PREFIX="${PREFIX:-/usr/local}"
note() { printf '[install-zig] %s\n' "$*" >&2; }

if command -v zig >/dev/null 2>&1 && [ "$(zig version 2>/dev/null)" = "$ZIG_VERSION" ]; then
  note "zig $ZIG_VERSION already installed — skipping."
  exit 0
fi

case "$(uname -m)" in
  x86_64|amd64) zarch=x86_64 ;;
  aarch64|arm64) zarch=aarch64 ;;
  *) note "unsupported arch $(uname -m) — install zig $ZIG_VERSION manually. Skipping."; exit 0 ;;
esac
case "$(uname -s)" in
  Linux)  zos=linux ;;
  Darwin) zos=macos ;;
  *) note "unsupported OS $(uname -s) — install zig $ZIG_VERSION manually. Skipping."; exit 0 ;;
esac

tarball="zig-${zos}-${zarch}-${ZIG_VERSION}.tar.xz"
url="https://ziglang.org/download/${ZIG_VERSION}/${tarball}"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT

note "fetching $url"
if ! curl -fsSL -o "$work/$tarball" "$url"; then
  note "download failed (ziglang.org not allowlisted?). Skipping — session start not blocked."
  exit 0
fi
tar -xJf "$work/$tarball" -C "$work" || { note "extract failed — skipping."; exit 0; }

dest="${PREFIX}/lib/zig-${ZIG_VERSION}"
sudo rm -rf "$dest"
sudo mkdir -p "${PREFIX}/lib" "${PREFIX}/bin"
sudo mv "$work/zig-${zos}-${zarch}-${ZIG_VERSION}" "$dest"
sudo ln -sf "${dest}/zig" "${PREFIX}/bin/zig"
note "installed → ${PREFIX}/bin/zig ($(zig version 2>/dev/null || echo '?'))"
