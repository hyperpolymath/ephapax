#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# install-idris2.sh — provision Idris2 for the Ephapax ABI + formal proofs
# (src/abi/ephapax-abi.ipkg, src/formal/ephapax-formal.ipkg).
#
# Follows the `iseriser/scripts/install-zig.sh` doctrine:
#   * curl + tar over HTTPS — NEVER `git clone`. The agent/CI proxy
#     scopes the GIT protocol to one repo (so `git clone idris-lang/Idris2`
#     → 403), but allowlists HTTPS to github.com / codeload.github.com.
#     A source *tarball* from codeload is a normal HTTPS GET → 200.
#   * pinned version (IDRIS2_VERSION), idempotent (early-exit if present),
#   * fail-soft: a missing Idris2 must NOT block setup or session start
#     (exit 0 on any fetch/build failure, with a diagnostic).
#
# Egress note: codeload.github.com is allowlisted by default. If your
# environment's proxy is stricter, add `codeload.github.com` to the
# HTTPS egress allowlist (same way ziglang.org is added for zig).

set -uo pipefail

IDRIS2_VERSION="${IDRIS2_VERSION:-0.8.0}"
PREFIX="${PREFIX:-$HOME/.idris2}"
SCHEME="${SCHEME:-chezscheme}"

note() { printf '[install-idris2] %s\n' "$*" >&2; }

# Idempotent: already the pinned version? Check both PATH *and* the install
# location ($PREFIX/bin/idris2). The latter matters because callers may run
# this before adding $PREFIX/bin to PATH, and we must NOT trigger a ~15-min
# rebuild when idris2 is already installed.
existing="$(command -v idris2 2>/dev/null || true)"
[ -z "$existing" ] && [ -x "$PREFIX/bin/idris2" ] && existing="$PREFIX/bin/idris2"
if [ -n "$existing" ]; then
  have="$("$existing" --version 2>/dev/null | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)"
  if [ "$have" = "$IDRIS2_VERSION" ]; then
    note "idris2 $IDRIS2_VERSION already installed ($existing) — skipping."
    exit 0
  fi
fi

# Backend + C deps from apt (no cross-repo network). These are the two
# that bit us the first time: chezscheme (the codegen backend) and
# libgmp-dev (gmp.h, needed by the refc support lib at `make install`).
if command -v apt-get >/dev/null 2>&1; then
  sudo apt-get update -qq || note "apt update failed (continuing)"
  sudo apt-get install -y --no-install-recommends \
    "$SCHEME" libgmp-dev make gcc curl || note "apt install of backend deps failed"
fi
if ! command -v "$SCHEME" >/dev/null 2>&1; then
  note "Chez Scheme ($SCHEME) unavailable — cannot build Idris2. Skipping (non-blocking)."
  exit 0
fi

work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
url="https://codeload.github.com/idris-lang/Idris2/tar.gz/refs/tags/v${IDRIS2_VERSION}"
note "fetching Idris2 ${IDRIS2_VERSION} source via HTTPS (curl, not git): $url"
if ! curl -fsSL -o "$work/idris2.tar.gz" "$url"; then
  note "download failed (proxy/egress?). Skipping — session start not blocked."
  exit 0
fi
tar -xzf "$work/idris2.tar.gz" -C "$work" || { note "extract failed — skipping."; exit 0; }
src="$work/Idris2-${IDRIS2_VERSION}"

note "bootstrapping (SCHEME=$SCHEME, PREFIX=$PREFIX) …"
if make -C "$src" bootstrap SCHEME="$SCHEME" PREFIX="$PREFIX" \
   && make -C "$src" install PREFIX="$PREFIX"; then
  note "installed → $PREFIX/bin/idris2"
  note "add to PATH:  export PATH=\"$PREFIX/bin:\$PATH\""
  "$PREFIX/bin/idris2" --version >&2 || true
else
  note "build/install failed — skipping (non-blocking). See logs above."
  exit 0
fi
