#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# install-coq.sh — provision Coq for the Ephapax formal proofs (formal/).
#
# Coq is the one prover that needs no curl+tar dance: Ubuntu 24.04 (noble)
# ships exactly 8.18.0 (`coq 8.18.0+dfsg`), the version pinned by
# formal/Justfile, pixi.toml's [feature.proofs], and .github/workflows/
# coq-build.yml. apt mirrors are not GitHub, so the git-protocol repo scope
# does not apply.
#
# Doctrine (shared with install-zig.sh / install-idris2.sh): idempotent
# (early-exit if the pinned version is present) and fail-soft (never block
# setup or session start — exit 0 on failure with a diagnostic).

set -uo pipefail

COQ_VERSION="${COQ_VERSION:-8.18.0}"
note() { printf '[install-coq] %s\n' "$*" >&2; }

if command -v coqc >/dev/null 2>&1; then
  have="$(coqc --version 2>/dev/null | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)"
  if [ "$have" = "$COQ_VERSION" ]; then
    note "coqc $COQ_VERSION already installed — skipping."
    exit 0
  fi
  note "coqc present but version '$have' != '$COQ_VERSION' — (re)installing via apt."
fi

if ! command -v apt-get >/dev/null 2>&1; then
  note "apt-get unavailable — install Coq $COQ_VERSION another way (opam/nix). Skipping (non-blocking)."
  exit 0
fi

sudo apt-get update -qq || note "apt update failed (continuing)"
if sudo apt-get install -y --no-install-recommends coq; then
  note "installed: $(coqc --version 2>/dev/null | head -1)"
else
  note "apt install of coq failed — skipping (non-blocking)."
  exit 0
fi
