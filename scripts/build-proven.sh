#!/usr/bin/env bash
set -euo pipefail

PROVEN_PATH="${PROVEN_PATH:-/var/mnt/eclipse/repos/proven}"

if [[ ! -f "$PROVEN_PATH/proven.ipkg" ]]; then
  echo "proven.ipkg not found at $PROVEN_PATH" >&2
  exit 1
fi

idris2 --install "$PROVEN_PATH/proven.ipkg"
