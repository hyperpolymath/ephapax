#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
INPUT="${1:-$ROOT_DIR/examples/hello.eph}"
OUT="${2:-/tmp/ephapax-smoke.wasm}"

"$ROOT_DIR/scripts/build-proven.sh"
"$ROOT_DIR/scripts/compile-affine.sh" "$INPUT" --mode affine --out "$OUT"

if [[ ! -s "$OUT" ]]; then
  echo "Smoke test failed: output wasm not written" >&2
  exit 1
fi

echo "Smoke OK: $OUT"
