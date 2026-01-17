#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input.eph> [iterations] [--sexpr]" >&2
  exit 1
fi

INPUT="$1"
ITERATIONS="${2:-10}"
USE_SEXPR="false"

shift || true
shift || true

while [[ $# -gt 0 ]]; do
  case "$1" in
    --sexpr)
      USE_SEXPR="true"
      shift 1
      ;;
    *)
      echo "Unknown arg: $1" >&2
      exit 1
      ;;
  esac
done

pushd "$ROOT_DIR" >/dev/null
scripts/build-zig-ffi.sh
idris2 --build idris2/ephapax-affine.ipkg

START=$(date +%s%N)
for _ in $(seq 1 "$ITERATIONS"); do
  if [[ "$USE_SEXPR" == "true" ]]; then
    "$ROOT_DIR/idris2/build/exec/ephapax-affine" "$INPUT" --mode affine --out /tmp/bench.sexpr --sexpr --parse-only >/dev/null
  else
    "$ROOT_DIR/idris2/build/exec/ephapax-affine" "$INPUT" --mode affine --out /tmp/bench.sexpr --parse-only >/dev/null
  fi
done
END=$(date +%s%N)

ELAPSED_NS=$((END - START))
ELAPSED_MS=$((ELAPSED_NS / 1000000))
PER_MS=$((ELAPSED_MS / ITERATIONS))

echo "Ran $ITERATIONS iterations in ${ELAPSED_MS}ms (${PER_MS}ms avg)"

popd >/dev/null
