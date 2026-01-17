#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input.eph|input.sexpr> --mode affine|linear --out <output.wasm> [--sexpr]" >&2
  exit 1
fi

INPUT="$1"
MODE="affine"
OUT=""
USE_SEXPR="false"

shift
while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --out)
      OUT="$2"
      shift 2
      ;;
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

if [[ -z "$OUT" ]]; then
  OUT="${INPUT%.*}.wasm"
fi

pushd "$ROOT_DIR" >/dev/null

scripts/build-proven.sh
scripts/build-zig-ffi.sh
IDRIS2_CG=refc \
  IDRIS2_CFLAGS="-I$ROOT_DIR/idris2/ffi/zig -include tokbuf.h" \
  IDRIS2_LDFLAGS="-L$ROOT_DIR/idris2/ffi/zig" \
  IDRIS2_LDLIBS="-lephapax_tokbuf" \
  IDRIS2_LIBS="$ROOT_DIR/idris2/ffi/shims:/usr/lib64/idris2-0.8.0/support/refc" \
  idris2 --build idris2/ephapax-affine.ipkg

TMP_SEXPR="$(mktemp)"
trap 'rm -f "$TMP_SEXPR"' EXIT

if [[ "$USE_SEXPR" == "true" ]]; then
  "$ROOT_DIR/idris2/build/exec/ephapax-affine" "$INPUT" --mode "$MODE" --out "$TMP_SEXPR" --sexpr
else
  "$ROOT_DIR/idris2/build/exec/ephapax-affine" "$INPUT" --mode "$MODE" --out "$TMP_SEXPR"
fi

cargo run --release -p ephapax-cli -- compile-sexpr "$TMP_SEXPR" -o "$OUT"

popd >/dev/null

echo "Wrote $OUT"
