#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Self-test for scripts/probe-battery.sh: the wasm-run command must keep
# the compiler's exit status. An ordinary compile error is `no-module`; a
# compile that dies by a signal or times out must not be reported as
# `no-module` (it would then pass as SAME against a no-module baseline).
#
# Uses a stub compiler and a fixture probe directory, so it needs neither
# cargo nor wasmtime. Usage: bash scripts/test-probe-battery.sh
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

mkdir -p "$T/probes"
for p in p_err p_crash p_slow; do echo "fn main() -> I32 { 0 }" >"$T/probes/$p.eph.txt"; done
echo '(module)' >"$T/probes/env.wat"
# Every baseline and target is no-module: only the ordinary error may match.
printf '%s\n' '# fixture' \
  "$(printf 'p_err\twasm-run\tno-module\tno-module\tT')" \
  "$(printf 'p_crash\twasm-run\tno-module\tno-module\tT')" \
  "$(printf 'p_slow\twasm-run\tno-module\tno-module\tT')" >"$T/probes/expectations.tsv"

cat >"$T/stub" <<'STUB'
#!/usr/bin/env bash
case "$2" in
  p_err.eph) echo "Type error: fixture" >&2; exit 1 ;;
  p_crash.eph) echo "fixture abort" >&2; kill -ABRT $$ ;;
  p_slow.eph) exec sleep 10 ;;
esac
exit 1
STUB
chmod +x "$T/stub"

set +e
PROBE_BATTERY_DIR="$T/probes" PROBE_TIMEOUT=2 \
  bash "$ROOT_DIR/scripts/probe-battery.sh" --bin "$T/stub" --out "$T/out.tsv" 2>"$T/err"
code=$?
set -e

pass=0; failn=0
expect_row() { # probe verdict status
  local got
  got="$(awk -F'\t' -v p="$1" '$1 == p { print $4 "/" $5 }' "$T/out.tsv")"
  if [[ "$got" == "$2/$3" ]]; then pass=$((pass + 1)); else failn=$((failn + 1)); echo "FAIL: $1: expected $2/$3, got $got"; fi
}
expect_row p_err no-module SAME
expect_row p_crash crash:134 CHANGED
expect_row p_slow timeout CHANGED
if [[ "$code" -eq 1 ]]; then pass=$((pass + 1)); else failn=$((failn + 1)); echo "FAIL: exit $code, expected 1"; cat "$T/err"; fi

echo "probe-battery self-test: $pass passed, $failn failed"
[[ "$failn" -eq 0 ]]
