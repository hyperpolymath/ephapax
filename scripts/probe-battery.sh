#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# probe-battery.sh — experiment X1 of the v2 plan: run the checker/compiler
# probe battery and diff today's verdicts against a checked-in baseline.
#
# Inputs:
#   tests/probes/*.eph.txt, tests/probes/qa/*.eph.txt
#       Probe sources. Stored with a .txt suffix so the repo-wide .eph
#       corpus gate (src/ephapax-cli/tests/eph_corpus_gate.rs) ignores them;
#       this script stages each one as <name>.eph in a temporary directory.
#   conformance/invalid/*.eph
#       Run in place.
#   tests/probes/expectations.tsv
#       One row per (probe, command): the BASELINE verdict (what the tree
#       did when the row was last recorded, known-bad behaviour included)
#       and the plan's TARGET verdict (a bash glob), with the plan rung.
#   tests/probes/env.wat
#       Stub host module (env.print_i32, env.print_string) for wasm-run.
#
# Commands per row:
#   check     ephapax check <probe>.eph
#   compile   ephapax compile <probe>.eph -o <tmp>.wasm
#             (compile always runs wasmparser validation before writing)
#   run       ephapax run <probe>.eph   (compiles, then runs the wasm
#             in-process; since v2 plan rung E4)
#   wasm-run  compile, then `wasmtime run --preload env=env.wat --invoke main`
#             with the wasmtime CLI; verdict `no-module` if compile fails
#             with an ordinary error, `timeout` or `crash:<exit>` if the
#             compile times out or dies by a signal, and
#             `unavailable:no-wasmtime` (status SKIP) if the CLI is absent.
#
# Verdicts: ok | ok:<value> | error:<Kind> | crash:<exit>[-stack-overflow]
#   | timeout | no-module | unavailable:no-wasmtime
# Kinds: InvalidWasm AnnotationNotEnforced CodegenError DesugarError
#   TypeError ParseError RuntimeError UnstableCore Other, and
#   Trap:<message> (wasm-run). UnstableCore: a form that is behind the
#   flag `--unstable-core` (v2 plan rung E9), which the battery does not give.
#
# Output: a TSV on stdout (or --out FILE), one line per row:
#   file  command  exit  verdict  status  baseline  target  diagnostic
# status is SAME (== baseline), IMPROVED (!= baseline, matches target),
# CHANGED (matches neither) or SKIP. A summary goes to stderr.
#
# Exit codes:
#   0  every row SAME or SKIP
#   1  some row CHANGED (a regression, or a move the plan did not predict)
#   2  no CHANGED, but some row IMPROVED: record the new baseline in the
#      same PR (run with --update) so later waves diff against it
#   3  could not run (missing binary, input or expectations)
#
# Usage:
#   scripts/probe-battery.sh [--bin PATH] [--out FILE] [--update]
#     --bin PATH   ephapax binary (default: $EPHAPAX_BIN, else
#                  `cargo build -p ephapax-cli --bin ephapax` and use
#                  target/debug/ephapax)
#     --update     rewrite the baseline column of expectations.tsv with the
#                  observed verdicts (targets are kept); SKIP rows unchanged
#   Environment: PROBE_BATTERY_DIR replaces tests/probes (the self-test
#   scripts/test-probe-battery.sh uses it); PROBE_TIMEOUT is the per-command
#   limit in seconds (default 60).
set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROBES="${PROBE_BATTERY_DIR:-$ROOT_DIR/tests/probes}"
PROBE_TIMEOUT="${PROBE_TIMEOUT:-60}"
EXPECT="$PROBES/expectations.tsv"
ENV_WAT="$PROBES/env.wat"

bin="${EPHAPAX_BIN:-}"
out=""
update=0
while [ $# -gt 0 ]; do
  case "$1" in
    --bin) bin="$2"; shift 2 ;;
    --out) out="$2"; shift 2 ;;
    --update) update=1; shift ;;
    -h|--help) sed -n '2,62p' "$0"; exit 0 ;;
    *) echo "probe-battery: unknown argument $1" >&2; exit 3 ;;
  esac
done

die() { echo "probe-battery: $*" >&2; exit 3; }

[ -f "$EXPECT" ] || die "missing $EXPECT"
# GNU timeout reports expiry as 124. BusyBox reports it as 143, the same
# status as a genuine SIGTERM, so a timeout would read as `crash:143`.
timeout --version 2>/dev/null | grep -q GNU || die "GNU coreutils timeout is required"

# timed CMD...: run under PROBE_TIMEOUT. A command that ignores SIGTERM is
# killed 5 s later; that escalated kill (137 after the deadline) is still a
# timeout, so report it as 124.
timed() {
  local start=$SECONDS rc
  timeout -k 5 "$PROBE_TIMEOUT" "$@"; rc=$?
  if [[ "$rc" -eq 137 && $((SECONDS - start)) -ge "$PROBE_TIMEOUT" ]]; then rc=124; fi
  return "$rc"
}
[ -f "$ENV_WAT" ] || die "missing $ENV_WAT"

if [ -z "$bin" ]; then
  (cd "$ROOT_DIR" && cargo build -q -p ephapax-cli --bin ephapax) \
    || die "cargo build of the ephapax binary failed"
  bin="$ROOT_DIR/target/debug/ephapax"
fi
[ -x "$bin" ] || die "ephapax binary not executable: $bin"
bin="$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")"

wasmtime_bin="$(command -v wasmtime || true)"

stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT

# Stage every probe source as <name>.eph, keeping subdirectories (qa/).
while IFS= read -r -d '' f; do
  rel="${f#"$PROBES"/}"
  mkdir -p "$stage/$(dirname "$rel")"
  cp "$f" "$stage/${rel%.txt}"
done < <(find "$PROBES" -name '*.eph.txt' -print0)

strip_ansi() { sed 's/\x1b\[[0-9;]*m//g'; }

# classify COMMAND EXIT OUTPUT -> verdict
classify() {
  local cmd="$1" code="$2" text="$3"
  if [ "$code" -eq 124 ]; then echo "timeout"; return; fi
  # The wasmtime CLI exits 134 on a wasm trap; that is a trap, not a crash.
  if [ "$cmd" = wasm-run ] && [ "$code" -ne 0 ] && grep -q 'wasm trap' <<<"$text"; then
    echo "error:Trap:$(grep -o 'wasm trap: .*' <<<"$text" | head -n 1 | sed 's/^wasm trap: //; s/[[:space:]]/_/g')"
    return
  fi
  if [ "$code" -ge 128 ]; then
    if grep -q 'overflowed its stack' <<<"$text"; then
      echo "crash:$code-stack-overflow"
    else
      echo "crash:$code"
    fi
    return
  fi
  if [ "$code" -eq 0 ]; then
    case "$cmd" in
      run|wasm-run)
        local last
        last="$(grep -v '^warning: using .--invoke. with a function' <<<"$text" | sed '/^[[:space:]]*$/d' | tail -n 1)"
        echo "ok:$last" ;;
      *) echo "ok" ;;
    esac
    return
  fi
  local kind=Other
  if grep -q 'failed structural validation' <<<"$text"; then kind=InvalidWasm
  elif grep -qi 'annotation not enforced' <<<"$text"; then kind=AnnotationNotEnforced
  elif grep -q 'Codegen error' <<<"$text"; then kind=CodegenError
  elif grep -qi 'desugar error' <<<"$text"; then kind=DesugarError
  elif grep -q 'Type error' <<<"$text"; then kind=TypeError
  elif grep -qi 'parse error' <<<"$text"; then kind=ParseError
  elif grep -q 'Runtime error' <<<"$text"; then kind=RuntimeError
  elif grep -q 'behind the flag `--unstable-core`' <<<"$text"; then kind=UnstableCore
  fi
  echo "error:$kind"
}

# First line that says what went wrong (or, on success, the size line),
# with the staging directory masked. Informational only; never compared.
diagnostic() {
  local text="$1"
  grep -m1 -E 'Error|error|overflowed|Compiled to|checked successfully' <<<"$text" \
    | sed -E -e "s#$stage#<tmp>#g" -e 's/thread .main. \([0-9]+\)/thread main/' -e "s#$ROOT_DIR/##g" -e 's/\t/ /g' \
    | cut -c1-160
}

# source_of PROBE -> path of the .eph to run, and the directory to run in
source_of() {
  case "$1" in
    conformance/*) echo "$ROOT_DIR/$1.eph" ;;
    *) echo "$stage/$1.eph" ;;
  esac
}

run_row() { # PROBE COMMAND -> sets CODE TEXT VERDICT
  local probe="$1" cmd="$2" src dir base wasm
  src="$(source_of "$probe")"
  [[ -f "$src" ]] || die "missing probe source for $probe ($src)"
  dir="$(dirname "$src")"
  base="$(basename "$src")"
  wasm="$stage/out/${probe//\//_}.wasm"
  mkdir -p "$stage/out"
  case "$cmd" in
    check|run)
      TEXT="$(cd "$dir" && timed "$bin" "$cmd" "$base" 2>&1)"
      CODE=$?
      ;;
    compile)
      TEXT="$(cd "$dir" && timed "$bin" compile "$base" -o "$wasm" 2>&1)"
      CODE=$?
      ;;
    wasm-run)
      # Keep the compiler's exit status and output. An ordinary compile
      # error means there is no module to run (`no-module`); a compile
      # that times out or dies by a signal is reported as such (`timeout`,
      # `crash:<exit>`), so it cannot pass as SAME against a no-module row.
      TEXT="$(cd "$dir" && timed "$bin" compile "$base" -o "$wasm" 2>&1)"
      CODE=$?
      if [[ "$CODE" -ne 0 ]]; then
        if [[ "$CODE" -eq 126 || "$CODE" -eq 127 ]]; then
          die "could not execute compile for $probe (exit $CODE): $TEXT"
        fi
        TEXT="$(strip_ansi <<<"$TEXT")"
        if [[ "$CODE" -eq 124 || "$CODE" -ge 128 ]]; then
          VERDICT="$(classify compile "$CODE" "$TEXT")"
        else
          VERDICT="no-module"
        fi
        return
      fi
      if [[ -z "$wasmtime_bin" ]]; then
        CODE=0; TEXT="wasmtime CLI not found"; VERDICT="unavailable:no-wasmtime"; return
      fi
      TEXT="$(timed "$wasmtime_bin" run --preload "env=$ENV_WAT" --invoke main "$wasm" 2>&1)"
      CODE=$?
      ;;
    *) die "unknown command '$cmd' in $EXPECT" ;;
  esac
  # 126/127: the command itself could not be executed; never a verdict.
  if [[ "$CODE" -eq 126 || "$CODE" -eq 127 ]]; then
    die "could not execute $cmd for $probe (exit $CODE): $TEXT"
  fi
  TEXT="$(strip_ansi <<<"$TEXT")"
  VERDICT="$(classify "$cmd" "$CODE" "$TEXT")"
}

tsv="$(mktemp -p "$stage")"
printf 'file\tcommand\texit\tverdict\tstatus\tbaseline\ttarget\tdiagnostic\n' >"$tsv"
n_same=0 n_improved=0 n_changed=0 n_skip=0 rows=0
declare -A observed=()

while IFS=$'\t' read -r probe cmd baseline target ref; do
  case "$probe" in ''|'#'*|probe) continue ;; esac
  rows=$((rows + 1))
  run_row "$probe" "$cmd"
  # The target column is a glob on purpose, so it is unquoted below.
  # shellcheck disable=SC2053
  if [ "$VERDICT" = "unavailable:no-wasmtime" ]; then
    status=SKIP; n_skip=$((n_skip + 1))
  elif [ "$VERDICT" = "$baseline" ]; then
    status=SAME; n_same=$((n_same + 1))
  elif [[ "$VERDICT" == $target ]]; then
    status=IMPROVED; n_improved=$((n_improved + 1))
  else
    status=CHANGED; n_changed=$((n_changed + 1))
  fi
  observed["$probe"$'\t'"$cmd"]="$VERDICT"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$probe" "$cmd" "$CODE" "$VERDICT" "$status" "$baseline" "$target" \
    "$(diagnostic "$TEXT")" >>"$tsv"
done <"$EXPECT"

[ "$rows" -gt 0 ] || die "no rows in $EXPECT"

if [ -n "$out" ]; then cp "$tsv" "$out"; else cat "$tsv"; fi

echo "probe-battery: $rows rows: $n_same SAME, $n_improved IMPROVED, $n_changed CHANGED, $n_skip SKIP" >&2

if [ "$update" -eq 1 ]; then
  new="$(mktemp -p "$stage")"
  while IFS= read -r line; do
    IFS=$'\t' read -r probe cmd baseline target ref <<<"$line"
    key="$probe"$'\t'"$cmd"
    case "$probe" in ''|'#'*|probe) printf '%s\n' "$line" >>"$new"; continue ;; esac
    v="${observed[$key]:-$baseline}"
    [ "$v" = "unavailable:no-wasmtime" ] && v="$baseline"
    printf '%s\t%s\t%s\t%s\t%s\n' "$probe" "$cmd" "$v" "$target" "$ref" >>"$new"
  done <"$EXPECT"
  cp "$new" "$EXPECT"
  echo "probe-battery: baseline column of $EXPECT updated" >&2
  exit 0
fi

if [ "$n_changed" -gt 0 ]; then exit 1; fi
if [ "$n_improved" -gt 0 ]; then exit 2; fi
exit 0
