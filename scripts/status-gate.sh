#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# status-gate.sh — fail when the doc count markers drift from ground truth.
#
# Two independent checks, selectable so CI can run the cheap one as a
# required gate and the expensive one as a separate, cancellable job:
#
#   --proofs   Proof-count only: greps formal/*.v for `Admitted.` and
#              compares to PROOF-NEEDS.adoc. No toolchain, runs in ~1s.
#              This is the CORE gate — keep it required.
#   --tests    Test-count only: `cargo test --all-targets -- --list` and
#              compares to TEST-NEEDS.adoc. Needs a full Rust build (minutes).
#              SAFE TO SKIP / CANCEL if you are in a rush — it never gates
#              soundness, only doc-count hygiene for the test inventory.
#   (no arg)   Both (the local `just status-gate` default).
set -euo pipefail

MODE="${1:-all}"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

fail() {
  echo "status-gate: $*" >&2
  exit 1
}

extract_claim() {
  local file="$1"
  local label="$2"
  local line

  line="$(grep -Eo "${label}: [0-9]+" "$file" | head -n 1 || true)"
  [ -n "$line" ] || fail "missing '${label}: <n>' marker in ${file}"
  echo "$line" | grep -Eo '[0-9]+' | head -n 1
}

# Compare the first proof count marker with lines starting with `Admitted.`
# (after optional whitespace) in Coq files under formal/. Exit if the marker
# is missing or the counts differ.
check_proofs() {
  # Single-source claim: PROOF-NEEDS.adoc §4 carries the canonical
  # `Coq admitted proofs remaining: <n>` marker (a source-marker count,
  # not an assertion that each marker is routine proof debt).
  local claim actual
  claim="$(extract_claim "PROOF-NEEDS.adoc" "Coq admitted proofs remaining")"
  actual="$(
    (grep -R --include='*.v' -n '^[[:space:]]*Admitted\.' formal || true) \
      | wc -l | tr -d ' '
  )"
  if [ "$claim" != "$actual" ]; then
    fail "PROOF-NEEDS.adoc claims ${claim} admitted markers, actual is ${actual}"
  fi
  echo "status-gate[proofs]: OK — admitted proofs: ${actual}"
}

# Compare the first test count marker with Cargo's listed lines ending in
# `: test`. Exit if the marker is missing, the counts differ, or the listing
# pipeline fails, including when no test lines match.
check_tests() {
  local claim actual
  claim="$(extract_claim "TEST-NEEDS.adoc" "Documented all-target tests")"
  actual="$(
    cargo test --all-targets -- --list \
      | grep ': test$' | wc -l | tr -d ' '
  )"
  if [ "$claim" != "$actual" ]; then
    fail "TEST-NEEDS.adoc claims ${claim} tests, actual is ${actual}"
  fi
  echo "status-gate[tests]: OK — all-target tests: ${actual}"
}

case "$MODE" in
  --proofs) check_proofs ;;
  --tests)  check_tests ;;
  all|"")   check_proofs; check_tests ;;
  *) fail "unknown mode '${MODE}' (use --proofs, --tests, or no argument)" ;;
esac
