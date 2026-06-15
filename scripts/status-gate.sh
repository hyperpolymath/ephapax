#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -euo pipefail

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

# Single-source claim: PROOF-NEEDS.md §4 carries the canonical
# `Coq admitted proofs remaining: <n>` marker. ROADMAP.adoc no longer
# duplicates this; see the per-file table + seam audit in PROOF-NEEDS.md.
PROOF_NEEDS_CLAIM="$(extract_claim "PROOF-NEEDS.md" "Coq admitted proofs remaining")"
TEST_NEEDS_CLAIM="$(extract_claim "TEST-NEEDS.md" "Documented all-target tests")"

ACTUAL_ADMITTED="$(
  (grep -R --include='*.v' -n '^[[:space:]]*Admitted\.' formal || true) \
    | wc -l \
    | tr -d ' '
)"

if [ "$PROOF_NEEDS_CLAIM" != "$ACTUAL_ADMITTED" ]; then
  fail "PROOF-NEEDS.md claims ${PROOF_NEEDS_CLAIM} admitted proofs, actual is ${ACTUAL_ADMITTED}"
fi

ACTUAL_TESTS="$(
  cargo test --all-targets -- --list \
    | grep ': test$' \
    | wc -l \
    | tr -d ' '
)"

if [ "$TEST_NEEDS_CLAIM" != "$ACTUAL_TESTS" ]; then
  fail "TEST-NEEDS.md claims ${TEST_NEEDS_CLAIM} tests, actual is ${ACTUAL_TESTS}"
fi

echo "status-gate: OK"
echo "  admitted proofs: ${ACTUAL_ADMITTED}"
echo "  all-target tests: ${ACTUAL_TESTS}"
