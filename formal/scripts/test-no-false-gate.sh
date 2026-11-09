#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Self-test for the source scanners of no-false-gate.sh. Needs only bash,
# awk, grep, sed and tr (no Coq), so it runs before the build. Each case is
# a small Coq fragment and the output the scanner must give for it.
#
# Usage: bash formal/scripts/test-no-false-gate.sh
set -euo pipefail
# shellcheck source=no-false-lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/no-false-lib.sh"

T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
pass=0; failn=0
ok()  { pass=$((pass + 1)); }
bad() { failn=$((failn + 1)); echo "FAIL: $1"; }

# Write fragment $2 to $1, stripped, and print the stripped path.
frag() { printf '%s\n' "$2" > "$T/$1.raw"; nofalse_strip "$T/$1.raw" > "$T/$1.v"; echo "$T/$1.v"; }

# --- bypass scan -------------------------------------------------------
expect_bypass() { # name fragment
  local f; f=$(frag "$1" "$2")
  if [ -n "$(nofalse_bypass_scan "$f")" ]; then ok; else bad "bypass not caught: $1"; fi
}
expect_no_bypass() {
  local f; f=$(frag "$1" "$2")
  if [ -z "$(nofalse_bypass_scan "$f")" ]; then ok; else bad "false bypass hit: $1"; fi
}
expect_bypass b_one_line   'Unset Guard Checking.'
expect_bypass b_split      $'Unset\nGuard\nChecking.\nFixpoint f (n : nat) : nat := f n.'
expect_bypass b_restored   $'Local Unset\n  Positivity   Checking.\nInductive T := C : (T -> False) -> T.\nSet Positivity Checking.'
expect_bypass b_universe   $'Unset Universe\n\tChecking.'
expect_bypass b_attr       '#[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.'
expect_no_bypass b_comment $'(* Unset\n Guard Checking *)\nLemma x : True. Proof. exact I. Qed.'
expect_no_bypass b_string  'Definition s := "Unset Guard Checking".'

# --- assumption scan ---------------------------------------------------
expect_assume() {
  local f; f=$(frag "$1" "$2")
  if [ -n "$(nofalse_assume_scan "$f")" ]; then ok; else bad "assumption not caught: $1"; fi
}
expect_no_assume() {
  local f; f=$(frag "$1" "$2")
  if [ -z "$(nofalse_assume_scan "$f")" ]; then ok; else bad "false assumption hit: $1"; fi
}
expect_assume a_axiom $'Axiom\n  bad : False.'
expect_assume a_admitted $'Lemma x : False.\nProof. Admitted.'
expect_no_assume a_qualified 'Lemma x : True. Proof. exact Foo.Axiom_free. Qed.'

# --- declaration census ------------------------------------------------
expect_decls() { # name fragment expected(newline-separated)
  local f got; f=$(frag "$1" "$2")
  got=$(nofalse_decls P "$f" 2>&1) || true
  if [ "$got" = "$3" ]; then ok; else bad "decls $1: expected [$3] got [$got]"; fi
}
expect_decls d_split $'Lemma\n  split_name : True.\nProof. exact I. Qed.\nTheorem\nother\n: True. Proof. exact I. Qed.' \
  $'P.split_name\nP.other'
expect_decls d_nested $'Module A.\n Lemma a1 : True. Proof. exact I. Qed.\n Module Import B.\n  Lemma b1 : True. Proof. exact I. Qed.\n End B.\n Section S.\n  Lemma s1 : True. Proof. exact I. Qed.\n End S.\nEnd A.\nLemma top : True. Proof. exact I. Qed.' \
  $'P.A.a1\nP.A.B.b1\nP.A.s1\nP.top'
expect_decls d_skip $'Module Type MT.\n Lemma hidden : True. Proof. exact I. Qed.\nEnd MT.\nModule F (X : MT).\n Lemma infunctor : True. Proof. exact I. Qed.\nEnd F.\nModule M := F.\nInstance : True := I.\n#[export] Instance named : True := I.\nLocal Lemma loc : True. Proof. exact I. Qed.' \
  $'P.named\nP.loc'
expect_decls d_qualid $'Lemma q : True.\nProof. apply Coq.Init.Logic.I. Qed.\nLemma r : True. Proof. exact I. Qed.' \
  $'P.q\nP.r'
# An unmatched End must fail loudly, not mis-qualify.
f=$(frag d_bad $'Module A.\nLemma x : True. Proof. exact I. Qed.\nEnd B.')
if nofalse_decls P "$f" >/dev/null 2>&1; then bad "unmatched End accepted"; else ok; fi

echo "no-false-gate self-test: $pass passed, $failn failed"
[ "$failn" -eq 0 ]
