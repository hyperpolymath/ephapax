#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Self-test for the scanners of no-false-gate.sh. The source cases need only bash,
# awk, grep, sed and tr; the sealed-module cases also need coqc and coqtop
# (installed in CI before this step runs). Each case is
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
expect_assume a_admit_obl $'Program Definition p : nat := _.\nAdmit Obligations.'
expect_assume a_admit_obl_split $'Program Definition p : nat := _.\nAdmit\n  Obligations of p.'
expect_no_assume a_qualified 'Lemma x : True. Proof. exact Foo.Axiom_free. Qed.'
expect_no_assume a_admit_ident 'Definition Admit_free := 0. Definition Admittance := 1.'

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
# Definitions, fixpoints and tactic-built definitions closed with Defined.
expect_decls d_defs $'Definition d1 : nat := 0.\nDefinition\n  d2 : True.\nProof. exact I. Defined.\nProgram Definition d3 : nat := 0.\nFixpoint f (n : nat) : nat := match n with 0 => 0 | S m => g m end\nwith g (n : nat) : nat := match n with 0 => 1 | S m => f m end.\nCoFixpoint c : nat := 0.\nSection S.\n Let hidden := 0.\n Definition d4 := hidden.\nEnd S.' \
  $'P.d1\nP.d2\nP.d3\nP.f\nP.c\nP.d4'
# Results in a ":"-sealed body are optional ("?"): the signature may hide
# them. "<:" keeps every field visible, so its results are required.
expect_decls d_sealed $'Module Type S.\n Parameter t : Type.\nEnd S.\nModule M : S.\n Definition t := nat.\n Lemma hidden : True. Proof. exact I. Qed.\nEnd M.\nModule N <: S.\n Definition t := nat.\n Lemma shown : True. Proof. exact I. Qed.\nEnd N.\nModule W : S with Definition t := nat.\n Definition t := nat.\n Lemma hidden2 : True. Proof. exact I. Qed.\nEnd W.\nModule V:S.\n Definition t := nat.\nEnd V.\nModule A := N.' \
  $'?P.M.t\n?P.M.hidden\nP.N.t\nP.N.shown\n?P.W.t\n?P.W.hidden2\n?P.V.t'
expect_decls d_function $'Module M.\n Function f (n : nat) := n.\nEnd M.' 'P.M.f'
expect_decls d_accent $'Module M : S.\n Definition café := 0.\nEnd M.' '?P.M.café'
# An unmatched End must fail loudly, not mis-qualify.
f=$(frag d_bad $'Module A.\nLemma x : True. Proof. exact I. Qed.\nEnd B.')
if nofalse_decls P "$f" >/dev/null 2>&1; then bad "unmatched End accepted"; else ok; fi
# A scope left open (no End at all) must fail too, independently of d_bad.
f=$(frag d_unclosed $'Module A.\nLemma x : True. Proof. exact I. Qed.')
if nofalse_decls P "$f" >/dev/null 2>&1; then bad "unclosed scope accepted"; else ok; fi
f=$(frag d_unclosed_sec $'Section S.\nLemma x : True. Proof. exact I. Qed.')
if nofalse_decls P "$f" >/dev/null 2>&1; then bad "unclosed Section accepted"; else ok; fi


# --- sealed-module census (needs coqc/coqtop; CI installs Coq first) ----
# An exposed field of a ":"-sealed module that uses a standard-library axiom
# must be reported open; a hidden field must be reported hidden; an exposed
# axiom-free field must be reported closed.
if command -v coqc >/dev/null 2>&1 && command -v coqtop >/dev/null 2>&1; then
  mkdir -p "$T/coq"
  cat > "$T/coq/Sealed.v" <<'COQ'
Require Import Coq.Logic.FunctionalExtensionality.
Module Type SIG.
  Parameter uses_funext : forall f g : nat -> nat, (forall x, f x = g x) -> f = g.
  Parameter clean : True.
  Parameter café : True.
End SIG.
Module M : SIG.
  Lemma uses_funext : forall f g : nat -> nat, (forall x, f x = g x) -> f = g.
  Proof. intros; apply functional_extensionality; auto. Qed.
  Lemma clean : True. Proof. exact I. Qed.
  Lemma café : True. Proof. exact I. Qed.
  Lemma hidden : forall f g : nat -> nat, (forall x, f x = g x) -> f = g.
  Proof. intros; apply functional_extensionality; auto. Qed.
End M.
COQ
  if (cd "$T/coq" && coqc -q -R . NFT Sealed.v) >/dev/null 2>&1; then
    names=$(nofalse_strip "$T/coq/Sealed.v" > "$T/coq/Sealed.stripped" \
            && nofalse_decls NFT.Sealed "$T/coq/Sealed.stripped" | tr '\n' ' ')
    if [ "$names" = "?NFT.Sealed.M.uses_funext ?NFT.Sealed.M.clean ?NFT.Sealed.M.café ?NFT.Sealed.M.hidden " ]; then ok
    else bad "sealed census names: $names"; fi
    for c in "M.uses_funext open" "M.clean closed" "M.café closed" "M.hidden hidden"; do
      read -r nm want <<< "$c"
      got=$(cd "$T/coq" && nofalse_sealed_check NFT Sealed "NFT.Sealed.$nm" | head -1)
      if [ "$got" = "$want" ]; then ok; else bad "sealed check $nm: expected $want, got $got"; fi
    done
  else
    bad "could not compile the sealed-module fixture"
  fi
else
  echo "SKIP: sealed-module census cases (coqc/coqtop not installed)"
fi

echo "no-false-gate self-test: $pass passed, $failn failed"
[ "$failn" -eq 0 ]
