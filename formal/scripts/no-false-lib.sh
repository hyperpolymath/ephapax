# SPDX-License-Identifier: MPL-2.0
# shellcheck shell=bash
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Source-level scanners shared by no-false-gate.sh and its self-test
# (test-no-false-gate.sh). Sourced, not executed.

NOFALSE_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

# Strip nested Coq comments and string literals, keeping line structure.
nofalse_strip() {
  awk '
    BEGIN { depth = 0; instr = 0 }
    {
      out = ""; n = length($0); i = 1
      while (i <= n) {
        c = substr($0, i, 1); d = substr($0, i, 2)
        if (instr) {
          if (c == "\"") { if (substr($0, i + 1, 1) == "\"") { i += 2; continue } instr = 0 }
          i++; continue
        }
        if (d == "(*") { depth++; i += 2; continue }
        if (depth > 0 && d == "*)") { depth--; i += 2; continue }
        if (depth > 0) { i++; continue }
        if (c == "\"") { instr = 1; i++; continue }
        out = out c; i++
      }
      print out
    }' "$1"
}

# Assumption vernacular and admit tactics: single tokens, so a line scan
# with word boundaries is enough. Prints file:line:text for each hit.
# "Admit" catches "Admit Obligations" however the two words are split
# across whitespace; with no obligation pending it would leave no axiom
# for checks 3 and 4 to find.
NOFALSE_ASSUME='(^|[^A-Za-z0-9_'"'"'.])(Admitted|Admit|admit|give_up|Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|Hypotheses|Variable|Variables|Context)([^A-Za-z0-9_'"'"']|$)'
nofalse_assume_scan() { grep -nHE "$NOFALSE_ASSUME" "$@" || true; }

# Kernel bypass flags. These are multi-word, so each stripped file is
# scanned with all whitespace (newlines included) collapsed to one space;
# "Unset\nGuard\nChecking" is caught. Any Unset counts, even if a later
# Set restores the flag. Prints file: match for each hit.
NOFALSE_BYPASS='(Unset (Guard|Positivity|Universe) Checking|Bypass Check|Set Type In Type|-type-in-type|bypass_check)'
nofalse_bypass_scan() {
  local f
  for f in "$@"; do
    tr -s '[:space:]' ' ' < "$f" | grep -oE "$NOFALSE_BYPASS" | sed "s|^|$f: |" || true
  done
}

# Fully qualified named results of one stripped file (see coq-decls.awk).
nofalse_decls() { awk -v prefix="$1" -f "$NOFALSE_DIR/coq-decls.awk" "$2"; }

# Check one result from a ":"-sealed module body. A sealed body may hide a
# field or expose it through the signature; Print Assumptions on an exposed
# field reports the axioms of its implementation. Usage:
#   nofalse_sealed_check <logical-root> "<Require list>" <qualified name>
# Run from the load-path root. Prints "hidden" when Coq reports that the name
# was not found, "closed" when it is closed under the global context, and
# otherwise "open" followed by Coq's output.
nofalse_sealed_check() {
  local out
  out=$(printf 'From %s Require %s.\nPrint Assumptions %s.\n' "$1" "$2" "$3" \
        | coqtop -quiet -R . "$1" 2>&1 || true)
  if printf '%s\n' "$out" | grep -qF "The reference $3 was not found"; then
    echo hidden
  elif printf '%s\n' "$out" | grep -qF 'Closed under the global context' \
       && ! printf '%s\n' "$out" | grep -qE '^Axioms:|Error'; then
    echo closed
  else
    echo open; printf '%s\n' "$out"
  fi
}
