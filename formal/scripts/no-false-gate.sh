#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# No-False gate for the Coq development in formal/.
#
# Claim this gate supports: every file in _CoqProject is free of declared
# assumptions and of kernel-check bypasses, and every named result is
# "Closed under the global context". Assuming Coq's own consistency, such
# a development cannot derive False. It says nothing about whether the
# stated theorems are the right theorems.
#
# Four independent checks; any one failing fails the gate:
#   1. token scan on comment- and string-stripped source for assumption
#      vernacular and admit tactics (comment-aware, word-boundary);
#   2. scan of the whitespace-collapsed source for kernel bypass flags
#      (guard, positivity, universe checking, Bypass Check, type-in-type),
#      so a flag split across lines is caught;
#   3. census: `Print Assumptions` on every Theorem/Lemma/Corollary/
#      Proposition/Fact/Remark/Example/Instance, found by sentence (so a
#      keyword and its name may be on different lines) and qualified
#      through nested Modules (coq-decls.awk); each must print
#      "Closed under the global context", and the count must match;
#   4. independent recheck of the compiled .vo files with coqchk: no
#      axiom in the Ephapax namespace, nothing relying on type-in-type,
#      unsafe (co)fixpoints or assumed positivity.
#
# Usage: run from formal/ after the build:  bash scripts/no-false-gate.sh
set -euo pipefail

FILES=$(grep -E '^[^#].*\.v[[:space:]]*$' _CoqProject | awk '{print $1}' | tr '\n' ' ')
MODS=$(for f in $FILES; do m=${f%.v}; printf '%s ' "${m//\//.}"; done)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# shellcheck source=no-false-lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/no-false-lib.sh"

fail=0
for f in $FILES; do mkdir -p "$(dirname "$WORK/$f")"; nofalse_strip "$f" > "$WORK/$f"; done

# 1. Assumption vernacular and admit tactics.
# shellcheck disable=SC2086 # FILES is a deliberate word list
hits=$(cd "$WORK" && nofalse_assume_scan $FILES)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits"
  echo "no-False gate [1]: assumption vernacular or admit tactic found above -> FAIL"; fail=1
fi

# 2. Kernel bypass flags (whitespace-collapsed, so split lines are caught).
# shellcheck disable=SC2086 # FILES is a deliberate word list
hits=$(cd "$WORK" && nofalse_bypass_scan $FILES)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits"
  echo "no-False gate [2]: kernel-check bypass found above -> FAIL"; fail=1
fi

# 3. Census of every named result, qualified through nested Modules.
NAMES="$WORK/names"
: > "$NAMES"
for f in $FILES; do
  m=${f%.v}; m=${m//\//.}
  nofalse_decls "Ephapax.$m" "$WORK/$f" >> "$NAMES" \
    || { echo "no-False gate [3]: could not read the declarations of $f -> FAIL"; fail=1; }
done
total=$(wc -l < "$NAMES")
# The headline results must stay in the census under these names.
for h in Counterexample.preservation_false \
         Counterexample_StepPop.step_pop_disjoint_from_type_l1_FALSE \
         Counterexample_PreservationL1.preservation_l1_FALSE \
         TypingL2.preservation_l2_via_l1 \
         TypingL2.preservation_l2_app_eff_beta_linear \
         TypingL2.preservation_l2_app_eff_beta_ground_nonlinear; do
  grep -qx "Ephapax.$h" "$NAMES" || { echo "no-False gate [3]: headline Ephapax.$h is missing from the census -> FAIL"; fail=1; }
done
{ echo "From Ephapax Require $MODS."; sed 's/.*/Print Assumptions &./' "$NAMES"; } > "$WORK/census.v"
coqtop -quiet -R . Ephapax < "$WORK/census.v" > "$WORK/census.out" 2>&1 || true
closed=$(grep -c 'Closed under the global context' "$WORK/census.out" || true)
if grep -qE '^Axioms:|Error' "$WORK/census.out"; then
  grep -nE -B3 -A8 '^Axioms:|Error' "$WORK/census.out" | head -80
  echo "no-False gate [3]: a named result depends on an assumption, or coqtop errored -> FAIL"; fail=1
fi
if [ "$closed" -ne "$total" ]; then
  echo "no-False gate [3]: $closed of $total named results closed -> FAIL"; fail=1
fi

# 4. Independent kernel recheck of the compiled libraries.
QUAL=$(for m in $MODS; do printf 'Ephapax.%s ' "$m"; done)
# shellcheck disable=SC2086 # QUAL is a deliberate word list
coqchk -o -silent -R . Ephapax $QUAL > "$WORK/coqchk.out" 2>&1 || { tail -30 "$WORK/coqchk.out"; echo "no-False gate [4]: coqchk rejected a library -> FAIL"; fail=1; }
awk '/^\* Axioms:/{a=1;next} /^\* /{a=0} a && NF' "$WORK/coqchk.out" > "$WORK/axioms"
if grep -q 'Ephapax\.' "$WORK/axioms"; then
  cat "$WORK/axioms"; echo "no-False gate [4]: coqchk reports an Ephapax axiom -> FAIL"; fail=1
fi
for k in 'type-in-type' 'unsafe (co)fixpoints' 'positivity is assumed'; do
  if ! grep -A1 -F "$k" "$WORK/coqchk.out" | grep -q '<none>'; then
    grep -A3 -F "$k" "$WORK/coqchk.out"; echo "no-False gate [4]: coqchk: '$k' is not <none> -> FAIL"; fail=1
  fi
done

echo "--- census: $closed/$total named results closed under the global context"
echo "--- coqchk environment axioms (loaded libraries, not necessarily used):"
sed 's/^/    /' "$WORK/axioms"
if [ "$fail" -ne 0 ]; then echo "no-False gate: FAIL"; exit 1; fi
echo "no-False gate: PASS"
