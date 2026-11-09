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
#   2. token scan for kernel bypass flags (guard, positivity, universe
#      checking, Bypass Check, type-in-type);
#   3. census: `Print Assumptions` on every Theorem/Lemma/Corollary/
#      Proposition/Fact/Remark/Example/Instance; each must print
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

# Strip nested Coq comments and string literals, keeping line structure.
strip() {
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

fail=0
for f in $FILES; do mkdir -p "$(dirname "$WORK/$f")"; strip "$f" > "$WORK/$f"; done

# 1. Assumption vernacular and admit tactics.
ASSUME='(^|[^A-Za-z0-9_'"'"'.])(Admitted|admit|give_up|Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|Hypotheses|Variable|Variables|Context)([^A-Za-z0-9_'"'"']|$)'
if (cd "$WORK" && grep -nE "$ASSUME" $FILES); then
  echo "no-False gate [1]: assumption vernacular or admit tactic found above -> FAIL"; fail=1
fi

# 2. Kernel bypass flags.
BYPASS='(Unset[[:space:]]+(Guard|Positivity|Universe)[[:space:]]+Checking|Bypass[[:space:]]+Check|Set[[:space:]]+Type[[:space:]]+In[[:space:]]+Type|-type-in-type|bypass_check)'
if (cd "$WORK" && grep -nE "$BYPASS" $FILES); then
  echo "no-False gate [2]: kernel-check bypass found above -> FAIL"; fail=1
fi

# 3. Census of every named result.
NAMES="$WORK/names"
: > "$NAMES"
for f in $FILES; do
  m=${f%.v}; m=${m//\//.}
  { grep -oE '(^|[[:space:]])(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example|Instance)[[:space:]]+[A-Za-z_][A-Za-z0-9_'"'"']*' "$WORK/$f" || true; } \
    | awk -v m="$m" '{print "Ephapax." m "." $NF}' >> "$NAMES"
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
