# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# List the named results of one comment- and string-stripped Coq file,
# fully qualified, one per line: <prefix>.<Module>...<name>.
#
# Input must already have comments and string literals removed (see
# strip() in no-false-gate.sh). The file is read as one stream and split
# into Coq sentences at a "." followed by whitespace or end of input, so a
# keyword and its name may sit on different lines.
#
# A named result is a Theorem, Lemma, Corollary, Proposition, Fact,
# Remark, Example, named Instance, Definition, Fixpoint, CoFixpoint or Function
# (with any Program/Local/Global prefix), so a proof closed with
# "Defined." or a definition built by tactics is censused like a lemma.
# For a mutual "Fixpoint f ... with g ...", only f is listed: f and g are
# bodies of one mutual block, so Print Assumptions on f reaches g's
# dependencies. "Let" is not listed: inside a Section it is discharged
# and has no name afterwards.
#
# Module and Section scopes are tracked. A Module adds its name to the
# qualification; a Section does not. "Module X := ..." opens no scope.
# Results inside a Module Type or a functor (a Module with parameters) are
# skipped, because the census cannot name them from outside. Gate checks
# 1, 2 and 4 still cover them (no assumption vernacular or admit, no kernel
# bypass, no Ephapax axiom under coqchk); check 3 does not see a dependency
# of such a result on a standard-library axiom.
#
# Inside a module sealed by a signature ("Module M : S."), a field the
# signature exposes can be named, and Print Assumptions on it reports the
# axioms its implementation uses; a field the signature hides cannot be
# named. The parser cannot tell the two apart, so it lists every result in
# a sealed body with a leading "?" (an optional name). The gate checks each
# optional name and skips it only when Coq reports that it was not found.
# A transparently ascribed module ("Module M <: S.") keeps every field and
# is censused normally.
#
# Usage: awk -v prefix=Ephapax.File -f coq-decls.awk stripped.v
BEGIN { buf = ""; depth = 0 }
{ buf = buf " " $0 }
END {
  gsub(/[[:space:]]+/, " ", buf)
  n = 0
  while (match(buf, /\.( |$)/)) {
    s = substr(buf, 1, RSTART - 1)
    buf = substr(buf, RSTART + RLENGTH)
    sentence(s)
  }
  if (buf ~ /[^ ]/) sentence(buf)
}

function trim(x) { sub(/^ +/, "", x); sub(/ +$/, "", x); return x }

function sentence(s,    w, k, i, name, kind, skip, opt, path, rest, valid) {
  s = trim(s)
  # Drop attributes and locality/flag prefixes.
  while (match(s, /^#\[[^]]*\] */)) s = substr(s, RLENGTH + 1)
  while (match(s, /^(Local|Global|Polymorphic|Monomorphic|Program|Cumulative|NonCumulative|Private) /))
    s = substr(s, RLENGTH + 1)
  k = split(s, w, " ")
  if (k == 0) return

  if (w[1] == "Module") {
    i = 2
    if (w[i] == "Type") { if (index(s, ":=") == 0) push(w[3], "mtype"); return }
    if (w[i] == "Import" || w[i] == "Export") i++
    name = w[i]; sub(/[(:].*$/, "", name)
    if (name == "") return
    # ":=" outside a "with Definition/Module x := ..." constraint makes
    # this an alias or a module defined by an expression: no scope.
    rest = s
    while (match(rest, /with +(Definition|Module) +[A-Za-z0-9_'.]+ *:=/))
      rest = substr(rest, 1, RSTART - 1) substr(rest, RSTART + RLENGTH)
    if (index(rest, ":=") > 0) return
    kind = (w[i] ~ /\(/ || w[i + 1] ~ /^\(/) ? "functor" : "module"
    if (kind == "module") {
      # Text after the name; a lone ":" (not "<:") seals the module.
      rest = s; sub(/^Module +((Import|Export) +)?/, "", rest)
      rest = substr(rest, length(name) + 1)
      if (rest ~ /^ *:([^=]|$)/) kind = "sealed"
    }
    push(name, kind); return
  }
  if (w[1] == "Section") { push(w[2], "section"); return }
  if (w[1] == "End") { pop(w[2]); return }

  if (w[1] ~ /^(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example|Instance|Definition|Fixpoint|CoFixpoint|Function)$/) {
    name = w[2]; sub(/[(:{].*$/, "", name)
    # Accept non-ASCII identifier bytes intact; never census a prefix.
    valid = name; gsub(/[A-Za-z0-9_']/, "", valid)
    if (name == "" || name ~ /^[0-9']/ || valid ~ /[[:cntrl:][:punct:][:space:]]/) return
    skip = 0; opt = ""; path = prefix
    for (i = 1; i <= depth; i++) {
      if (kinds[i] == "mtype" || kinds[i] == "functor") skip = 1
      if (kinds[i] == "sealed") opt = "?"
      if (kinds[i] == "module" || kinds[i] == "sealed") path = path "." names[i]
    }
    if (!skip) print opt path "." name
  }
}

function push(nm, kd) { depth++; names[depth] = nm; kinds[depth] = kd }
function pop(nm) {
  if (depth > 0 && names[depth] == nm) { depth--; return }
  # Mismatched End: report loudly rather than mis-qualify silently.
  print "coq-decls.awk: unmatched End " nm " in " prefix > "/dev/stderr"
  bad = 1
}
END { if (depth != 0) { print "coq-decls.awk: " depth " unclosed scope(s) in " prefix > "/dev/stderr"; exit 2 }
      if (bad) exit 2 }
