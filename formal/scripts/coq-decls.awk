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
# Module and Section scopes are tracked. A Module adds its name to the
# qualification; a Section does not. Results inside a Module Type or a
# functor (a Module with parameters) are skipped, because they cannot be
# named from outside. "Module X := ..." opens no scope.
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

function sentence(s,    w, k, i, name, kind, skip, path) {
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
    if (index(s, ":=") > 0) return                 # alias / definition: no scope
    kind = (w[i] ~ /\(/ || w[i + 1] ~ /^\(/) ? "functor" : "module"
    push(name, kind); return
  }
  if (w[1] == "Section") { push(w[2], "section"); return }
  if (w[1] == "End") { pop(w[2]); return }

  if (w[1] ~ /^(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example|Instance)$/) {
    name = w[2]; sub(/[^A-Za-z0-9_'].*$/, "", name)
    if (name !~ /^[A-Za-z_][A-Za-z0-9_']*$/) return   # anonymous Instance
    skip = 0; path = prefix
    for (i = 1; i <= depth; i++) {
      if (kinds[i] == "mtype" || kinds[i] == "functor") skip = 1
      if (kinds[i] == "module") path = path "." names[i]
    }
    if (!skip) print path "." name
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
