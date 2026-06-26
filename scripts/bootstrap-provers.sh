#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# bootstrap-provers.sh — one entry point that provisions every prover the
# Ephapax proofs need, using the -iser doctrine (curl+tar from vendor /
# codeload over HTTPS, never `git clone`; idempotent; fail-soft).
#
#   Coq 8.18   → formal/*.v            (scripts/install-coq.sh, apt)
#   Idris2 0.7 → src/abi, src/formal   (scripts/install-idris2.sh, codeload)
#   Zig 0.14   → tools/coproc/*.zig    (scripts/install-zig.sh, ziglang.org)
#
# Why this exists: a fresh Claude-Code-on-the-web container is re-cloned
# from scratch, so the provers must be (re)installed per session. This is
# invoked by the SessionStart hook (.claude/hooks/session-start.sh) and by
# the devcontainer postCreateCommand, and can be run by hand (`just
# bootstrap`).
#
# Fail-soft by construction: each installer exits 0 even on failure, so a
# blocked egress domain degrades gracefully (that prover is simply absent)
# rather than bricking startup. Idris2 is built from source (~10–15 min);
# Coq (apt) and Zig (vendor binary) are quick.
#
# If CLAUDE_ENV_FILE is set (Claude Code on the web), the Idris2 bin dir is
# persisted onto PATH for the rest of the session.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
log() { printf '[bootstrap-provers] %s\n' "$*"; }

# Put the Idris2 install dir on PATH up front so the installers' idempotency
# checks see an already-installed idris2 and skip the ~15-min rebuild.
export PATH="${PREFIX:-$HOME/.idris2}/bin:$PATH"

log "begin — $(date -u 2>/dev/null || echo '?')"

bash "$HERE/install-coq.sh"    || true
bash "$HERE/install-zig.sh"    || true
bash "$HERE/install-idris2.sh" || true

# Persist Idris2 on PATH for the session (Claude Code on the web).
IDRIS2_BIN="${PREFIX:-$HOME/.idris2}/bin"
if [ -x "$IDRIS2_BIN/idris2" ] && [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export PATH=\"$IDRIS2_BIN:\$PATH\"" >> "$CLAUDE_ENV_FILE"
  log "persisted $IDRIS2_BIN to \$CLAUDE_ENV_FILE"
fi
export PATH="$IDRIS2_BIN:$PATH"

log "summary:"
log "  coq:    $(command -v coqc   >/dev/null 2>&1 && coqc   --version 2>/dev/null | head -1 || echo 'absent')"
log "  idris2: $(command -v idris2 >/dev/null 2>&1 && idris2 --version 2>/dev/null | head -1 || echo 'absent')"
log "  zig:    $(command -v zig    >/dev/null 2>&1 && echo "zig $(zig version 2>/dev/null)"  || echo 'absent')"
log "done."
