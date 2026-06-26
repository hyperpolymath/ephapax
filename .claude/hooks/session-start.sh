#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# SessionStart hook for Claude Code on the web. Bootstraps the formal-
# methods provers (Coq / Idris2 / Zig) via scripts/bootstrap-provers.sh so
# a fresh remote session can run the proofs without a manual install dance.
#
# SYNCHRONOUS (blocking): the session does not start until the provers are
# provisioned, so the first prompt is GUARANTEED a working Coq/Idris2/Zig
# (no race where Claude runs a proof before its prover exists). The heavy
# Idris2 source build (~10–15 min) is paid ONCE on a cold container; Claude
# Code on the web caches the container after the hook completes, so every
# later session hits the idempotent early-exits and starts fast. Everything
# is fail-soft, so a blocked egress domain degrades gracefully instead of
# wedging startup; and because the installers are idempotent, a hook cut
# short by any timeout simply resumes on the next session until cached.
# PATH for idris2 is persisted via $CLAUDE_ENV_FILE.
#
# (To return to non-blocking startup, restore async mode by emitting
#  `{"async": true, "asyncTimeout": 1200000}` as the first stdout line.)

set -uo pipefail

# Only meaningful in the remote (web) environment; devcontainers use the
# postCreateCommand instead. No-op locally.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

LOG="${TMPDIR:-/tmp}/ephapax-bootstrap.log"
echo "[session-start] Provisioning provers (Coq/Idris2/Zig) before the session starts."
echo "[session-start] First cold start builds Idris2 (~10-15 min, then cached). Full log: $LOG"

# Run synchronously; keep the verbose Idris2 build out of the session
# transcript by logging to a file, then surface a one-line-per-prover summary.
"${CLAUDE_PROJECT_DIR:-.}/scripts/bootstrap-provers.sh" > "$LOG" 2>&1 || true

echo "[session-start] Prover bootstrap finished:"
grep -E '^\[bootstrap-provers\]   (coq|idris2|zig):' "$LOG" || tail -n 3 "$LOG"
