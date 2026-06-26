#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# SessionStart hook for Claude Code on the web. Bootstraps the formal-
# methods provers (Coq / Idris2 / Zig) via scripts/bootstrap-provers.sh so
# a fresh remote session can run the proofs without a manual install dance.
#
# ASYNC (non-blocking): the first stdout line opts into async mode, so the
# session becomes usable immediately while the provers install in the
# background. Coq (apt) and Zig (vendor binary) land in ~1–2 min; the
# Idris2 source build takes ~10–15 min and finishes within asyncTimeout.
# Everything is idempotent + fail-soft, so re-runs and blocked egress are
# both safe. PATH for idris2 is persisted via $CLAUDE_ENV_FILE.

set -uo pipefail

# Opt into async so session startup is not blocked by the ~15-min Idris2 build.
echo '{"async": true, "asyncTimeout": 1200000}'

# Only meaningful in the remote (web) environment; devcontainers use the
# postCreateCommand instead. No-op locally.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

exec "${CLAUDE_PROJECT_DIR:-.}/scripts/bootstrap-provers.sh" \
  > "${TMPDIR:-/tmp}/ephapax-bootstrap.log" 2>&1
