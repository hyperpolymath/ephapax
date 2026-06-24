<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Hypatia findings — outstanding triage handoff (2026-06-24)

> **Status: OPEN.** The Hypatia neurosymbolic gate is now active and reports
> **37 pre-existing findings (5 critical, 7 high, 25 medium)** on ephapax.
> They are **not** fixed — triage + fix is the work below. These are
> pre-existing repo debt that a broken CI pin had been masking, **not**
> introduced by the change that unmasked them.

## How this surfaced

The `scan / Hypatia Neurosymbolic Analysis` gate used to die at "Prepare all
required actions" because the three `hyperpolymath/standards` reusable
workflows were pinned to `5a93d9d57cc0`, a ref that is **not** an ancestor of
`standards` HEAD; that broken pin also transitively referenced a dead
`actions/cache` SHA. PR #315 re-pinned to a published HEAD (later bumped to
`d135b05…` in #316), which let the scan actually run — and report the 37
findings that were previously invisible.

> **Two milestones are not one:** "the workflow now *runs*" and "the workflow
> now *passes*" are different. Fixing the pin achieved the first; the second
> is this document.

## Why this is handed off (cannot be run in the remote sandbox)

The engine is an Elixir escript in `github.com/hyperpolymath/hypatia`. Building
it needs `mix deps.get`, which fetches from **`repo.hex.pm`** — and the remote
session's egress policy returns `403` for the Hex registry (npm/PyPI/crates/Go
are allowed; Hex is not). So the engine must be run on a host where Hex is
reachable (a local machine, or a CI runner), **or** the environment's network
policy must be widened to allow `repo.hex.pm` + `builds.hex.pm`.

## Task 1 — produce the exact findings

```bash
git clone https://github.com/hyperpolymath/hypatia.git ~/hypatia
cd ~/hypatia
mix local.hex --force && mix local.rebar --force
mix deps.get
mix escript.build
# Run with NO GITHUB_TOKEN to match CI (CI had none, so the dependabot /
# secret-scanning / code-scanning alert rules emit nothing — the 37 are
# file-based rules):
HYPATIA_FORMAT=json ./hypatia-cli.sh scan /path/to/ephapax > hypatia-findings.json
jq '[.[].severity] | group_by(.) | map({(.[0]): length}) | add' hypatia-findings.json
```

- Rules are pure functions in `lib/rules/*.ex`; `scan` runs `@all_rule_modules`.
- With no token the 37 are file-based — most likely from `honest_completion`,
  `proof_obligation`, `disambiguation_rules`, `code_safety`, `root_hygiene`,
  `supply_chain`, `structural_drift`, `workflow_audit`, `workflow_hardening`,
  `cicd_rules`, `scorecard_compliance`. (A local token may surface MORE than
  37 — run without one to reproduce the gate's set.)
- Severities depend on the pinned `standards` reusable-workflow version
  (currently `d135b05…`); the 5/7/25 split was observed on the first
  unblocked run and may shift slightly with the engine version.

## Task 2 — triage + fix

1. Group by rule × severity. Fix order: **5 critical → 7 high → 25 medium**.
2. Per finding: true positive → fix in code/docs; false positive / accepted →
   add a justified `rule:path` line to `.hypatia-ignore` (matched `grep -qxF`),
   or enter it in `.hypatia-baseline.json` (schema in `standards`
   `.machine_readable/hypatia-baseline.schema.json`).
3. **Proof / claim findings** (`honest_completion`, `proof_obligation`): fix by
   making *claims* honest (docs/metadata), **never** by editing or force-closing
   the fenced legacy proofs. Per `CLAUDE.md`: do not touch
   `formal/Semantics.v` `Theorem preservation` (provably false; deliberately
   `Admitted`), `formal/Typing.v`, or `formal/Counterexample.v`.
4. **`disambiguation_rules`** findings: ensure the ephapax-vs-AffineScript
   disambiguation markers are present per `CLAUDE.md`.
5. Re-run the scan until `critical = 0` (ideally total within policy). Open a
   PR with a triage table: *finding → disposition → fix*.

## Task 3 — make the gate non-opaque (in `hyperpolymath/standards`)

The gate fails **opaquely**: in `standards`'
`.github/workflows/hypatia-scan-reusable.yml` the scan runs under `bash -e`,
and `hypatia-cli.sh scan` **exits 1 when findings exist**, so the step aborts
*before* the (already-present) `upload-artifact` step and the "warn but don't
fail" critical-check ever run. Net effect: a hard job failure emitting only a
severity count, no detail.

**Fix (in `standards`):** wrap the scan in `set +e` + capture the rc; **always**
upload `hypatia-findings.json` (`if: always()`); write a findings table to
`$GITHUB_STEP_SUMMARY`; enforce the gate in a final dedicated step. Pin
`actions/upload-artifact` by SHA (same supply-chain lesson as PR #315). A full
suggested patch was drafted in-session (not yet applied).

## Guardrails (from `CLAUDE.md`)

- This is `hyperpolymath/ephapax` (not AffineScript). Signed commits.
- Code/config = `MPL-2.0`; prose (`.md`/`.adoc`) = `CC-BY-SA-4.0`.
- Never touch the fenced legacy preservation proof or `Typing.v` /
  `Counterexample.v`. Fix proof/claim findings by aligning claims to reality.
