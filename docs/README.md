<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# `docs/` — Ephapax Documentation

This directory holds long-form documentation. The root README, ROADMAP,
EXPLAINME, and audience-quickstart files are the discoverable entry
points; the material here is the depth behind them.

## Layout

| Subdirectory | What lives here | Examples |
|---|---|---|
| [`specs/`](specs/) | Versioned design specs and the running ledgers of outstanding obligations. | `PROOF-NEEDS.md`, `TEST-NEEDS.md`, `TOPOLOGY.md`, `KNOWN-PROOF-DEBT.md`, `DESIGN-DECISIONS.adoc`, `LANGUAGE-COMPARISON.adoc`, `DESIGN-NOTE-{date}-{topic}.md` |
| [`sessions/`](sessions/) | Date-stamped session logs — focused work sessions, handoffs, audits. | `SESSION-{YYYY-MM-DD}-{topic}.{md,adoc}` |
| [`vision/`](vision/) | Long-form narrative — why the language exists, what it's for. | `EPHAPAX-VISION.adoc` |
| [`papers/`](papers/) | Academic papers (LaTeX sources). | `arcvix-*.tex` |
| [`ai/`](ai/) | LLM warm-up prompts and AI-pair-programming docs. | `llm-warmup-{dev,user}.md` |
| [`governance/`](governance/) | Governance, ethics, conduct audits. | `CRG-AUDIT-{date}.adoc` |
| [`compliance/`](compliance/) | Compliance-axis docs (accessibility, accessibility, etc.). | `ACCESSIBILITY.adoc` |
| [`accessibility/`](accessibility/) | Accessibility-specific manifests, screenshots, tests. | `README.adoc` |
| [`reports/`](reports/) | Generated reports — audits, scans, retros. | `audit/audit-{date}.md` |
| [`quickstart/`](quickstart/) | (Reserved for audience-quickstart expansion; current quickstarts live at repo root for discoverability.) | — |

## Naming conventions

- **Session logs:** `SESSION-YYYY-MM-DD-short-topic.{md,adoc}` — date
  first so chronological sort works. Use the format the original
  session used (`.md` for short notes, `.adoc` for structured longform).
- **Design notes / decisions:** `DESIGN-NOTE-YYYY-MM-DD-topic.md`
  (one decision per file; cite alternatives considered).
- **Audits:** `{KIND}-AUDIT-YYYY-MM-DD.adoc` (e.g. `CRG-AUDIT`).
- **Specs:** descriptive name (`PROOF-NEEDS.md`, `TOPOLOGY.md`) — no
  date prefix because these are ledgers that update in place.

## Authority

When two documents disagree:
- For language semantics: `spec/SPEC.md` and `spec/ephapax-v2-grammar.ebnf` are canonical (see [`../spec/README.md`](../spec/README.md)).
- For proof status: `docs/specs/PROOF-NEEDS.md` (running ledger).
- For the implementation roadmap: `../ROADMAP.adoc`.
- For known formal-verification gaps: `docs/specs/KNOWN-PROOF-DEBT.md`.

If a doc here is out of date, fix it or delete it — don't let it rot.
The repo's policy is "no stale documentation that lies": better an
honest gap than a lie.
