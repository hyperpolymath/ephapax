<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Audit Report: ephapax — 2026-05-26 — standards#134 reconciliation

## Classification: Estate proof-debt epic, P2 sub-issue (standards#124 / standards#134)

---

## Context

`hyperpolymath/standards#134` (sub-issue of `standards#124`, the estate proof-debt
epic) opened with the following ephapax line item from the 2026-05-18 reconciled
audit:

> **ephapax** — 11 partial; also Rust/SPARK NON-COMPLIANT (no seam)
> 35k-LOC compiler: 11 partial in Idris2; bare Rust, no seam, 49 unsafe.
> Tighten totality + add ABI seam for type-checker invariants + stance doc.

Five sub-tasks, all P2. As of 2026-05-26 only the Coq item is still load-bearing.

## Sub-task ledger (verified by re-grep against `main` 2026-05-26)

| # | Sub-task | Audit (2026-05-18) | Now (2026-05-26) | Status |
|---|----------|--------------------|--------------------|--------|
| 1 | Idris2 `partial` count | 11 (across 9 files) | **0** | ✅ DONE — May-20 totality sub-campaign, PRs #88-#100 |
| 2 | ABI seam (Rust↔Idris2 invariants) | none (NON-COMPLIANT) | `src/abi/Ephapax/ABI/{Types,Foreign,Invariants}.idr` shipped + `abi-verify` CI gate | ✅ DONE — PR #95 |
| 3 | `RUST-SPARK-STANCE.adoc` | missing | 182 lines | ✅ DONE — landed alongside PR #95 |
| 4 | Coq `preservation` Qed | 910 open goals; in-file false "Qed 2026-04-27" claim | `Admitted` with **1 explicit admit in `step_output_context_eq` (Lemma B) + 1 in `step_preserves_type` + 12 cascading congruence goals in `preservation`** | ⚠️ Last open work item — see `formal/PRESERVATION-HANDOFF.md` |
| 5 | Rust `unsafe` blocks | 49 | **30** (14 in `src/ephapax-runtime/src/lib.rs`, 12 in `…/list.rs`, 4 in `src/ephapax-interp/src/lib.rs`) | 🟡 Partial — concentrated at FFI/runtime boundary; policy documented in `RUST-SPARK-STANCE.adoc`; separate audit out of scope for standards#134 |

## Why the original case-count for sub-task 4 was misleading

The audit's "910 open goals" framing reflected the state of the proof script
*before* the 2026-05-20 / 2026-05-24 sessions:

- `910 → 29` via `remember (cfg) ...; induction Hstep` (PR #102)
- `29 → 22` via universal-IH revert (PR #106)
- `22 → 12` via per-case manual closures (PR #116)
- Lemma B `step_output_context_eq` scaffolded with `cfg`-remember pattern; **27 of 35 step rules closed** (PR #121/#124/#126). The 24 listed as "open" in the 2026-05-21 PROOF-NEEDS.md baseline were superseded by the 2026-05-24 cluster closures (handoff doc § "Cluster A — FULLY CLOSED", § "Cluster C — FULLY CLOSED").
- `step_preserves_type` (the type-only sub-lemma) likewise closed all but **one** sub-case.

Empirical verification (this audit, `coqc 8.18.0`):

```
==STPT-OPEN==                                                     1 goal
==LB-OPEN==                                                       1 goal
==PRES-OPEN==                                                    12 goals
```

The 12 in `preservation` are the cascading congruence cases (`S_*_Step`,
`S_StringConcat_Step1/2`, `S_StringLen_Step`, `S_Region_Step`) — they close
mechanically once Lemma B's body is `Qed` (`~2h fan-out`, Phase 2 of
PROOF-NEEDS.md). They are NOT independently hard.

So the actual closure surface is **one structural admit** appearing twice
(`Semantics.v:4885`, `Semantics.v:5963`) — the S_Region_Step `r = r1`
sub-case where an inner step exits the outer region from inside. The doc
characterises this as type-alignment circularity; resolution path agreed
(2026-05-26): **Option 2 — `exit_implies_typing_at_remove_first` helper
lemma proved by structural recursion on `Hstep`**.

## Wall-clock estimate revision

PROOF-NEEDS.md / PRESERVATION-HANDOFF.md previously cited "8-15 focused
hours for Lemma B alone, + ~2h cascade". Those numbers were keyed off the
"31 cases" framing. After the 2026-05-24 cluster closures the actual
remaining surface is one helper lemma (~150 LOC by the doc's own estimate)
plus the cascade.

**Revised estimate: 4-6 hours wall-clock** for the whole chain:
- ~3h Option 2 helper lemma body
- ~1h plug into `step_preserves_type` + Lemma B admits
- ~2h cascade through `preservation`'s 12 congruence goals + S_Region_Step
- ~1h unwind checklist (PROOF-NEEDS / ROADMAP / RUST-SPARK-STANCE / delete
  HANDOFF / `Admitted → Qed`)

## What this audit does NOT discharge

- **Sub-task 5** (30 remaining `unsafe` blocks). FFI-boundary code with
  policy stance documented but no per-block contract review. Worth filing
  as a separate SPARK-style contract-audit ticket; outside the standards#134
  scope as originally framed.
- **Pre-v1.0.0 line items** in PROOF-NEEDS.md ("Linear type consumption",
  "Effect system soundness", "Region safety", "Compiler correctness") —
  these are roadmap targets, not standards#134 sub-tasks.

## Joint-close criteria

PRs that close the Lemma B admit + cascade `preservation` to `Qed` should
land with `Refs hyperpolymath/standards#134` per the epic's joint-close
convention. Joint-close only on explicit agreement from the standards#124
maintainer.
