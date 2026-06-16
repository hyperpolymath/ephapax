<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Test & Benchmark Requirements

## CRG Grade: C — ACHIEVED 2026-04-04

## Current State — CRG C ACHIEVED (2026-04-04)

- Unit tests: 365 pass / 0 fail (across 17 active workspace crates + `tests/fuzz`; count from `cargo test --workspace --lib -- --list | grep ': test$'`)
- Integration tests: `src/ephapax-cli/tests/integration.rs` (parse->type-check, 18 tests)
- Conformance tests: `src/ephapax-cli/tests/conformance.rs` (spec compliance, 16 tests)
- E2E/WASM tests: `src/ephapax-cli/tests/wasm_e2e.rs` (parse->type-check->compile->wasmtime, 13 tests)
- Property-based tests: `src/ephapax-cli/tests/property_tests.rs` (proptest, 6 properties)
- Contract/invariant tests: `src/ephapax-cli/tests/contract_tests.rs` (type system invariants, 13 tests)
- Aspect tests: `src/ephapax-cli/tests/aspect_tests.rs` (security, performance, correctness, 13 tests)
- Benchmarks: `src/ephapax-parser/benches/parse_bench.rs`, `src/ephapax-vram-cache/benches/cache_bench.rs`
- Total: **486 tests** (`cargo test --workspace --all-targets`); pass/fail enforced by `rust-ci.yml`
- Documented all-target tests: 486

## CRG Testing Taxonomy — Status

| Category | Status | Files |
|----------|--------|-------|
| Unit tests | DONE | 17 active workspace crates + `tests/fuzz` |
| Integration tests | DONE | `tests/integration.rs` |
| Conformance tests | DONE | `tests/conformance.rs` |
| E2E tests | DONE | `tests/wasm_e2e.rs` |
| Property-based (proptest) | DONE | `tests/property_tests.rs` |
| Contract/invariant | DONE | `tests/contract_tests.rs` |
| Aspect tests | DONE | `tests/aspect_tests.rs` |
| Benchmarks | DONE | 2 bench files (criterion) |

## What's Still Missing (for CRG B+)

### Point-to-Point (P2P)
**Source counts:** 49 Rust (19 crates) + 98 .eph files + 17 Idris2 + 3 V

**Coq admitted proofs remaining: 4** (1 outer `Admitted.` in
`formal/Semantics.v` + 3 outer `Admitted.` markers in
`formal/Semantics_L1.v` covering 5 internal `admit.` cases). Single-
source breakdown lives in `PROOF-NEEDS.md §4`; `scripts/status-gate.sh`
reads from there.

#### Crates with ZERO tests:
- Multiple crates show 0 tests in cargo test output
- codegen crates — no tests
- Several small utility crates — no tests

#### .eph files (98):
- Standard library .eph files not tested via automated runner
- Example programs not verified in CI

#### Known issues:
- 4 Admitted markers in Coq (1 in `Semantics.v` — provably-false legacy preservation, sacrosanct; 3 in `Semantics_L1.v` covering 5 inner `admit.` cases — pre-existing L1 structural debt + parallel mirrors per PROOF-NEEDS.md §4)
- 5 remaining tasks (#15-#19) from type checker audit
- interp env-leak fix was made 2026-03-28

### End-to-End (E2E)
- All 98 .eph example programs should compile and run (not automated)
- Multi-file compilation with imports
- REPL interaction (if exists)

### Build & Execution
- [x] cargo build — compiles
- [x] cargo test --workspace --all-targets — 467 pass, 0 fail
- [ ] Compile and run all 98 .eph files — not automated
- [ ] CLI --help works — not verified
- [ ] Self-diagnostic — none

### Benchmarks Needed (for B+)
- Parser throughput on large .eph files
- Type checker performance on complex linear type programs
- Comparison: linear type checking overhead vs non-linear
- Memory usage during compilation
- Verify 2 existing benchmark files actually run

### Self-Tests
- [ ] panic-attack assail on own repo
- [ ] Compile all .eph stdlib files as test suite
- [ ] Resolve remaining Admitted Coq markers (`preservation` in `Semantics.v` is sacrosanct — provably false; 3 in `Semantics_L1.v` track pre-existing L1 structural debt — see PROOF-NEEDS.md §4)

## Priority
- **CRG C** — ACHIEVED (2026-04-04). Property, contract, aspect, and reflexive tests
  now present alongside existing unit/integration/conformance/E2E tests.
- **CRG B** — Requires: coverage metrics, 6+ test targets per module, zero-test
  crates remediated, .eph files tested as a suite.
- **CRG A** — Requires: fuzz harness, formal proof coverage, mutation testing.

## FUZZ TESTING STATUS

- ✅ Real fuzz testing infrastructure added in `tests/fuzz/`
- ✅ Parser fuzzer implemented (`fuzz_targets/parse_fuzzer.rs`)
- ✅ Type checker fuzzer implemented (`fuzz_targets/typecheck_fuzzer.rs`)
- ✅ Seed corpus created with valid and invalid test cases
- ✅ Integrated into workspace Cargo.toml

**Priority: P1 — Real fuzz coverage now exists**

To run fuzz tests:
```bash
cd tests/fuzz
cargo fuzz run parse_fuzzer -- -max_total_time=60
cargo fuzz run typecheck_fuzzer -- -max_total_time=60
```
