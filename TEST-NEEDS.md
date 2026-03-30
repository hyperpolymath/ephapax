# Test & Benchmark Requirements

## Current State
- Unit tests: 304 pass / 0 fail (across 19 crates: 42+24+17+16+14+14+13+9+7+6+3+3+3+2+1+1+1+49+63 + many 0-test crates)
- Integration tests: 1 (integration test in one crate)
- E2E tests: NONE
- Benchmarks: 2 files exist
- panic-attack scan: NEVER RUN

## What's Missing
### Point-to-Point (P2P)
**Source counts:** 49 Rust (19 crates) + 98 .eph files + 17 Idris2 + 3 V

The Rust compiler crates have 304 tests — reasonable but many crates have 0:
- Several crates returning "0 passed; 0 failed" in cargo test
- 98 .eph example/stdlib files are not used in automated testing
- Idris2 ABI definitions (17 files) have no verification tests
- V-lang files (3) have no tests

#### Crates with tests (good):
- Parser crate (~42+ tests)
- Type checker crate (~63 tests)
- Evaluator/interpreter crate (~49 tests)
- Linear type system (~24 tests)
- Various other crates with 1-17 tests each

#### Crates with ZERO tests:
- Multiple crates show 0 tests in cargo test output
- codegen crates — no tests
- Several small utility crates — no tests

#### .eph files (98):
- Standard library .eph files not tested via automated runner
- Example programs not verified in CI

#### Known issues (from memory):
- 3 Admitted proofs in Coq (ctx_transfer 15/24, subst_lemma, preservation)
- 5 remaining tasks (#15-#19) from type checker audit
- interp env-leak fix was made 2026-03-28

### End-to-End (E2E)
- Full compilation: .eph source -> parse -> typecheck (linear types) -> eval -> output
- All 98 .eph example programs should compile and run
- Error reporting: introduce type error -> get meaningful error message
- Linear type enforcement: violate linearity -> compiler rejects
- Effect system: track effects -> enforce boundaries
- Multi-file compilation with imports
- REPL interaction (if exists)

### Aspect Tests
- [ ] Security (code injection via macros if any, untrusted .eph file execution)
- [ ] Performance (type checker on deeply nested linear types, large programs)
- [ ] Concurrency (parallel compilation, if applicable)
- [ ] Error handling (all error paths, malformed input, encoding issues)
- [ ] Accessibility (N/A — compiler)

### Build & Execution
- [x] cargo build — compiles
- [x] cargo test — 304 pass, 0 fail
- [ ] Compile and run all 98 .eph files — not automated
- [ ] CLI --help works — not verified
- [ ] Self-diagnostic — none

### Benchmarks Needed
- Parser throughput on large .eph files
- Type checker performance on complex linear type programs
- Comparison: linear type checking overhead vs non-linear
- Memory usage during compilation
- Verify 2 existing benchmark files actually run

### Self-Tests
- [ ] panic-attack assail on own repo
- [ ] Compile all .eph stdlib files as test suite
- [ ] Resolve 3 Admitted Coq proofs

## Priority
- **HIGH** — As a language implementation with novel linear type system, 304 tests across 19 crates is a start but many crates have 0 tests. The 98 .eph files should be compiled as an automated test suite but are not. The Coq proofs have 3 Admitted holes. For a language that claims provable linearity, incomplete proofs and untested codegen paths undermine the core value proposition.

## FAKE-FUZZ ALERT

- `tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
