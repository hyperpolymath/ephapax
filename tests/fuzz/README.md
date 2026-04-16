# Fuzz Testing for Ephapax

This directory contains fuzz testing harnesses for Ephapax using cargo-fuzz.

## Current Status

- ✅ Property-based tests exist (proptest in `src/ephapax-cli/tests/property_tests.rs`)
- ❌ No real fuzz testing implemented yet
- The `placeholder.txt` file was a scorecard requirement but provides no actual fuzzing

## Fuzz Targets Needed

### 1. Parser Fuzzer
- **Target**: `fuzz_targets/parse_fuzzer.rs`
- **Goal**: Find parser crashes, infinite loops, or incorrect AST generation
- **Input**: Arbitrary byte sequences treated as UTF-8 source code
- **Oracle**: Parser should not panic or hang

### 2. Type Checker Fuzzer
- **Target**: `fuzz_targets/typecheck_fuzzer.rs`
- **Goal**: Find type checker crashes or incorrect type assignments
- **Input**: Valid ASTs from parser (use parser fuzzer output as input)
- **Oracle**: Type checker should not panic

### 3. WASM Codegen Fuzzer
- **Target**: `fuzz_targets/codegen_fuzzer.rs`
- **Goal**: Find code generation crashes or invalid WASM output
- **Input**: Type-checked ASTs
- **Oracle**: Generated WASM should validate and not crash wasmtime

## Setup Instructions

```bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Initialize fuzzing in this directory
cd tests/fuzz
cargo fuzz init

# Build fuzz targets
cargo fuzz build

# Run parser fuzzer
cargo fuzz run parse_fuzzer
```

## Corpus

Start with a seed corpus of:
- Valid Ephapax programs from `examples/`
- Invalid programs that currently fail gracefully
- Edge cases (empty files, very large numbers, deep nesting)

## Integration

Add to root Cargo.toml:
```toml
[profile.release]
debug = 1

[workspace]
members = [
    # ... existing members ...
    "tests/fuzz",
]
```

## CI Integration

Add fuzzing to CI workflows:
```yaml
- name: Fuzz Test
  run: |
    cd tests/fuzz
    cargo fuzz run parse_fuzzer -- -max_total_time=60
```

## Safety Notes

- Run fuzzers in isolated environments
- Set time/memory limits
- Monitor for resource exhaustion
- Use `-max_len` to limit input size initially
