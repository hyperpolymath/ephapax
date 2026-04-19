# Fuzzing Guide for Ephapax

This guide explains how to use the fuzz testing infrastructure for Ephapax.

## Quick Start

```bash
# From repository root
./tests/fuzz/run_fuzz.sh
```

This will:
1. Install cargo-fuzz if needed
2. Build the fuzz targets
3. Run both fuzzers for 60 seconds each

## Fuzz Targets

### 1. Parser Fuzzer (`parse_fuzzer`)

**Location**: `tests/fuzz/src/parse_fuzzer/lib.rs`

**Purpose**: Test parser robustness against arbitrary input

**Input**: Raw bytes (converted to UTF-8)

**Oracle**: Parser should not panic, hang, or cause memory issues

**Example usage**:
```bash
cd tests/fuzz
cargo fuzz run parse_fuzzer -- -max_total_time=300
```

### 2. Type Checker Fuzzer (`typecheck_fuzzer`)

**Location**: `tests/fuzz/src/typecheck_fuzzer/lib.rs`

**Purpose**: Test type checker correctness on valid ASTs

**Input**: Raw bytes → UTF-8 → Parser → Type checker

**Oracle**: Type checker should not panic on any valid AST

**Example usage**:
```bash
cd tests/fuzz
cargo fuzz run typecheck_fuzzer -- -max_total_time=300
```

## Corpus Management

The seed corpus is in `tests/fuzz/corpus/`:

```bash
# Add a new test case to parser corpus
cp my_test.eph tests/fuzz/corpus/parse_fuzzer/

# Add a new test case to type checker corpus
cp my_test.eph tests/fuzz/corpus/typecheck_fuzzer/
```

## Advanced Usage

### Run with specific options

```bash
# Limit input size to 1KB
cargo fuzz run parse_fuzzer -- -max_len=1024

# Run with 4 workers
cargo fuzz run parse_fuzzer -- -jobs=4

# Run for 10 minutes
cargo fuzz run parse_fuzzer -- -max_total_time=600
```

### Minimize a test case

```bash
cargo fuzz tmin parse_fuzzer tests/fuzz/artifacts/parse_fuzzer/crash-*
```

### View coverage

```bash
cargo fuzz coverage parse_fuzzer
```

## CI Integration

Add to your CI workflow:

```yaml
- name: Fuzz Test
  run: |
    cd tests/fuzz
    cargo fuzz run parse_fuzzer -- -max_total_time=60
    cargo fuzz run typecheck_fuzzer -- -max_total_time=60
```

## Safety Guidelines

1. **Run in isolated environments**: Fuzzers can consume significant resources
2. **Set time limits**: Always use `-max_total_time`
3. **Monitor resource usage**: Fuzzing can use lots of CPU and memory
4. **Start with small inputs**: Use `-max_len=1024` initially
5. **Review crashes carefully**: Not all crashes are security issues

## Troubleshooting

### "No targets specified"
Make sure you're in the `tests/fuzz` directory and have run `cargo fuzz build`.

### Build failures
Ensure all workspace dependencies are built:
```bash
cd ..
cargo build --workspace
cd tests/fuzz
```

### Performance issues
Reduce the input size or run with fewer workers.

## Future Enhancements

- Add WASM codegen fuzzer
- Add differential testing against reference implementation
- Integrate with OSS-Fuzz for continuous fuzzing
- Add mutation testing
