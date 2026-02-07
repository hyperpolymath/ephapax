# Ephapax Performance Benchmarks

This document describes the benchmark suite for measuring Ephapax compiler and runtime performance compared to Rust and AssemblyScript.

## Overview

The benchmark suite measures three key aspects:
1. **Compilation Time** - How fast the compiler processes source code
2. **Binary Size** - Size of generated WASM modules (raw and gzipped)
3. **Runtime Performance** - Execution speed of compiled WASM

## Directory Structure

```
benches/
├── comparison/
│   ├── ephapax/          # Ephapax reference implementations
│   │   ├── fibonacci.eph
│   │   ├── factorial.eph
│   │   └── *.wasm       # Generated during benchmarks
│   ├── rust/             # Rust reference implementations
│   │   ├── fibonacci.rs
│   │   ├── factorial.rs
│   │   └── *.wasm       # Generated during benchmarks
│   └── assemblyscript/   # AssemblyScript reference implementations
│       ├── fibonacci.ts
│       ├── factorial.ts
│       ├── package.json
│       └── *.wasm       # Generated during benchmarks
├── scripts/
│   ├── run_all_benchmarks.sh   # Master script to run all benchmarks
│   └── compare_results.py      # Generate markdown comparison tables
├── compile_time.rs      # Criterion benchmark for compilation speed
├── binary_size.rs       # Binary size measurement tool
├── runtime_perf.rs      # Criterion benchmark for runtime performance
└── BENCHMARK-RESULTS.md # Generated comparison report

```

## Running Benchmarks

### Quick Start

Run all benchmarks with the master script:

```bash
./benches/scripts/run_all_benchmarks.sh
```

This will:
1. Build the Ephapax compiler
2. Install AssemblyScript dependencies (if needed)
3. Run compilation time benchmarks
4. Run binary size measurements
5. Run runtime performance benchmarks
6. Generate comparison reports

### Individual Benchmarks

**Compilation Time:**
```bash
cargo bench --bench compile_time
```

**Binary Size:**
```bash
cargo run --release --bin binary_size
```

**Runtime Performance:**
```bash
cargo bench --bench runtime_perf
```

### Viewing Results

After running benchmarks:

- **HTML Reports**: `firefox target/criterion/report/index.html`
- **Markdown Report**: `cat benches/BENCHMARK-RESULTS.md`
- **Compiled WASM**: `ls -lh benches/comparison/*/` *.wasm

## Benchmark Programs

### Fibonacci (fib)

Recursive Fibonacci calculation testing function calls and arithmetic:

```ephapax
fn fib(n: I32): I32 =
    if n <= 1 then n
    else fib(n - 1) + fib(n - 2)

fn main(): I32 = fib(30)
```

### Factorial

Recursive factorial testing function calls and multiplication:

```ephapax
fn factorial(n: I32): I32 =
    if n <= 1 then 1
    else n * factorial(n - 1)

fn main(): I32 = factorial(20)
```

## Methodology

### Compilation Time

- Uses Criterion for statistical benchmarking
- Measures full pipeline: parse → type check → codegen
- Reports mean time and standard deviation
- Runs multiple iterations for statistical significance

### Binary Size

- Measures raw WASM file size in bytes
- Measures gzipped size (simulates network transfer)
- Compares across all three languages
- Uses maximum compression (gzip -9)

### Runtime Performance

- Uses wasmtime as the WASM runtime
- Measures execution time with Criterion
- Instantiates module and calls main() function
- Reports mean time and throughput (ops/second)

## Compilation Flags

### Ephapax
- Default optimization level (no flags currently)
- Mode: Linear (default)

### Rust
- `--target wasm32-unknown-unknown`
- `-C opt-level=3` (maximum optimization)
- `-C lto=fat` (link-time optimization)
- `-C codegen-units=1` (better optimization)
- `--crate-type cdylib`

### AssemblyScript
- `--optimize` (optimization enabled)

## CI Integration

Benchmarks run automatically on:
- Every push to main
- Every pull request
- Weekly schedule (Monday 00:00 UTC)

See `.github/workflows/benchmark.yml` for details.

Pull requests receive automated comments with benchmark results.

## Adding New Benchmarks

To add a new benchmark program:

1. **Create implementations** in all three languages:
   - `benches/comparison/ephapax/mytest.eph`
   - `benches/comparison/rust/mytest.rs`
   - `benches/comparison/assemblyscript/mytest.ts`

2. **Update compile_time.rs**:
   ```rust
   let benchmarks = vec![
       ("fibonacci", "benches/comparison/ephapax/fibonacci.eph"),
       ("factorial", "benches/comparison/ephapax/factorial.eph"),
       ("mytest", "benches/comparison/ephapax/mytest.eph"),  // NEW
   ];
   ```

3. **Update binary_size.rs**:
   ```rust
   for file in &["fibonacci", "factorial", "mytest"] {  // Add "mytest"
       // ...
   }
   ```

4. **Run benchmarks**:
   ```bash
   ./benches/scripts/run_all_benchmarks.sh
   ```

## Interpreting Results

### Compilation Time

- **Lower is better**
- Ephapax should be competitive with Rust
- AssemblyScript typically faster (simpler type system)

### Binary Size

- **Smaller is better**
- Gzipped size more important (network transfer)
- Ephapax should be comparable to Rust
- Linear types may reduce size (fewer runtime checks)

### Runtime Performance

- **Lower time / higher throughput is better**
- All three should be close (WASM is the equalizer)
- Differences often due to optimization strategies
- Ephapax's linear types may enable more aggressive optimization

## Troubleshooting

### AssemblyScript Missing

If AssemblyScript benchmarks are skipped:

```bash
cd benches/comparison/assemblyscript
npm install
cd ../../..
```

### Criterion Errors

If Criterion benchmarks fail to compile:

```bash
cargo clean
cargo bench --bench compile_time
```

### WASM Compilation Failures

Check that wasm32 target is installed:

```bash
rustup target add wasm32-unknown-unknown
```

## Performance Goals

Target performance characteristics:

- **Compilation Time**: Within 20% of Rust compiler
- **Binary Size**: Within 10% of Rust output
- **Runtime Performance**: Within 5% of Rust (WASM eliminates most differences)

## Future Benchmarks

Planned additions:
- String concatenation (heap allocation)
- Array operations (memory access patterns)
- Complex data structures (trees, graphs)
- Real-world algorithms (JSON parsing, sorting)
- Memory usage profiling
- Benchmark against C/C++ (via Emscripten)
