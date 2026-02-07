#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Run all benchmark suites and generate comparison reports

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT"

echo "==================================="
echo "Ephapax Benchmark Suite"
echo "==================================="
echo ""

# Build Ephapax compiler first
echo "Building Ephapax compiler..."
cargo build --release
echo "✓ Compiler built"
echo ""

# Install AssemblyScript dependencies if needed
if [ ! -d "benches/comparison/assemblyscript/node_modules" ]; then
    echo "Installing AssemblyScript dependencies..."
    cd benches/comparison/assemblyscript
    npm install
    cd "$REPO_ROOT"
    echo "✓ Dependencies installed"
    echo ""
fi

# Run compilation time benchmarks
echo "==================================="
echo "1. Compilation Time Benchmarks"
echo "==================================="
cargo bench --bench compile_time
echo ""

# Run binary size measurements
echo "==================================="
echo "2. Binary Size Measurements"
echo "==================================="
cargo run --release --bin binary_size
echo ""

# Run runtime performance benchmarks
echo "==================================="
echo "3. Runtime Performance Benchmarks"
echo "==================================="
cargo bench --bench runtime_perf
echo ""

echo "==================================="
echo "Benchmark Results"
echo "==================================="
echo ""
echo "Detailed results available in:"
echo "  - target/criterion/         (HTML reports)"
echo "  - benches/comparison/       (compiled WASM files)"
echo ""
echo "To view HTML reports:"
echo "  firefox target/criterion/report/index.html"
echo ""
