#!/bin/bash

# Fuzz testing script for Ephapax
# Run this from the repository root: ./tests/fuzz/run_fuzz.sh

set -e

echo "=== Ephapax Fuzz Testing ==="
echo

# Install cargo-fuzz if not present
if ! command -v cargo-fuzz &> /dev/null; then
    echo "Installing cargo-fuzz..."
    cargo install cargo-fuzz
fi

cd "$(dirname "$0")"

echo "Building fuzz targets..."
cargo fuzz build

echo
echo "Running parser fuzzer (60 seconds)..."
cargo fuzz run parse_fuzzer -- -max_total_time=60

echo
echo "Running type checker fuzzer (60 seconds)..."
cargo fuzz run typecheck_fuzzer -- -max_total_time=60

echo
echo "=== Fuzz testing complete ==="
echo "To run longer sessions:"
echo "  cargo fuzz run parse_fuzzer -- -max_total_time=300"
echo "  cargo fuzz run typecheck_fuzzer -- -max_total_time=300"
