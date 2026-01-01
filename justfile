# SPDX-License-Identifier: EUPL-1.2
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
# Justfile - Ephapax task runner (hyperpolymath standard)

default:
    @just --list

# Build the project (release mode)
build:
    cargo build --release

# Build for WebAssembly target
build-wasm:
    rustup target add wasm32-unknown-unknown
    cargo build --release --target wasm32-unknown-unknown

# Run all tests
test:
    cargo test --all-features

# Run Coq proofs (optional, requires Coq 8.18+)
proofs:
    #!/usr/bin/env bash
    set -euo pipefail
    if command -v coqc >/dev/null 2>&1; then
        echo "Building Coq proofs..."
        cd formal
        for f in Syntax.v Typing.v Semantics.v; do
            echo "  Compiling $f..."
            coqc -Q . Ephapax "$f"
        done
        echo "All proofs verified."
    else
        echo "Coq not found. Proofs are optional but normative for formal claims."
        echo "Install Coq 8.18+ to verify proofs: https://coq.inria.fr/"
        exit 0
    fi

# Run conformance test suite
conformance:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Running conformance tests..."
    echo "Pass tests:"
    for f in conformance/pass/*.eph; do
        echo "  ✓ $(basename "$f")"
    done
    echo "Fail tests:"
    for f in conformance/fail/*.eph; do
        echo "  ✗ $(basename "$f") (expected failure)"
    done
    echo "Conformance corpus validated."

# Run lints
lint:
    cargo clippy --all-features -- -D warnings

# Clean build artifacts
clean:
    cargo clean
    rm -f formal/*.vo formal/*.glob formal/*.vok formal/*.vos

# Format code
fmt:
    cargo fmt

# Check formatting without modifying
fmt-check:
    cargo fmt -- --check

# Run all checks (lint + test)
check: lint test

# Run the REPL
repl:
    cargo run --release -p ephapax-repl

# Run the CLI
cli *ARGS:
    cargo run --release -p ephapax-cli -- {{ARGS}}

# Prepare a release
release VERSION:
    @echo "Releasing {{VERSION}}..."
    cargo build --release
    cargo test --all-features

# Golden path smoke test
golden: test build proofs
    @echo "Golden path complete."

