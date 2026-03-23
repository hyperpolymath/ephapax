# SPDX-License-Identifier: PMPL-1.0-or-later
# Ephapax build recipes

# Default recipe
default: build

# Build all Rust crates
build:
    cargo build

# Build for WASM
build-wasm:
    cargo build --target wasm32-unknown-unknown

# Run all tests
test:
    cargo test

# Run conformance test suite
conformance:
    cargo test --test conformance

# Build Idris2 formal proofs
idris-build:
    cd src/formal && idris2 --build ephapax-formal.ipkg

# Verify Coq proofs (requires Coq 8.18+)
proofs:
    cd formal && coq_makefile -f _CoqProject -o Makefile && make

# Clean Coq build artefacts
proofs-clean:
    cd formal && rm -f *.vo *.vok *.vos *.glob .*.aux Makefile .Makefile.d

# Golden path: test + build + proofs
golden: test build proofs

# Run panic-attack pre-commit checks
lint:
    panic-attack assail

# Run panic-attacker pre-commit scan
assail:
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "panic-attack not found — install from https://github.com/hyperpolymath/panic-attacker"

# Format code
fmt:
    cargo fmt --all

# Check formatting without modifying
fmt-check:
    cargo fmt --all --check
