# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Ephapax build recipes

# Default recipe
import? "contractile.just"

default: build

# Build all Rust crates
build:
    cargo build

# Build for WASM
build-wasm:
    cargo build --target wasm32-unknown-unknown

# Structurally validate emitted wasm for the compilable fixture corpus.
# Compiles each fixture and runs `wasm-tools validate`, failing on any
# structurally invalid module. Authoritative CLI twin of the in-process
# wasmparser assertion in the wasm_e2e tests. Includes the hypatia
# bridge.eph integration target (its multi-arg call-arity codegen bug is
# fixed). hypatia_gui.eph is excluded — it is an import-only module pulled
# in via bridge.eph's `import`, not a standalone program.
validate-wasm:
    #!/usr/bin/env bash
    set -euo pipefail
    command -v wasm-tools >/dev/null 2>&1 || { echo "wasm-tools not found — cargo install wasm-tools"; exit 1; }
    CARGO_INCREMENTAL=0 cargo build -q -p ephapax-cli
    BIN=target/debug/ephapax
    FAIL=0
    for f in tests/v2-grammar/fixtures/*.eph tests/v2-grammar/fixtures/hypatia-port/bridge.eph; do
        out="$(mktemp --suffix=.wasm)"
        if ! "$BIN" compile "$f" -o "$out" >/dev/null 2>&1; then
            echo "  [compile-fail] $f"; FAIL=1; rm -f "$out"; continue
        fi
        if wasm-tools validate "$out" 2>/dev/null; then
            echo "  [valid]   $f"
        else
            echo "  [INVALID] $f"; wasm-tools validate "$out" 2>&1 | sed 's/^/      /'; FAIL=1
        fi
        rm -f "$out"
    done
    if [ "$FAIL" -eq 0 ]; then echo "validate-wasm: all modules structurally valid"; else echo "validate-wasm: FAILED"; exit 1; fi

# Run all tests
test:
    cargo test

# Run conformance test suite
conformance:
    cargo test --test conformance

# Fail if proof/test counts in docs drift from repo state
status-gate:
    ./scripts/status-gate.sh

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
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "panic-attack not found — install from https://github.com/hyperpolymath/panic-attack"

# Format code
fmt:
    cargo fmt --all

# Check formatting without modifying
fmt-check:
    cargo fmt --all --check

# ═══════════════════════════════════════════════════════════════════════════════
# ONBOARDING & DIAGNOSTICS
# ═══════════════════════════════════════════════════════════════════════════════

# Check all required toolchain dependencies and report health
doctor:
    #!/usr/bin/env bash
    echo "═══════════════════════════════════════════════════"
    echo "  Ephapax Doctor — Toolchain Health Check"
    echo "═══════════════════════════════════════════════════"
    echo ""
    PASS=0; FAIL=0; WARN=0
    check() {
        local name="$1" cmd="$2" min="$3"
        if command -v "$cmd" >/dev/null 2>&1; then
            VER=$("$cmd" --version 2>&1 | head -1)
            echo "  [OK]   $name — $VER"
            PASS=$((PASS + 1))
        else
            echo "  [FAIL] $name — not found (need $min+)"
            FAIL=$((FAIL + 1))
        fi
    }
    check "just"              just      "1.25" 
    check "git"               git       "2.40" 
    check "Rust (cargo)"      cargo     "1.80" 
    # Optional tools
    if command -v panic-attack >/dev/null 2>&1; then
        echo "  [OK]   panic-attack — available"
        PASS=$((PASS + 1))
    else
        echo "  [WARN] panic-attack — not found (pre-commit scanner)"
        WARN=$((WARN + 1))
    fi
    echo ""
    echo "  Result: $PASS passed, $FAIL failed, $WARN warnings"
    if [ "$FAIL" -gt 0 ]; then
        echo "  Run 'just heal' to attempt automatic repair."
        exit 1
    fi
    echo "  All required tools present."

# Attempt to automatically install missing tools
heal:
    #!/usr/bin/env bash
    echo "═══════════════════════════════════════════════════"
    echo "  Ephapax Heal — Automatic Tool Installation"
    echo "═══════════════════════════════════════════════════"
    echo ""
    if ! command -v cargo >/dev/null 2>&1; then
        echo "Installing Rust via rustup..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
        source "$HOME/.cargo/env"
    fi
    if ! command -v just >/dev/null 2>&1; then
        echo "Installing just..."
        cargo install just 2>/dev/null || echo "Install just from https://just.systems"
    fi
    echo ""
    echo "Heal complete. Run 'just doctor' to verify."

# Guided tour of the project structure and key concepts
tour:
    #!/usr/bin/env bash
    echo "═══════════════════════════════════════════════════"
    echo "  Ephapax — Guided Tour"
    echo "═══════════════════════════════════════════════════"
    echo ""
    echo '// SPDX-License-Identifier: MPL-2.0'
    echo '// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>'
    echo ""
    echo "Key directories:"
    echo "  src/                      Source code" 
    echo "  lib/                      Library modules" 
    echo "  docs/                     Documentation" 
    echo "  tests/                    Test suite" 
    echo "  .github/workflows/        CI/CD workflows" 
    echo "  .machine_readable/        Machine-readable metadata" 
    echo "  examples/                 Usage examples" 
    echo ""
    echo "Quick commands:"
    echo "  just doctor    Check toolchain health"
    echo "  just heal      Fix missing tools"
    echo "  just help-me   Common workflows"
    echo "  just default   List all recipes"
    echo ""
    echo "Read more: README.adoc, EXPLAINME.adoc"

# Show help for common workflows
help-me:
    #!/usr/bin/env bash
    echo "═══════════════════════════════════════════════════"
    echo "  Ephapax — Common Workflows"
    echo "═══════════════════════════════════════════════════"
    echo ""
    echo "FIRST TIME SETUP:"
    echo "  just doctor           Check toolchain"
    echo "  just heal             Fix missing tools"
    echo ""
    echo "DEVELOPMENT:" 
    echo "  cargo build           Build the project" 
    echo "  cargo test            Run tests" 
    echo "" 
    echo "PRE-COMMIT:"
    echo "  just assail           Run panic-attacker scan"
    echo ""
    echo "LEARN:"
    echo "  just tour             Guided project tour"
    echo "  just default          List all recipes"


# Print the current CRG grade (reads from READINESS.md '**Current Grade:** X' line)
crg-grade:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    echo "$$grade"

# Generate a shields.io badge markdown for the current CRG grade
# Looks for '**Current Grade:** X' in READINESS.md; falls back to X
crg-badge:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    case "$$grade" in \
      A) color="brightgreen" ;; B) color="green" ;; C) color="yellow" ;; \
      D) color="orange" ;; E) color="red" ;; F) color="critical" ;; \
      *) color="lightgrey" ;; esac; \
    echo "[![CRG $$grade](https://img.shields.io/badge/CRG-$$grade-$$color?style=flat-square)](https://github.com/hyperpolymath/standards/tree/main/component-readiness-grades)"
