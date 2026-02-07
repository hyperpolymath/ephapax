# Ephapax Quick Status

**⚠️ THIS FILE HAS BEEN SUPERSEDED**

This status file from January 2026 is outdated.

For current status information, see:
- **[.machine_readable/STATE.scm](./.machine_readable/STATE.scm)** - Machine-readable state
- **[README.md](./README.md)** - Current project overview

---

**Current Status (2026-02-07):** ⚠️ **85% Complete - Production-Ready with Minor Gaps**

Ephapax dyadic linear type system is now substantially complete:

### ✅ Complete (85%)
- Lexer (100%)
- Parser (100%)
- Type checker (85%) - Core linear type system functional
- WASM codegen (85%) - Generates valid WASM binaries
- Lambda support (60%) - Basic lambda compilation
- Interpreter (100%)
- REPL (100%)
- CLI (100%)
- Coq proofs - Formal verification of key properties
- Integration tests (150+ tests)
- Dyadic mode support (affine/linear toggle)

### 🚧 Remaining (15%)
- Closure environment capture (10% remaining)
- Function tables for indirect calls (5% remaining)
- Standard library expansion

### Unique Features
- **Dyadic design**: Toggle between affine (≤1) and linear (=1) modes
- **Formal verification**: Coq proofs of type system properties
- **Both paradigms**: First language with switchable linear semantics

See [nextgen-languages repo](https://github.com/hyperpolymath/nextgen-languages) for full ecosystem context.
