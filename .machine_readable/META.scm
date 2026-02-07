;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Architectural decisions and project meta-information
;; Media-Type: application/meta+scheme

(define-meta ephapax
  (version "1.0.0")

  (architecture-decisions
    ;; ADR format: (adr-NNN status date context decision consequences)
    ((adr-001 accepted "2026-01-30"
      "Need to establish repository structure and standards"
      "Adopt RSR (Rhodium Standard Repository) conventions from rsr-template-repo"
      "Ensures consistency with 500+ repos in hyperpolymath ecosystem. "
      "Enables automated quality enforcement via gitbot-fleet and Hypatia.")

    (adr-002 accepted "2026-02-07"
      "Language supports both strict and permissive type checking modes"
      "Implement dyadic design: Affine mode (permissive, use ≤1 time) AND Linear mode (strict, use exactly 1 time)"
      "Both modes are first-class citizens, not a migration path. "
      "Affine mode enables prototyping and exploration with optional cleanup. "
      "Linear mode guarantees resource safety and prevents memory leaks. "
      "Same syntax, different strictness via --mode flag. "
      "Innovation: First language where you toggle between strict/permissive type systems.")

    (adr-003 accepted "2026-02-07"
      "Need to drive project to production readiness like phronesis"
      "Complete type checker (60%→100%), WASM codegen (30%→100%), build production binary, implement stdlib, create LSP, expand tests"
      "Makes Ephapax production-ready with working binaries for BOTH affine and linear modes. "
      "Provides reference implementation for dyadic language design. "
      "Enables real-world adoption and validation of affine/linear type systems.")))

  (development-practices
    (code-style
      "Follow hyperpolymath language policy: "
      "Prefer ReScript, Rust, Gleam, Elixir. "
      "Avoid TypeScript, Go, Python per RSR.")
    (security
      "All commits signed. "
      "Hypatia neurosymbolic scanning enabled. "
      "OpenSSF Scorecard tracking.")
    (testing
      "Comprehensive test coverage required. "
      "CI/CD runs on all pushes.")
    (versioning
      "Semantic versioning (semver). "
      "Changelog maintained in CHANGELOG.md.")
    (documentation
      "README.adoc for overview. "
      "STATE.scm for current state. "
      "ECOSYSTEM.scm for relationships.")
    (branching
      "Main branch protected. "
      "Feature branches for new work. "
      "PRs required for merges."))

  (design-rationale
    (why-rsr
      "RSR provides standardized structure across 500+ repos, "
      "enabling automated tooling and consistent developer experience.")
    (why-hypatia
      "Neurosymbolic security scanning combines neural pattern recognition "
      "with symbolic reasoning for fast, deterministic security checks.")
    (why-dyadic
      "Dyadic design (affine + linear modes) addresses real-world trade-offs: "
      "Affine mode for rapid prototyping where flexibility is key, "
      "Linear mode for production where safety guarantees are critical. "
      "Developers choose mode per use case, not per project maturity. "
      "Eliminates false choice between 'move fast' and 'be safe'.")
    (why-two-stage-compiler
      "Stage 1 (Idris2): Dependent types enable formal verification of type system correctness. "
      "Stage 2 (Rust): Performance-oriented WASM compilation with zero-cost abstractions. "
      "Separation allows formal proofs without sacrificing runtime efficiency.")
    (why-wasm-target
      "WebAssembly provides sandboxed execution, portability, and predictable performance. "
      "Linear types naturally map to WASM linear memory model. "
      "Enables deployment to web, edge, embedded without code changes."))))
