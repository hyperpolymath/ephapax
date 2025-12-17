;;; STATE.scm — Ephapax
;; SPDX-License-Identifier: EUPL-1.2
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

(define metadata
  '((version . "0.1.0")
    (updated . "2025-12-17")
    (project . "ephapax")
    (description . "Linear type system for safe memory management targeting WebAssembly")))

(define current-position
  '((phase . "v0.1 - Foundation")
    (overall-completion . 40)
    (components
     ((formal-semantics ((status . "complete") (completion . 100)))
      (type-system-design ((status . "complete") (completion . 100)))
      (syntax-crate ((status . "complete") (completion . 100)))
      (typing-crate ((status . "in-progress") (completion . 60)))
      (wasm-codegen ((status . "in-progress") (completion . 50)))
      (runtime ((status . "in-progress") (completion . 50)))
      (lexer ((status . "planned") (completion . 0)))
      (parser ((status . "planned") (completion . 0)))
      (repl ((status . "planned") (completion . 0)))
      (stdlib ((status . "planned") (completion . 0)))))))

(define blockers-and-issues
  '((critical ())
    (high-priority
     (("Complete lexer implementation" . "Required for parsing Ephapax source files")
      ("Complete parser implementation" . "Required for building AST from source")))
    (resolved
     (("Cargo.lock corrupted" . "Fixed: Regenerated lock file")
      ("SECURITY.md template placeholders" . "Fixed: Filled in project-specific values")
      ("SCM files using template-repo name" . "Fixed: Updated to ephapax")))))

(define critical-next-actions
  '((immediate
     (("Implement lexer with logos crate" . high)
      ("Implement parser with chumsky crate" . high)))
    (this-week
     (("Complete type checker implementation" . high)
      ("Add WASM validation tests" . medium)
      ("Add property-based tests with proptest" . medium)))
    (this-month
     (("Implement REPL with wasmtime" . medium)
      ("Begin standard library" . medium)
      ("Add fuzzing infrastructure" . low)))))

(define roadmap
  '((phase-1
     (name . "Foundation")
     (status . "in-progress")
     (completion . 40)
     (target . "Q1 2026")
     (components
      ("Project structure" "CI/CD" "Documentation" "Formal semantics" "Rust skeleton")))
    (phase-2
     (name . "Language Frontend")
     (status . "planned")
     (completion . 0)
     (target . "Q2 2026")
     (components
      ("Lexer (logos)" "Parser (chumsky)" "Error reporting (ariadne)")))
    (phase-3
     (name . "Type System")
     (status . "planned")
     (completion . 0)
     (target . "Q2-Q3 2026")
     (components
      ("Linear context tracking" "Region checking" "Borrow checking" "Type inference")))
    (phase-4
     (name . "Code Generation")
     (status . "planned")
     (completion . 0)
     (target . "Q3 2026")
     (components
      ("IR design" "WASM backend completion" "Memory management")))
    (phase-5
     (name . "Developer Tools")
     (status . "planned")
     (completion . 0)
     (target . "Q4 2026")
     (components
      ("REPL" "CLI" "LSP server" "Interpreter")))
    (phase-6
     (name . "Standard Library")
     (status . "planned")
     (completion . 0)
     (target . "2026-2027")
     (components
      ("Core types" "String operations" "Collections" "I/O" "Memory utilities")))
    (phase-7
     (name . "Frameworks")
     (status . "planned")
     (completion . 0)
     (target . "2027")
     (components
      ("Web framework" "CLI framework" "Testing framework" "Serialization")))
    (phase-8
     (name . "Advanced Features")
     (status . "research")
     (completion . 0)
     (target . "2027+")
     (components
      ("Typestate" "Fractional permissions" "Concurrency" "Metaprogramming")))))

(define milestones
  '((v0.1.0 (target . "Q1 2026") (features . "Foundation complete"))
    (v0.2.0 (target . "Q2 2026") (features . "Lexer + Parser"))
    (v0.3.0 (target . "Q3 2026") (features . "Type checker complete"))
    (v0.4.0 (target . "Q4 2026") (features . "WASM codegen complete"))
    (v0.5.0 (target . "Q4 2026") (features . "REPL + basic stdlib"))
    (v0.6.0 (target . "Q1 2027") (features . "LSP support"))
    (v0.7.0 (target . "Q2 2027") (features . "Core stdlib complete"))
    (v0.8.0 (target . "Q3 2027") (features . "Collections + I/O"))
    (v0.9.0 (target . "Q4 2027") (features . "Frameworks"))
    (v1.0.0 (target . "2028") (features . "Production ready"))))

(define session-history
  '((snapshots
     ((date . "2025-12-17")
      (session . "initial-setup")
      (notes . "Project structure created, Coq proofs, Rust crates, spec document"))
     ((date . "2025-12-17")
      (session . "scm-security-review")
      (notes . "Fixed Cargo.lock corruption, updated SCM files, filled SECURITY.md template, fixed dead code warnings")))))

(define state-summary
  '((project . "ephapax")
    (tagline . "Linear types for safe memory management")
    (completion . 40)
    (blockers . 0)
    (updated . "2025-12-17")
    (next-milestone . "v0.2 - Lexer & Parser")
    (tests-passing . #t)
    (build-clean . #t)))
