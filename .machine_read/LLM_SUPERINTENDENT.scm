;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; LLM_SUPERINTENDENT.scm - Instructions for LLM assistants

(define llm-superintendent
  '((schema . "hyperpolymath.llm-superintendent/1")
    (purpose
      . "Guide LLM assistants working on the Ephapax codebase.")

    (identity
      . ((project . "Ephapax")
         (pronunciation . "eff-AH-pax")
         (etymology . "Greek ἐφάπαξ meaning 'once for all'")
         (kind . "programming language")
         (domain . "linear types + regions for safe memory management")
         (primary-target . "WebAssembly (wasm32-unknown-unknown)")
         (one-sentence
           . "A language with a linear type system + regions that prevents UAF/leaks and targets WebAssembly.")))

    (core-invariants
      . ("Every linear value must be used exactly once."
         "Borrows are second-class: cannot escape scope, cannot be stored."
         "Regions scope allocations; exiting a region frees all its allocations."
         "Copy is explicit: only unrestricted types can be copied, and copying requires `copy(e)`."
         "The type system prevents: use-after-free, double-free, memory leaks, escaping regions."))

    (implementation-stack
      . ((rust . "Compiler implementation: lexer, parser, type checker, WASM codegen")
         (coq . "Formal specification: typing rules, operational semantics, soundness proofs")))

    (key-files
      . (("spec/SPEC.md" . "Human-readable language specification")
         ("formal/Syntax.v" . "Coq: AST and type definitions")
         ("formal/Typing.v" . "Coq: Linear typing rules")
         ("formal/Semantics.v" . "Coq: Operational semantics + soundness")
         (".machine_read/SPEC.core.scm" . "Machine-readable core semantics")
         (".machine_read/ROADMAP.f0.scm" . "First-pass roadmap and staged work")))

    (do-not
      . ("Do not change the core identity: linear types + regions for memory safety."
         "Do not add implementation languages beyond Rust and Coq."
         "Do not create Makefiles; use justfile recipes."
         "Do not claim features exist that are not implemented."
         "Do not weaken linearity guarantees or make copies implicit."))

    (task-runner
      . ((tool . "just")
         (list-tasks . "just --list")
         (run-tests . "just test")
         (build . "just build")
         (proofs . "just proofs")))

    (semantic-authority
      . ((executable-behavior . "Rust implementation is authoritative")
         (formal-semantics . "Coq proofs are normative for soundness claims")
         (human-spec . "spec/SPEC.md is the source of truth for language design")))

    (conformance-testing
      . ((location . "conformance/")
         (structure . ((pass . "Programs that should type-check successfully")
                       (fail . "Programs with deliberate type errors")))
         (required-failure-cases
           . ("double-use.eph"
              "use-after-consume.eph"
              "escaping-region.eph"
              "illegal-copy.eph"
              "borrow-escape.eph"))))))
