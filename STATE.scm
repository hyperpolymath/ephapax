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
    (overall-completion . 35)
    (components
     ((formal-semantics ((status . "complete") (completion . 100)))
      (type-system-design ((status . "complete") (completion . 100)))
      (syntax-crate ((status . "complete") (completion . 100)))
      (typing-crate ((status . "in-progress") (completion . 60)))
      (wasm-codegen ((status . "in-progress") (completion . 40)))
      (runtime ((status . "in-progress") (completion . 50)))
      (lexer ((status . "planned") (completion . 0)))
      (parser ((status . "planned") (completion . 0)))
      (repl ((status . "planned") (completion . 0)))
      (stdlib ((status . "planned") (completion . 0)))))))

(define blockers-and-issues
  '((critical ())
    (high-priority
     (("Complete lexer implementation" . "Required for parsing")
      ("Complete parser implementation" . "Required for type checking")))))

(define critical-next-actions
  '((immediate
     (("Implement lexer with logos" . high)
      ("Implement parser with lalrpop or chumsky" . high)))
    (this-week
     (("Complete type checker implementation" . high)
      ("Add WASM validation tests" . medium)))
    (this-month
     (("Implement REPL" . medium)
      ("Begin standard library" . medium)
      ("Property-based testing" . medium)))))

(define session-history
  '((snapshots
     ((date . "2025-12-17")
      (session . "initial-setup")
      (notes . "Project structure created, Coq proofs, Rust crates, spec document")))))

(define state-summary
  '((project . "ephapax")
    (tagline . "Linear types for safe memory management")
    (completion . 35)
    (blockers . 0)
    (updated . "2025-12-17")
    (next-milestone . "v0.2 - Lexer & Parser")))
