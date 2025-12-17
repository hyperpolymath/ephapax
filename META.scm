;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; META.scm — Ephapax

(define-module (ephapax meta)
  #:export (architecture-decisions development-practices design-rationale))

(define architecture-decisions
  '((adr-001
     (title . "RSR Compliance")
     (status . "accepted")
     (date . "2025-12-15")
     (context . "Linear type system for safe memory management targeting WebAssembly")
     (decision . "Follow Rhodium Standard Repository guidelines")
     (consequences . ("RSR Gold target" "SHA-pinned actions" "SPDX headers" "Multi-platform CI")))
    (adr-002
     (title . "Formal Verification with Coq")
     (status . "accepted")
     (date . "2025-12-17")
     (context . "Type system correctness is critical for memory safety guarantees")
     (decision . "Mechanize type system proofs in Coq")
     (consequences . ("Type safety proven" "Progress and preservation theorems" "Coq 8.18+ dependency")))
    (adr-003
     (title . "WebAssembly Target")
     (status . "accepted")
     (date . "2025-12-17")
     (context . "Need portable, sandboxed execution environment")
     (decision . "Target WebAssembly as primary backend")
     (consequences . ("Browser compatibility" "WASI support" "Region-based memory via linear memory")))))

(define development-practices
  '((code-style
     (languages . ("rust" "coq" "scheme"))
     (formatter . "rustfmt")
     (linter . "clippy"))
    (security
     (sast . "CodeQL")
     (credentials . "env vars only")
     (dependency-scanning . "dependabot"))
    (testing
     (coverage-minimum . 70)
     (formal-proofs . "coq"))
    (versioning (scheme . "SemVer 2.0.0"))))

(define design-rationale
  '((why-rsr "RSR ensures consistency, security, and maintainability.")
    (why-linear-types "Linear types guarantee each value is used exactly once, enabling deterministic memory management without garbage collection.")
    (why-regions "Regions provide scoped memory management, enabling safe bulk deallocation without runtime overhead.")
    (why-wasm "WebAssembly provides a safe, portable, sandboxed execution environment with predictable performance.")))
