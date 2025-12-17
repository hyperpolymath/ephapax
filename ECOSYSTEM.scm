;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ECOSYSTEM.scm — Ephapax

(ecosystem
  (version "1.0.0")
  (name "ephapax")
  (type "programming-language")
  (purpose "Linear type system for safe memory management targeting WebAssembly")

  (position-in-ecosystem
    "Core research language in the hyperpolymath ecosystem demonstrating linear types and region-based memory management. Follows RSR Gold guidelines.")

  (related-projects
    (project (name "rhodium-standard-repositories")
             (url "https://github.com/hyperpolymath/rhodium-standard-repositories")
             (relationship "standard"))
    (project (name "linear-types-research")
             (relationship "research-foundation"))
    (project (name "wasm-ecosystem")
             (relationship "target-platform")))

  (what-this-is
    "A research programming language exploring:
     - Linear types for memory safety without garbage collection
     - Region-based memory management for deterministic deallocation
     - WebAssembly compilation for safe, portable execution
     - Formal verification of type system soundness via Coq proofs")

  (what-this-is-not
    "- NOT a general-purpose production language (yet)
     - NOT exempt from RSR compliance
     - NOT a garbage-collected language"))
