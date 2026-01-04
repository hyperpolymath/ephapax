;; SPDX-License-Identifier: AGPL-3.0-or-later
;; ECOSYSTEM.scm - Ecosystem position for ephapax
;; Media-Type: application/vnd.ecosystem+scm

(ecosystem
  (version "1.0")
  (name "ephapax")
  (type "programming-language")
  (purpose "Linear type system for safe memory management targeting WebAssembly")

  (position-in-ecosystem
    (category "compilers-and-languages")
    (subcategory "memory-safe-systems-languages")
    (unique-value
      "Combines linear types with region-based memory for compile-time safety without GC"
      "Formal verification of type system soundness in Rocq/Coq"
      "WebAssembly-first design for portable sandboxed execution"
      "Simpler than Rust borrow checker through second-class borrows"))

  (related-projects
    ;; Sibling standards in hyperpolymath ecosystem
    (rhodium-standard-repositories
      (relationship "sibling-standard")
      (description "RSR template this project follows")
      (integration "Uses RSR workflow patterns and file structure"))

    (affinescript
      (relationship "sibling-language")
      (description "OCaml-based affine type system compiler")
      (integration "Shares linear/affine type theory foundations"))

    (rescript-wasm-runtime
      (relationship "potential-consumer")
      (description "ReScript WASM runtime and bindings")
      (integration "Could use Ephapax for memory-critical WASM modules"))

    (svalinn
      (relationship "potential-consumer")
      (description "Edge security shield with custom OCI runtime")
      (integration "Could compile security-critical components in Ephapax"))

    (valence-shell
      (relationship "inspiration")
      (description "Reversible shell with transaction semantics")
      (integration "Shares philosophy of explicit resource management"))

    ;; External inspirations
    (rust-lang
      (relationship "inspiration")
      (description "Ownership and borrowing concepts")
      (notes "Ephapax simplifies with second-class borrows"))

    (linear-haskell
      (relationship "inspiration")
      (description "Linear types in Haskell")
      (notes "Different approach - retrofitted to existing language"))

    (cyclone
      (relationship "inspiration")
      (description "Region-based memory-safe C dialect")
      (notes "Tofte-Talpin region calculus influence"))

    (austral-lang
      (relationship "peer")
      (description "Linear types for systems programming")
      (notes "Similar goals, different design choices"))

    (vale-lang
      (relationship "peer")
      (description "Generational references for memory safety")
      (notes "Alternative to linear types")))

  (what-this-is
    "A compiled programming language with linear types"
    "A formally verified type system with Rocq/Coq proofs"
    "A WebAssembly-targeting compiler"
    "A memory-safe systems programming approach"
    "A research vehicle for linear type theory"
    "A practical tool for writing safe WASM modules")

  (what-this-is-not
    "Not a garbage-collected language"
    "Not a Rust replacement (simpler scope, different trade-offs)"
    "Not an interpreter-only language (compiles to WASM)"
    "Not a general-purpose scripting language"
    "Not backwards-compatible with any existing language"
    "Not dependent on a runtime (aside from minimal WASM support)"))
