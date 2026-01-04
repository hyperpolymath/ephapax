;; SPDX-License-Identifier: AGPL-3.0-or-later
;; META.scm - Meta-level information for ephapax
;; Media-Type: application/meta+scheme

(meta
  (architecture-decisions
    (adr-001
      (title "Linear Types as Default")
      (status "accepted")
      (date "2025-12-16")
      (context "Memory safety can be achieved through garbage collection, reference counting, or ownership systems. We need compile-time safety without runtime overhead.")
      (decision "Default to linear types where every value must be used exactly once. Affine types (use at most once) available as opt-in for values that may be dropped.")
      (consequences
        "No garbage collector needed"
        "No use-after-free possible"
        "No memory leaks for linear values"
        "Steeper learning curve for developers"))

    (adr-002
      (title "Region-Based Memory Management")
      (status "accepted")
      (date "2025-12-16")
      (context "Linear types ensure single use, but allocation strategy affects performance. Per-object allocation is expensive.")
      (decision "Use Tofte-Talpin style regions for scoped bulk allocation and deallocation.")
      (consequences
        "Bulk deallocation at region exit"
        "No individual free calls needed"
        "Memory locality improved"
        "Region annotations required in syntax"))

    (adr-003
      (title "Second-Class Borrows")
      (status "accepted")
      (date "2025-12-16")
      (context "Reading a value without consuming it requires temporary access. Full borrowing systems (like Rust) are complex.")
      (decision "Implement second-class borrows that cannot be stored or returned, only passed to function parameters.")
      (consequences
        "Simpler borrow checking than Rust"
        "Cannot store references in data structures"
        "Must explicitly copy when persistence needed"
        "Easier mental model for users"))

    (adr-004
      (title "WebAssembly Primary Target")
      (status "accepted")
      (date "2025-12-16")
      (context "Need a portable, sandboxed execution environment. Native compilation possible but secondary.")
      (decision "Target wasm32-unknown-unknown as primary output format. Native via Cranelift as secondary.")
      (consequences
        "Portable across browsers and runtimes"
        "Sandboxed execution by default"
        "WASI for system access"
        "Linear memory model aligns well"))

    (adr-005
      (title "Formal Verification with Rocq/Coq")
      (status "accepted")
      (date "2025-12-16")
      (context "Type system correctness claims require mathematical proof. Testing alone is insufficient for safety guarantees.")
      (decision "Mechanize type system semantics in Rocq (formerly Coq) and prove Progress and Preservation theorems.")
      (consequences
        "Provably sound type system"
        "Formal specification serves as documentation"
        "Changes must update proofs"
        "Coq expertise required for modifications"))

    (adr-006
      (title "Rust for Implementation")
      (status "accepted")
      (date "2025-12-16")
      (context "Compiler implementation language affects performance, safety, and maintainability. Multiple options exist.")
      (decision "Implement compiler in Rust with workspace of focused crates (lexer, parser, typing, wasm, etc).")
      (consequences
        "Memory safety in implementation"
        "Performance for compilation"
        "Cargo ecosystem for dependencies"
        "Can compile to WASM for web playground"))

    (adr-007
      (title "Combinator Parsing with Chumsky")
      (status "accepted")
      (date "2025-12-16")
      (context "Parser implementation options: hand-written recursive descent, parser generators, or combinator libraries.")
      (decision "Use chumsky parser combinator library for composable, type-safe parsing with good error recovery.")
      (consequences
        "Composable parser definitions"
        "Type-safe at compile time"
        "Built-in error recovery"
        "Slightly slower than hand-written"))

    (adr-008
      (title "Logos for Lexing")
      (status "accepted")
      (date "2025-12-16")
      (context "Lexer can be hand-written or use a lexer generator.")
      (decision "Use logos derive macro for declarative, zero-allocation lexer generation.")
      (consequences
        "Fast tokenization"
        "Zero heap allocation"
        "Derive macro simplicity"
        "Limited to regular languages")))

  (development-practices
    (code-style
      (language "Rust")
      (formatter "rustfmt")
      (linter "clippy")
      (edition "2021")
      (msrv "1.83"))
    (security
      (principle "Defense in depth")
      (dependencies "SHA-pinned")
      (secrets "Never hardcoded")
      (hashing "SHA256+ only"))
    (testing
      (unit-tests "Per crate")
      (conformance-tests "conformance/pass and conformance/fail")
      (formal-proofs "formal/*.v")
      (coverage-target "80%"))
    (versioning "SemVer")
    (documentation "AsciiDoc primary, Markdown accepted")
    (branching "main for stable, feature branches for development"))

  (design-rationale
    (why-linear-types
      "Linear types provide compile-time memory safety without garbage collection overhead. They fit naturally with WASM's linear memory model and enable deterministic resource management.")
    (why-regions
      "Region-based allocation amortizes allocation costs and ensures bulk deallocation. This matches the hierarchical structure of programs (functions, blocks) and simplifies reasoning about lifetimes.")
    (why-not-rust-borrow-checker
      "Full Rust-style borrow checking is complex and has a steep learning curve. Second-class borrows are simpler while covering most read-only access patterns.")
    (why-wasm-first
      "WebAssembly provides portable, sandboxed execution with predictable performance. It's the natural target for a new language in 2025+.")
    (why-formal-verification
      "A type system claiming safety guarantees must prove them. Rocq/Coq mechanization ensures the proofs are machine-checked and the specification is unambiguous.")))
