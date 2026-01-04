;; SPDX-License-Identifier: AGPL-3.0-or-later
;; STATE.scm - Project state for ephapax
;; Media-Type: application/vnd.state+scm

(state
  (metadata
    (version "0.1.0")
    (schema-version "1.0")
    (created "2025-12-16")
    (updated "2026-01-04")
    (project "ephapax")
    (repo "github.com/hyperpolymath/ephapax"))

  (project-context
    (name "ephapax")
    (tagline "Linear type system for safe memory management targeting WebAssembly")
    (tech-stack
      (primary "Rust")
      (formal-verification "Rocq/Coq")
      (metadata "Guile Scheme")
      (build-runner "Just")
      (target "wasm32-unknown-unknown")))

  (current-position
    (phase "core-compiler")
    (overall-completion 35)
    (components
      (formal-semantics
        (status "complete")
        (completion 100)
        (files "formal/Syntax.v" "formal/Typing.v" "formal/Semantics.v")
        (notes "Progress and Preservation theorems proven"))
      (ast-syntax
        (status "complete")
        (completion 100)
        (crate "ephapax-syntax"))
      (lexer
        (status "complete")
        (completion 100)
        (crate "ephapax-lexer")
        (tech "logos"))
      (parser
        (status "complete")
        (completion 100)
        (crate "ephapax-parser")
        (tech "chumsky"))
      (type-checker
        (status "in-progress")
        (completion 40)
        (crate "ephapax-typing")
        (remaining
          "linear-context-threading"
          "region-scope-tracking"
          "borrow-validity-checking"
          "branch-agreement-verification"
          "affine-mode-support"))
      (wasm-codegen
        (status "in-progress")
        (completion 30)
        (crate "ephapax-wasm")
        (tech "wasm-encoder")
        (remaining
          "type-compilation"
          "expression-compilation"
          "runtime-function-generation"
          "memory-layout"
          "region-stack-management"))
      (interpreter
        (status "complete")
        (completion 100)
        (crate "ephapax-interp"))
      (repl
        (status "complete")
        (completion 100)
        (crate "ephapax-repl")
        (tech "rustyline"))
      (cli
        (status "complete")
        (completion 100)
        (crate "ephapax-cli")
        (tech "clap"))
      (runtime
        (status "in-progress")
        (completion 20)
        (crate "ephapax-runtime"))
      (stdlib
        (status "planned")
        (completion 0)
        (crate "ephapax-stdlib")))
    (working-features
      "lexical-analysis"
      "parsing-to-ast"
      "coq-formalization"
      "progress-preservation-proofs"
      "interpreter-execution"
      "repl-interaction"
      "cli-interface"))

  (route-to-mvp
    (milestones
      (m0-foundation
        (status "complete")
        (verification "coqc formal/*.v succeeds")
        (items
          "type-system-design"
          "coq-mechanization"
          "progress-theorem"
          "preservation-theorem"
          "ast-crate"
          "ci-pipeline"))
      (m1-lexer
        (status "complete")
        (verification "cargo test -p ephapax-lexer --all-features")
        (items
          "tokenize-keywords"
          "tokenize-operators"
          "tokenize-literals"
          "tokenize-identifiers"
          "tokenize-region-annotations"
          "span-tracking"))
      (m2-parser
        (status "complete")
        (verification "cargo test -p ephapax-parser --all-features")
        (items
          "parse-let-bindings"
          "parse-functions"
          "parse-application"
          "parse-products"
          "parse-sums"
          "parse-regions"
          "parse-borrows"
          "parse-conditionals"
          "parse-operators"
          "operator-precedence"))
      (m3-type-checker
        (status "in-progress")
        (verification "cargo test -p ephapax-typing --all-features")
        (items
          (linearity-check (status "in-progress"))
          (region-scoping (status "in-progress"))
          (borrow-validity (status "in-progress"))
          (type-inference (status "planned"))
          (use-after-move-rejection (status "planned"))
          (region-escape-rejection (status "planned"))
          (double-use-rejection (status "planned"))
          (unused-linear-rejection (status "planned"))))
      (m4-wasm-codegen
        (status "in-progress")
        (verification "wasm-validate output.wasm && wasmtime run output.wasm")
        (items
          (primitives-codegen (status "in-progress"))
          (functions-codegen (status "in-progress"))
          (products-codegen (status "planned"))
          (sums-codegen (status "planned"))
          (regions-codegen (status "planned"))
          (linear-memory-mgmt (status "planned"))
          (region-deallocation (status "planned"))))
      (m5-test-suite
        (status "planned")
        (verification "cargo test --workspace --all-features"))
      (m6-stdlib
        (status "planned")
        (verification "cargo test -p ephapax-stdlib"))
      (m7-repl
        (status "complete")
        (verification "cargo run -- repl"))
      (m8-cli
        (status "complete")
        (verification "cargo run -- help"))))

  (blockers-and-issues
    (critical)
    (high
      (type-checker-linear-context
        (description "Linear context threading not fully implemented")
        (affects "m3-type-checker")
        (assigned "core-team")))
    (medium
      (wasm-region-stack
        (description "Region stack management for WASM needs design")
        (affects "m4-wasm-codegen")))
    (low))

  (critical-next-actions
    (immediate
      "complete-linearity-checking"
      "implement-region-scope-tracking"
      "add-borrow-validity-checks")
    (this-week
      "finish-type-checker-core"
      "basic-wasm-primitives")
    (this-month
      "hello-world-compilation"
      "end-to-end-simple-program"))

  (session-history
    (session
      (date "2026-01-04")
      (accomplishments
        "fixed-codeql-language-matrix"
        "populated-scm-files"))))
