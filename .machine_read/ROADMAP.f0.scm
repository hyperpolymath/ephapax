;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ROADMAP.f0.scm - First-pass (f0) roadmap and staged work

(define roadmap-f0
  '((schema . "hyperpolymath.roadmap/1")
    (phase . "f0")
    (phase-name . "Foundation")
    (target-tier . "silver-now")

    ;; ========================================
    ;; F0 OBJECTIVES
    ;; ========================================
    (objectives
      . ("Freeze core language semantics: linear types + regions."
         "Establish single runnable golden path for tests and proofs."
         "Create conformance corpus exercising all type safety properties."
         "Resolve identity drift between README and repo description."
         "Ensure parser exists (even if minimal) to validate syntax claims."))

    ;; ========================================
    ;; COMPLETION STATUS
    ;; ========================================
    (status
      . ((core-type-system . ((status . "complete")
                              (notes . "Linearity, regions, borrows fully designed")))
         (formal-semantics . ((status . "complete")
                              (notes . "Coq proofs in formal/: Syntax.v, Typing.v, Semantics.v")))
         (lexer . ((status . "complete")
                   (notes . "logos-based tokenizer in ephapax-lexer")))
         (parser . ((status . "complete")
                    (notes . "chumsky-based parser in ephapax-parser")))
         (type-checker . ((status . "in-progress")
                          (notes . "Core logic in ephapax-typing, needs test coverage")))
         (wasm-codegen . ((status . "in-progress")
                          (notes . "Basic structure in ephapax-wasm")))
         (interpreter . ((status . "complete")
                         (notes . "Tree-walking interpreter in ephapax-interp")))
         (repl . ((status . "complete")
                  (notes . "Interactive shell in ephapax-repl")))
         (cli . ((status . "complete")
                 (notes . "Command-line interface in ephapax-cli")))
         (conformance-corpus . ((status . "complete")
                                (notes . "Located in conformance/")))
         (coq-proofs-ci . ((status . "staged")
                           (notes . "Proofs build locally; CI integration deferred to f1")))))

    ;; ========================================
    ;; GOLDEN PATH
    ;; ========================================
    (golden-path
      . ((smoke-test
           . ((commands . ("just test" "just build"))
              (expected . "All tests pass, release build succeeds")))
         (proof-check
           . ((command . "just proofs")
              (expected . "Coq proofs compile successfully")
              (staged-note . "Coq is optional for basic usage; proofs are normative for formal claims")))
         (conformance
           . ((command . "just conformance")
              (expected . "All pass/ programs type-check; all fail/ programs are rejected")))))

    ;; ========================================
    ;; CONFORMANCE REQUIREMENTS
    ;; ========================================
    (conformance-requirements
      . ((minimum-pass . 5)
         (minimum-fail . 5)
         (required-pass-cases
           . ("region-basic.eph"
              "borrow-read.eph"
              "linear-consume.eph"
              "pair-destruct.eph"
              "sum-match.eph"))
         (required-fail-cases
           . ("double-use.eph"
              "use-after-consume.eph"
              "escaping-region.eph"
              "illegal-copy.eph"
              "borrow-escape.eph"))
         (comprehensive-example
           . ((file . "region-full-cycle.eph")
              (exercises . ("region allocation" "borrow" "consume"))))))

    ;; ========================================
    ;; STAGED WORK (DEFERRED TO F1)
    ;; ========================================
    (staged-f1
      . ((coq-ci . "Integrate Coq proof checks into CI pipeline")
         (property-testing . "Add property-based tests for type checker")
         (wasm-artifacts . "Generate and test actual WASM output")
         (documentation-generation . "Auto-generate docs from Coq and Rust")
         (benchmark-suite . "Performance benchmarks for compilation")))

    ;; ========================================
    ;; UPGRADE PATH
    ;; ========================================
    (upgrade-path
      . ((current . "silver-now")
         (next . "gold-after-f1")
         (gold-requirements
           . ("Coq proofs in CI"
              "Property testing coverage > 80%"
              "WASM artifacts tested in browser/wasmtime"
              "Full conformance corpus with >20 test cases"))))))
