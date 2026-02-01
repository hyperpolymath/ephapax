;; SPDX-License-Identifier: PMPL-1.0-or-later
;; PLAYBOOK.scm - Operational runbook for ephapax
;; Media-Type: application/vnd.playbook+scm

(define playbook
  `((version . "1.0.0")
    (project . "ephapax")

    ;; Development procedures
    (procedures
      ((setup
         (description "Initial development environment setup")
         (steps
           (("install-rust" . "rustup default stable")
            ("add-wasm-target" . "rustup target add wasm32-unknown-unknown")
            ("install-just" . "cargo install just")
            ("install-coq" . "opam install coq.8.18.0")  ; Optional
            ("verify" . "just golden"))))

       (build
         (description "Build the compiler")
         (commands
           (("full-build" . "just build")
            ("wasm-build" . "just build-wasm")
            ("single-crate" . "cargo build -p ephapax-<crate>"))))

       (test
         (description "Run test suites")
         (commands
           (("all-tests" . "just test")
            ("single-crate" . "cargo test -p ephapax-<crate>")
            ("conformance" . "just conformance")
            ("with-coverage" . "cargo tarpaulin --workspace"))))

       (lint
         (description "Code quality checks")
         (commands
           (("clippy" . "just lint")
            ("format-check" . "just fmt-check")
            ("format-fix" . "just fmt"))))

       (proofs
         (description "Verify formal proofs")
         (commands
           (("verify-all" . "just proofs")
            ("single-file" . "coqc -Q formal Ephapax formal/<file>.v")))
         (notes "Requires Coq 8.18+. Proofs are optional but normative."))

       (release
         (description "Prepare a release")
         (steps
           (("verify-tests" . "just test")
            ("verify-proofs" . "just proofs")
            ("verify-lint" . "just lint")
            ("build-release" . "just release VERSION")
            ("tag" . "git tag -s v<VERSION>")
            ("push" . "git push origin main --tags"))))

       (repl
         (description "Interactive development")
         (commands
           (("start-repl" . "just repl")
            ("run-file" . "just cli run <file>.eph")
            ("type-check" . "just cli check <file>.eph"))))

       (debug
         (description "Debugging procedures")
         (commands
           (("verbose-build" . "RUST_BACKTRACE=1 cargo build")
            ("debug-lexer" . "cargo test -p ephapax-lexer -- --nocapture")
            ("debug-parser" . "cargo test -p ephapax-parser -- --nocapture")
            ("wasm-validate" . "wasm-validate output.wasm")
            ("wasm-run" . "wasmtime run output.wasm"))))))

    ;; Troubleshooting guides
    (troubleshooting
      ((lexer-errors
         (symptoms "Unexpected token" "Unknown character")
         (diagnosis "Check ephapax-lexer token definitions")
         (resolution "Add missing token pattern or escape special chars"))

       (parser-errors
         (symptoms "Parse error at line X" "Expected X but found Y")
         (diagnosis "Check parser combinator definitions in ephapax-parser")
         (resolution "Add missing production or fix operator precedence"))

       (type-errors
         (symptoms "Linearity violation" "Region escape" "Type mismatch")
         (diagnosis "Check ephapax-typing rules")
         (resolution
           "Linearity: Ensure single use of linear values"
           "Region escape: Value cannot outlive its region"
           "Type mismatch: Check expected vs actual types"))

       (wasm-errors
         (symptoms "Invalid WASM module" "Runtime trap")
         (diagnosis "Run wasm-validate, check memory layout")
         (resolution "Verify wasm-encoder output, check region stack"))

       (proof-failures
         (symptoms "Coq proof incomplete" "Qed fails")
         (diagnosis "Type system change broke proof invariant")
         (resolution "Update proof to match new semantics"))))

    ;; CI/CD integration
    (ci-cd
      ((github-actions
         (workflows
           ("ci.yml" "Main build and test")
           ("codeql.yml" "Security scanning")
           ("quality.yml" "Quality gates")
           ("scorecard.yml" "OpenSSF scorecard"))
         (required-checks
           ("cargo build" "cargo test" "cargo clippy")))

       (pre-commit
         (hooks
           ("fmt-check" . "cargo fmt -- --check")
           ("clippy" . "cargo clippy -- -D warnings")
           ("test" . "cargo test --workspace")))))

    ;; Alerts and monitoring
    (alerts
      ((build-failure
         (severity "high")
         (action "Check CI logs, fix immediately"))
       (proof-regression
         (severity "critical")
         (action "Type system soundness at risk, prioritize fix"))
       (security-advisory
         (severity "critical")
         (action "Review dependency, update or patch"))))

    ;; Contacts
    (contacts
      ((maintainer
         (name "Jonathan D.A. Jewell")
         (role "Primary maintainer")
         (github "hyperpolymath"))
       (security
         (email "See SECURITY.md")
         (pgp "Available on request"))))))
