;; SPDX-License-Identifier: PMPL-1.0-or-later
;; AGENTIC.scm - AI agent interaction patterns for ephapax
;; Media-Type: application/vnd.agentic+scm

(define agentic-config
  `((version . "1.0.0")
    (project . "ephapax")

    ;; Claude Code configuration
    (claude-code
      ((model . "claude-opus-4-5-20251101")
       (tools . ("read" "edit" "bash" "grep" "glob" "task" "web-search"))
       (permissions . "read-all")
       (context-files
         ".machine_readable/STATE.scm"
         ".machine_readable/META.scm"
         ".machine_readable/ECOSYSTEM.scm"
         ".claude/CLAUDE.md"
         "IMPLEMENTATION-PLAN.md"
         "MILESTONES.md")))

    ;; Agent behavior patterns
    (patterns
      ((code-review
         (style . "thorough")
         (focus . ("linear-type-correctness" "borrow-validity" "region-safety"))
         (verify . ("no-double-use" "no-unused-linear" "no-region-escape")))
       (refactoring
         (style . "conservative")
         (preserve . ("type-signatures" "public-api" "coq-proofs"))
         (automate . ("rustfmt" "clippy-fixes")))
       (testing
         (style . "comprehensive")
         (types . ("unit" "conformance" "property-based"))
         (coverage-target . 80))
       (documentation
         (style . "minimal-but-accurate")
         (format . "asciidoc")
         (update-on . ("api-change" "behavior-change")))
       (commits
         (style . "atomic")
         (message-format . "conventional")
         (sign . true))))

    ;; Language constraints (hyperpolymath standard)
    (constraints
      ((allowed-languages
         "rust"           ; Primary implementation
         "coq"            ; Formal proofs (Rocq)
         "scheme"         ; Machine-readable metadata
         "bash"           ; Build scripts
         "just"           ; Task runner
         "toml"           ; Configuration
         "asciidoc"       ; Documentation
         "markdown")      ; Supplementary docs
       (banned-languages
         "typescript"     ; Use ReScript
         "go"             ; Use Rust
         "python"         ; Use Rust/ReScript
         "makefile"       ; Use Just
         "javascript")))  ; Use ReScript

    ;; Compiler-specific agent guidance
    (compiler-patterns
      ((lexer
         (crate . "ephapax-lexer")
         (tech . "logos")
         (agent-notes . "Token definitions via derive macro, span tracking required"))
       (parser
         (crate . "ephapax-parser")
         (tech . "chumsky")
         (agent-notes . "Combinator style, recovery on errors, ariadne diagnostics"))
       (type-checker
         (crate . "ephapax-typing")
         (agent-notes . "Linear context threading, split contexts for branches"))
       (codegen
         (crate . "ephapax-wasm")
         (tech . "wasm-encoder")
         (agent-notes . "Direct WASM construction, no LLVM"))
       (formal
         (directory . "formal/")
         (tech . "coq")
         (agent-notes . "Any type system change requires proof update"))))

    ;; Task automation hints
    (automation
      ((build . "just build")
       (test . "just test")
       (lint . "just lint")
       (format . "just fmt")
       (proofs . "just proofs")
       (golden . "just golden")
       (repl . "just repl")
       (conformance . "just conformance")))

    ;; Error handling guidance
    (error-handling
      ((type-errors
         (reporter . "ariadne")
         (format . "inline-with-source"))
       (parse-errors
         (recovery . "skip-to-next-statement")
         (collect . "all-errors"))
       (linearity-violations
         (explain . "which-value-used-twice-or-not-at-all")
         (suggest . "explicit-drop-or-copy"))))))
