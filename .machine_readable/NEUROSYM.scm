;; SPDX-License-Identifier: AGPL-3.0-or-later
;; NEUROSYM.scm - Neurosymbolic integration config for ephapax
;; Media-Type: application/vnd.neurosym+scm

(define neurosym-config
  `((version . "1.0.0")
    (project . "ephapax")

    ;; Symbolic reasoning layer (primary for this project)
    (symbolic-layer
      ((type . "linear-logic")
       (reasoning-modes
         ("deductive"      ; Type checking derivations
          "linear"         ; Resource-sensitive reasoning
          "region-scoped"  ; Lexical scoping of allocations
          "separation"))   ; Memory ownership reasoning
       (verification
         ((proof-assistant . "rocq")
          (mechanized-proofs . ("progress" "preservation" "type-safety"))
          (specification-files . ("formal/Syntax.v" "formal/Typing.v" "formal/Semantics.v"))))
       (symbolic-representations
         ((ast . "ephapax-syntax crate")
          (types . "linear-types with region annotations")
          (contexts . "split-able linear contexts")
          (judgments . "typing derivations")))))

    ;; Neural layer (limited use in this project)
    (neural-layer
      ((embeddings . #f)
       (fine-tuning . #f)
       (llm-assisted
         ((code-generation . "claude-code for scaffolding")
          (error-messages . "natural language explanations")
          (documentation . "assisted but human-verified")))
       (future-potential
         ("type-error-explanation-llm"
          "code-completion-with-type-awareness"
          "natural-language-to-ephapax"))))

    ;; Integration points between symbolic and neural
    (integration
      ((symbolic-grounding
         (description "All neural outputs must be type-checked")
         (enforcement "Compiler rejects ill-typed code regardless of source"))
       (proof-verification
         (description "Neural suggestions cannot bypass formal proofs")
         (enforcement "Coq proofs must pass for any type system change"))
       (constraint-propagation
         (description "Linear constraints are symbolic, not probabilistic")
         (enforcement "Type checker is deterministic"))
       (hybrid-workflows
         ((code-assist
            (neural "Generate code skeleton from description")
            (symbolic "Type-check and refine for linearity"))
          (error-explain
            (symbolic "Identify linearity violation")
            (neural "Generate human-friendly explanation"))
          (documentation
            (neural "Draft documentation from code")
            (symbolic "Verify claims against type signatures"))))))

    ;; Formal methods integration
    (formal-methods
      ((theorem-prover . "rocq")
       (proof-style . "mechanized")
       (extracted-code . #f)  ; Not using Coq extraction currently
       (invariants
         ("progress" "Well-typed terms reduce or are values")
         ("preservation" "Reduction preserves types")
         ("linearity" "Linear values used exactly once")
         ("region-safety" "No dangling region references"))))

    ;; Reasoning boundaries
    (boundaries
      ((neural-can
         "Suggest code patterns"
         "Explain errors in natural language"
         "Generate documentation drafts"
         "Assist with boilerplate")
       (neural-cannot
         "Override type checker decisions"
         "Bypass linearity constraints"
         "Modify formal proofs without verification"
         "Generate unsafe memory operations")))))
