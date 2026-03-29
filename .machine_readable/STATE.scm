;; SPDX-License-Identifier: PMPL-1.0-or-later
;; Ephapax project state — updated 2026-03-29
(state
  (metadata
    (version "0.1.0")
    (last-session "2026-03-29")
    (agent "claude-opus-4.6"))

  (project-context
    (name "ephapax")
    (description "Dyadic linear-affine type system targeting WebAssembly")
    (stage "active-development"))

  (current-position
    (milestone "type-checker-audit-complete")
    (completion-percentage 95)
    (summary "Full type checker audit against Perfect Type Checker checklist.
              Generics, modules, effects, error spans all implemented.
              Formal proofs blocked by Rocq 9.1.1 regression."))

  (route-to-mvp
    (phase "type-system-hardening"
      (status "in-progress")
      (items
        ("SpannedTypeError" . "done")
        ("generics-polymorphism" . "done")
        ("module-system" . "done")
        ("effect-system-ast" . "done")
        ("effect-type-checking" . "done")
        ("parser-generics-imports" . "done")
        ("parser-perform-handle" . "done")
        ("parser-qualified-modules" . "done")
        ("parser-haskell-comments" . "done")
        ("parser-linear-affine-modifiers" . "done")
        ("parser-const-decl" . "done")
        ("parser-named-record-types" . "done")
        ("parser-arrow-return-syntax" . "done")
        ("parser-region-colon-syntax" . "done")
        ("parser-keyword-word-boundary" . "done")
        ("ast-decl-const-variant" . "done")
        ("formal-flags-only-increase" . "Qed")
        ("formal-ctx-transfer" . "20/24-proved-4-need-consumption-tracking")
        ("formal-subst-lemma" . "needs-ctx-transfer")
        ("formal-preservation" . "needs-subst-lemma"))))

  (blockers-and-issues
    (blocker
      (id "rocq-pair-injection")
      (severity "medium")
      (description "Root cause: String.length shadows List.length across
                    Rocq module boundaries. flags_only_increase SOLVED via
                    projected lookups. All .v files compile clean (0 errors).")
      (resolution "1. Fix length shadowing (import String before List)
                   2. Add consumption tracking to ctx_transfer
                   3. Close remaining 6 Admitted")))

  (critical-next-actions
    ("Resolve Rocq 9.1.1 pair injection regression")
    ("Close subst_preserves_typing once Rocq compiles")
    ("Close preservation theorem")
    ("Add effect declarations to type checker (effect registry)")))
