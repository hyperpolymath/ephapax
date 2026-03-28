;; SPDX-License-Identifier: PMPL-1.0-or-later
;; Ephapax project state — updated 2026-03-28
(state
  (metadata
    (version "0.1.0")
    (last-session "2026-03-28")
    (agent "claude-opus-4.6"))

  (project-context
    (name "ephapax")
    (description "Dyadic linear-affine type system targeting WebAssembly")
    (stage "active-development"))

  (current-position
    (milestone "type-checker-audit-complete")
    (completion-percentage 92)
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
        ("formal-ctx-transfer" . "22/24-proved")
        ("formal-subst-lemma" . "blocked-rocq-9.1.1")
        ("formal-preservation" . "blocked-rocq-9.1.1"))))

  (blockers-and-issues
    (blocker
      (id "rocq-pair-injection")
      (severity "high")
      (description "Rocq 9.1.1 congruence/discriminate/injection fail on
                    option (ty * bool) hypotheses in inductive proof contexts.
                    Works in standalone tests. No upgrade available.")
      (resolution "Wait for Rocq 9.2 or restructure proofs to avoid
                   nth_error on list (ty * bool)")))

  (critical-next-actions
    ("Resolve Rocq 9.1.1 pair injection regression")
    ("Close subst_preserves_typing once Rocq compiles")
    ("Close preservation theorem")
    ("Add effect declarations to type checker (effect registry)")))
