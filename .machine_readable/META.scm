;; SPDX-License-Identifier: PMPL-1.0-or-later
;; Ephapax meta information — updated 2026-03-28
(meta
  (architecture-decisions
    (adr "substitution-based-semantics"
      (status "accepted")
      (date "2026-03-28")
      (decision "Replaced environment-based operational semantics with
                 De Bruijn substitution-based semantics")
      (rationale "Environment-leaking soundness bug: congruence rules
                  propagated env extensions from sub-expression evaluation
                  to sibling expressions, making preservation false"))

    (adr "spanned-type-errors"
      (status "accepted")
      (date "2026-03-28")
      (decision "All type errors carry source Span via SpannedTypeError wrapper")
      (rationale "LSP diagnostics defaulted to (0,0). Sub-expression errors
                  propagate the inner span for maximum precision"))

    (adr "rank-1-polymorphism"
      (status "accepted")
      (date "2026-03-28")
      (decision "Prenex parametric polymorphism with ForAll + unification")
      (rationale "Sufficient for generic linear code. HKT deferred.
                  Type variables are non-linear (Phase 2: linearity bounds)"))

    (adr "module-registry"
      (status "accepted")
      (date "2026-03-28")
      (decision "ModuleRegistry for cross-module type resolution with
                 Import declarations and Public/Private visibility")
      (rationale "Single-file limitation blocked real programs"))

    (adr "effect-system"
      (status "accepted")
      (date "2026-03-28")
      (decision "Algebraic effects with Perform/Handle/ResumeMode in AST,
                 parser grammar, and type checker")
      (rationale "Required by v2 grammar spec. resume(multi) rejects
                  linear captures to prevent duplication"))

    (adr "simplified-ctx-transfer"
      (status "accepted")
      (date "2026-03-28")
      (decision "Dropped 4th conjunct (consumption tracking) from
                 typing_ctx_transfer, keeping typing + types_agree +
                 false_preserved")
      (rationale "Consumption chaining required flags_only_increase as
                  intermediate which created circular dependencies.
                  3-conjunct version sufficient for preservation")))

  (development-practices
    (formal-proofs "Rocq 9.1.1 (Coq fork)")
    (adr "projected-lookups"
      (status "accepted")
      (date "2026-03-28")
      (decision "Added ctx_lookup_ty and ctx_lookup_flag projected accessors
                 to avoid option (ty * bool) discrimination in Rocq 9.1.1")
      (rationale "congruence/discriminate/injection fail on nested pairs inside
                  option in complex inductive proof contexts. Projected lookups
                  decompose into option ty + option bool which Rocq handles fine"))

    (adr "rocq-import-order"
      (status "accepted")
      (date "2026-03-28")
      (decision "Import Coq.Strings.String BEFORE Coq.Lists.List in all .v files")
      (rationale "String.length shadows List.length across module boundaries,
                  breaking eapply/eassumption for cross-module lemma application")))

  (development-practices
    (formal-proofs "Rocq 9.1.1 — 20 Qed, 6 Admitted, 0 compilation errors")
    (testing "cargo test, 35 suites, 290+ tests")
    (ci "GitHub Actions with hypatia-scan")
    (toolchain "asdf: rust stable, ocaml 5.4.1")))
