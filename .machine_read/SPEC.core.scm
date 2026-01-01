;; SPDX-License-Identifier: EUPL-1.2
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; SPEC.core.scm - Machine-readable core language semantics

(define spec-core
  '((schema . "hyperpolymath.spec-core/1")
    (version . "0.1.0")
    (status . "draft")

    ;; ========================================
    ;; LINEARITY
    ;; ========================================
    (linearity
      . ((definition
           . "A value is linear if it must be used exactly once during program execution.")
         (annotations
           . ((linear . "Value must be consumed exactly once")
              (unrestricted . "Value may be used zero or more times")))
         (linear-types
           . ("String@r" "Functions consuming linear args" "Products with linear components"
              "Sums with linear variants" "Region-scoped allocations"))
         (unrestricted-types
           . ("()" "Bool" "I32" "I64" "F32" "F64" "&T"))
         (consumption
           . ((variable-use . "Using a linear variable consumes it")
              (function-application . "Passing to a function consumes the argument")
              (pattern-match . "Matching destructures and consumes the value")
              (explicit-drop . "drop(e) explicitly consumes the value")))
         (invariants
           . ("Linear values cannot be used after consumption."
              "Linear values cannot be duplicated without explicit copy."
              "All linear bindings must be consumed by scope exit."))))

    ;; ========================================
    ;; REGION SCOPES
    ;; ========================================
    (regions
      . ((definition
           . "A region is a lexically scoped memory arena. Allocations within a region are bulk-freed on region exit.")
         (syntax . "region r { e }")
         (semantics
           . ((entry . "Push current bump pointer to region stack; introduce region name r")
              (allocation . "String.new@r(...) allocates in region r using bump allocation")
              (exit . "Pop bump pointer from stack, restoring previous allocation point; all allocations freed")))
         (type-rule
           . "region r { e } : T requires that T does not mention r (no escaping references)")
         (invariants
           . ("Allocations in region r cannot outlive the region scope."
              "Type checker rejects any attempt to return a region-scoped value."
              "Regions cannot be first-class values; they are purely lexical."))))

    ;; ========================================
    ;; SECOND-CLASS BORROWS
    ;; ========================================
    (borrows
      . ((definition
           . "A borrow &e provides temporary read-only access to a value without transferring ownership.")
         (syntax . "&e")
         (type . "&T")
         (second-class-restrictions
           . ("Cannot be stored in data structures (pairs, sums)."
              "Cannot be returned from functions."
              "Cannot escape the lexical scope where created."
              "Cannot be assigned to let bindings that outlive the borrowed expression."))
         (typing
           . "R; Γ ⊢ &x : &T ⊣ Γ  (borrow does not consume x)")
         (use-cases
           . ("String.len(&s) -- read length without consuming string"
              "Comparison functions -- compare without consuming"
              "Inspection operations -- examine without ownership transfer"))
         (invariants
           . ("Original value remains linear and must still be consumed elsewhere."
              "Borrow lifetime is strictly nested within original value's lifetime."))))

    ;; ========================================
    ;; EXPLICIT COPY RULES
    ;; ========================================
    (explicit-copy
      . ((definition
           . "Duplication of values requires explicit syntax; there is no implicit copying.")
         (syntax . "copy(e)")
         (applicability
           . "Only unrestricted types may be copied: (), Bool, I32, I64, F32, F64")
         (linear-types
           . "Linear types cannot be copied. Attempting copy(linear_val) is a type error.")
         (semantics
           . "copy(e) evaluates e and produces a fresh copy of the value, leaving original unconsumed.")
         (rationale
           . ("Prevents accidental duplication of resources."
              "Makes resource flow explicit in source code."
              "Aligns with linear logic where contraction (copying) is controlled."))
         (invariants
           . ("copy(e) where e : T requires unrestricted(T)."
              "The original value and the copy are independent."))))

    ;; ========================================
    ;; TYPING JUDGEMENT
    ;; ========================================
    (typing-judgement
      . ((form . "R; Γ ⊢ e : T ⊣ Γ'")
         (components
           . ((R . "Set of active region names")
              (Γ . "Input typing context: list of (x : T, used) triples")
              (e . "Expression being typed")
              (T . "Resulting type")
              (Γ' . "Output context with updated usage information")))
         (context-operations
           . ((lookup . "Γ(x) = T retrieves binding for x")
              (mark-used . "Γ[x ↦ used] marks x as consumed")
              (extend . "Γ, x : T adds fresh binding")
              (all-used . "∀(x : T, used) ∈ Γ. used = true (all linear vars consumed)")))))

    ;; ========================================
    ;; KEY TYPING RULES
    ;; ========================================
    (typing-rules
      . ((T-Var-Lin
           . ((premises . ("Γ(x) = T" "linear(T)" "¬used(Γ, x)"))
              (conclusion . "R; Γ ⊢ x : T ⊣ Γ[x ↦ used]")
              (description . "Using a linear variable consumes it")))

         (T-Var-Un
           . ((premises . ("Γ(x) = T" "unrestricted(T)"))
              (conclusion . "R; Γ ⊢ x : T ⊣ Γ")
              (description . "Unrestricted variables can be used without consumption")))

         (T-StringNew
           . ((premises . ("r ∈ R"))
              (conclusion . "R; Γ ⊢ String.new@r(s) : String@r ⊣ Γ")
              (description . "Allocate string in active region")))

         (T-StringConcat
           . ((premises . ("R; Γ ⊢ e1 : String@r ⊣ Γ'"
                           "R; Γ' ⊢ e2 : String@r ⊣ Γ''"))
              (conclusion . "R; Γ ⊢ String.concat(e1, e2) : String@r ⊣ Γ''")
              (description . "Concatenation consumes both input strings")))

         (T-Region
           . ((premises . ("r ∉ R"
                           "R ∪ {r}; Γ ⊢ e : T ⊣ Γ'"
                           "T does not mention r"))
              (conclusion . "R; Γ ⊢ region r { e } : T ⊣ Γ'")
              (description . "Region introduces fresh scope; result cannot reference region")))

         (T-Borrow
           . ((premises . ("Γ(x) = T"))
              (conclusion . "R; Γ ⊢ &x : &T ⊣ Γ")
              (description . "Borrow does not consume the value")))

         (T-Drop
           . ((premises . ("R; Γ ⊢ e : T ⊣ Γ'" "linear(T)"))
              (conclusion . "R; Γ ⊢ drop(e) : () ⊣ Γ'")
              (description . "Explicit drop consumes linear value")))

         (T-Copy
           . ((premises . ("R; Γ ⊢ e : T ⊣ Γ'" "unrestricted(T)"))
              (conclusion . "R; Γ ⊢ copy(e) : T ⊣ Γ'")
              (description . "Copy produces duplicate of unrestricted value")))))

    ;; ========================================
    ;; MEMORY SAFETY THEOREMS
    ;; ========================================
    (safety-theorems
      . ((progress
           . "If R; Γ ⊢ e : T ⊣ Γ' and e is not a value, then e can step.")
         (preservation
           . "If R; Γ ⊢ e : T ⊣ Γ' and e → e', then R; Γ'' ⊢ e' : T ⊣ Γ' for some Γ''.")
         (linearity-soundness
           . "If R; Γ ⊢ e : T ⊣ Γ' and e →* v, all linear bindings in Γ are consumed.")
         (no-use-after-free
           . "Linear types ensure resources cannot be accessed after consumption.")
         (no-double-free
           . "Linear types ensure resources are consumed at most once.")
         (no-leaks
           . "Linear types ensure resources are consumed at least once.")
         (no-region-escape
           . "Region-scoped types cannot outlive their region.")))

    ;; ========================================
    ;; WASM TARGET
    ;; ========================================
    (wasm-compilation
      . ((target . "wasm32-unknown-unknown")
         (memory-model
           . ((bump-pointer . "0x0000 (4 bytes)")
              (region-stack-pointer . "0x0004 (4 bytes)")
              (region-stack . "0x0008 (256 bytes, 64 levels max)")
              (heap-start . "0x0108")))
         (type-mapping
           . (("()" . "no value")
              ("Bool" . "i32 (0 or 1)")
              ("I32" . "i32")
              ("I64" . "i64")
              ("F32" . "f32")
              ("F64" . "f64")
              ("String@r" . "i32 (pointer)")
              ("(T1, T2)" . "i32 (pointer to struct)")
              ("T1 + T2" . "i32 (pointer to tagged union)")))))))
