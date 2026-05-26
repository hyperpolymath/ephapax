<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell -->

# Preservation: principled redesign

Companion to `PRESERVATION-HANDOFF.md`. The handoff document is a
diagnostic record of attempted proof-engineering. This document is the
**design** rationale for the typing-layer change that the verified
counterexample (`Counterexample.v`, all three lemmas `Qed.`) now makes
unavoidable.

The handoff's Option 3 ("type-system change") is here re-cast not as a
patch but as the deliberate separation of four concerns that the
current calculus conflates: **structural discipline**,
**region capability tracking**, **dyadic interaction semantics**, and
**echo / residue semantics**. Preservation is derived from explicit
invariants in the new architecture; it is not forced through the old.

---

## 1. What the counterexample proves

`formal/Counterexample.v` exhibits a configuration where the calculus
admits a single-step reduction whose result is *untypable* at the same
outer type — i.e. preservation as stated is **false**, not unproven.

| Input | Type at `R_in = [r0; r1]` |
|---|---|
| `EPair (ERegion r1 (ELoc l0 r0)) (ELoc l1 r1)` | `TProd (TString r0) (TString r1)` |

After one `S_Pair_Step1` (lifting `S_Region_Exit` on the first child):

| Output | Type at `R' = [r0]` |
|---|---|
| `EPair (ELoc l0 r0) (ELoc l1 r1)` | **none** (sibling `ELoc l1 r1` requires `In r1 [r0]`, false) |

### The missing invariant, named

The sibling `ELoc l1 r1` was typed under the assumption that `r1`
would be live. The first child *invalidated that assumption* by
exiting `r1` mid-evaluation. The typing judgment has no place to
record that the input region environment for the second sibling
depends on the output region environment of the first.

> **Missing invariant — region capability monotonicity per
> sub-expression**: for any compound form `C(e₁, …, eₙ)`, the
> capability environment in which `e_{i+1}` is typed equals the
> capability environment *left over* after `e_i` evaluates.

The current rules thread the *linearity* context `G` left-to-right
through compound rules, but the *region* environment `R` is shared
statically by all siblings. That asymmetry is the bug.

---

## 2. Why a side-condition patch is wrong

The handoff lists three minimal-patch candidates: mutual induction,
inversion-on-`Hstep` structural recursion (~150 LOC helper), or an
ad-hoc sibling-region-disjointness side condition on `T_Pair`, `T_Let`,
`T_App`, ….

All three preserve the architectural defect (R as a static, sibling-
shared parameter) and force the proof through it. The disjointness
side condition is the worst of the three because it scatters the
invariant across every compound rule, making future rules (Echo Types,
effect/capability extensions, dyadic interaction primitives) responsible
for re-discovering and re-imposing the same constraint at every
introduction.

The principled fix is to thread R the same way G is threaded. The
sibling-region-disjointness *property* then **follows as a corollary**
of the new threading; it is no longer a rule premise.

---

## 3. The four orthogonal concerns

The redesign separates four discipline layers that the current calculus
braids together:

| Layer | Concern | What it tracks | Encoded as |
|---|---|---|---|
| **L1** | Region capabilities | Which regions are currently live; how they shrink under reduction | Input/output capability sets `R_in → R_out` threaded through every rule |
| **L2** | Structural discipline | Whether linear bindings must be consumed (Linear) or may be implicitly dropped (Affine) | Modality parameter `ℓ ∈ {Linear, Affine}` on the judgment + a thin-poset weakening `Linear ⇒ Affine` |
| **L3** | Echo / residue | Whether irreversible operations (region exit, drop) produce a residue witness that must (Linear-echo) or may (Affine-echo) be observed | Echo types `Echo f y := Σ A (λ x → f x ≡ y)` ([echo-types/Echo.agda:14](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/Echo.agda#L14)); residue obligation tracked by a third thin-poset decoration |
| **L4** | Dyadic interaction | The mother–child pairing of the language: ephapax-linear vs ephapax-affine as observable interaction modes | Top-level mode declaration; consequences cascade into L2 and L3 defaults |

The key claim — borrowed verbatim from the echo-types calculus
(`EchoLinear.agda:30-101`) — is that **decoration commuting** holds:
because each layer's order is a thin poset (subset on `R`, the
two-point modality `Linear ≤ Affine`, the residue refinement
`mandatory ≤ optional`), composition of layers is definitional. No
coherence burden is introduced; the layers do not have to "agree" on
anything beyond their independent invariants.

This is the architectural payoff: **adding L3 later does not require
reproving anything about L1 and L2.**

---

## 4. Layer 1 in detail — the preservation fix

### 4.1 Judgment signature

Current:

```
R ; G  ⊢  e : T  -|  G'
```

New:

```
R ; G  ⊢  e : T  -|  R' ; G'
```

`R'` is the capability environment **after** `e` has reduced to a
value. It is determined syntactically from `e` (see §4.3); the change
is syntax-directed, not inferential.

### 4.2 Compound rules thread `R` left-to-right

Every compound rule that currently threads `G` left-to-right gains the
corresponding `R` threading. Example, `T_Pair`:

```coq
| T_Pair : forall R R' R'' G G' G'' e1 e2 T1 T2,
    R  ; G  ⊢ e1 : T1 -| R'  ; G'  ->
    R' ; G' ⊢ e2 : T2 -| R'' ; G'' ->
    R  ; G  ⊢ EPair e1 e2 : TProd T1 T2 -| R'' ; G''
```

Same shape change for `T_Let`, `T_LetLin`, `T_App`, `T_StringConcat`,
`T_If`, `T_Case` (with branches required to *agree* on `R_out`),
`T_Fst`, `T_Snd`, `T_Inl`, `T_Inr`, `T_Drop`, `T_Copy`, `T_Borrow_Val`.

### 4.3 Region rules expose the capability shift

`T_Loc` and value rules: `R_out = R_in` (values don't affect
capabilities).

`T_Region` (fresh region introduction; `~ In r R_in`):

```coq
| T_Region : forall R R_body G G' r e T,
    ~ In r R ->
    ~ In r (free_regions T) ->
    (r :: R) ; G ⊢ e : T -| R_body ; G' ->
    R ; G ⊢ ERegion r e : T -| remove_first r R_body ; G'
```

`T_Region_Active` (re-entering an already-live region; `In r R_in`):

```coq
| T_Region_Active : forall R G G' r e T,
    In r R ->
    ~ In r (free_regions T) ->
    R ; G ⊢ e : T -| R ; G' ->                    (* body must NOT exit r *)
    R ; G ⊢ ERegion r e : T -| remove_first r R ; G'
```

The two regional rules now make the capability cost of the construct
**explicit** at the typing level. `S_Region_Exit`'s operational effect
(shrink `R` by one `r`) is mirrored by the typing rule's `R_out`.

### 4.4 The counterexample no longer types

Under the new rules:

- `ERegion r1 (ELoc l0 r0)` typed at `R_in = [r0; r1]`:
  by `T_Region_Active` with `In r1 [r0; r1]` ✓ and
  `~ In r1 (free_regions (TString r0)) = ~ In r1 [r0]` ✓.
  Body `ELoc l0 r0`: `R_in = [r0; r1]`, `R_out = [r0; r1]`.
  Outer `R_out = remove_first r1 [r0; r1] = [r0]`.

- Now `EPair`'s second sibling `ELoc l1 r1` must type at
  `R = [r0]`. `T_Loc` requires `region_active [r0] r1`, false.

- **The `EPair` rule has no derivation.** Counterexample disappears.

### 4.5 Preservation under the new judgment

The original goal —

> If `R; G ⊢ e : T -| G'` and `(μ, R, e) → (μ', R', e')` then
> `R'; G ⊢ e' : T -| G'`.

— now becomes:

> If `R; G ⊢ e : T -| R_final; G'` and `(μ, R, e) → (μ', R', e')` then
> there exists `R'_final` such that `R'; G ⊢ e' : T -| R'_final; G'` and
> `R'_final` is consistent with `R_final` (specifically: `R_final` is
> reachable from `R'_final` by zero or more applications of the
> remaining region exits in `e'`).

The 11 admits on the `touches_region` RIGHT branch dissolve: each
admit was asking "how do I re-type the unchanged sibling under the
shrunken R'?". Under the new threading the sibling is typed at
`R'` from the outset — there is nothing to re-type.

### 4.6 Cost: which existing lemmas need re-proof

The judgment shape changes, so every lemma that pattern-matches the
old shape (`R; G |- e : T -| G'`) must be updated. The lemma count
in the current `Semantics.v` is ~80; most are mechanical signature
updates. The **substance** of each proof is unchanged because the
new R-threading is just a parallel copy of the existing G-threading.

A targeted estimate (the user explicitly de-prioritises patch size,
so this is informational only):

| Lemma class | Count (approx) | Substance change |
|---|---:|---|
| `value_context_unchanged` and variants | ~6 | none — values: `R_out = R_in` |
| `subst_preserves_typing`, `_strong` | 2 | thread `R` like `G` |
| `region_shrink_preserves_typing`, `_dup` | 2 | restated; some may become redundant |
| `region_add_typing`, `region_env_perm_typing` | 2 | restated |
| `step_R_eq_or_touches_region`, `step_R_change_shape` | 2 | possibly subsumed by the new judgment |
| `step_preserves_type`, `step_output_context_eq` and at-pre helpers | 4 | restate `step_output_context_eq` to relate `R_final` and `R'_final`; `step_preserves_type` proves the new preservation statement directly |
| `preservation` | 1 | proved by structural induction on the new judgment |

The at-pre helper pattern survives because it is orthogonal to the
threading change: the pre-step env is the new `R_in` of the
diagonal typing rule.

---

## 5. Layer 2 in detail — Linear vs Affine modality

Currently `is_linear_ty` and `T_Drop`/`T_Copy` encode a per-*type*
distinction (a `TRef Lin` is linear, a `TRef Unr` is not). The user
clarified that there is a stronger, **language-level** dyadicity:

- **Ephapax-Linear**: strict exact-consumption semantics. Weakening
  forbidden. Drop must be explicit and consumes the value. Every
  irreversible operation must produce an observed residue.
- **Ephapax-Affine**: permits implicit drop. Weakening allowed.
  Irreversible operations may silently produce a non-duplicable
  residue trace.

Encode the modality as a judgment parameter:

```
R ; G  ⊢_ℓ  e : T  -|  R' ; G'        where ℓ ∈ {Linear, Affine}
```

The modality lives on the **judgment**, not on the type. The two
sublanguages share the same syntax (`Syntax.v` unchanged) and the
same operational semantics (`Semantics.v` unchanged); they differ in
which derivations the typing relation admits.

### Linear ⇒ Affine: a thin-poset decoration

Every Linear derivation is an Affine derivation (Linear is the more
restrictive mode). This is the modality weakening:

```coq
weaken_modality : forall R G e T R' G',
    R ; G ⊢_Linear e : T -| R' ; G' ->
    R ; G ⊢_Affine e : T -| R' ; G'
```

This mirrors `EchoLinear.agda:53-58` (`weaken : LEcho linear → LEcho
affine`). Because `Linear ≤ Affine` is propositional, the weakening
commutes with R-threading and G-threading by the decoration-commuting
recipe (echo-types' `degradeMode-comp`, `EchoLinear.agda:93-101`).

### What changes per mode

| Rule | Linear | Affine |
|---|---|---|
| `T_Lam` | `(T1, true) :: G` on body output | `(T1, true_or_unused) :: G` |
| Top-level (closed terms) | `G = G' = []` required | `G = []`, `G'` may carry unused linear bindings |
| `T_Drop` | discharges an *obligation* to consume; required for unused linear bindings | optional; produces an Affine-echo residue (see §6) |
| Branches in `T_Case`, `T_If` | must agree on `(R', G')` exactly | may differ; meet operation on outputs (also a thin-poset operation) |

`T_Region`, `T_Region_Active`, `T_Loc`, `T_StringNew`,
`T_StringConcat`, `T_Pair`, `T_App`, etc. are **modality-polymorphic**
— the rule shape is identical in both modes.

### Proof obligations specific to each mode

| Property | Ephapax-Linear | Ephapax-Affine |
|---|---|---|
| Preservation | ✓ (L1 fix) | ✓ (same fix; Affine derivations are L1-safe by weakening) |
| Progress | ✓ | ✓ |
| **No-leak** (every introduced linear value is consumed) | proved | does **not** hold; replaced by "no-duplicate" |
| **No-duplicate** | trivially (Linear ⇒ no-duplicate) | proved as a structural property |
| **Resource-exact** (linear count = linear introductions) | proved | not stated |
| **Garbage residue inhabited** | not applicable | proved (every silent drop has a residue trace) |

Cross-mode: the Linear ⇒ Affine weakening lemma is a single induction.
Combined with monomode preservation, this gives Affine preservation
for free.

---

## 6. Layer 3 — Echo / residue, in design

This layer is **not required for preservation**. Documented here so
that L1 + L2 don't bake in assumptions that block L3 later.

### 6.1 Echo, the fiber

Echo-types defines:

```agda
Echo : (A → B) → B → Set
Echo f y = Σ A (λ x → f x ≡ y)
```

An echo of `y` under `f` is a witnessed preimage — proof-relevant
because *which* `x` mapped to `y` is information the irreversibility
of `f` deliberately erased. (`Echo.agda:14-15`.)

For ephapax, the irreversible operations are:

| Operation | Collapse | Echo type |
|---|---|---|
| `S_Region_Exit` of `r` | `collapse_region_r : LiveAt_r → ExitedAt_r` | `Echo collapse_region_r exited` — witnessed by which value escaped |
| `S_Drop` of `v : T` | `collapse_drop : T → ⊤` | `Echo collapse_drop tt` — full fiber on `T` |
| Implicit drop (Affine only) | as above, but residue is `EchoR` (lowered) | `EchoR ⊤ TrivialCert tt` |

### 6.2 Two modes, one type former

Following `EchoLinear.agda:30-58`:

```
LEcho : Mode → Set
LEcho Linear = Echo collapse tt          -- full fiber, mandatory observation
LEcho Affine = EchoR ⊤ TrivialCert tt    -- lowered residue, optional
```

**Linear echo is not a different type from affine echo.** It is the
same fiber, with a different observation discipline imposed by the
modality layer. The weakening `weaken : LEcho Linear → LEcho Affine`
*is* the echo-lowering map (`EchoResidue.agda:33-73`). This is what
the user means by "echo semantics and structural discipline must
remain orthogonal and compositional": L2 chooses the mode; L3 is the
same fiber regardless.

### 6.3 Where echo enters the typing rules

The L3 extension introduces:

- A new type former `TEcho (op : irreversible_op) : ty`.
- An operational rule pairing: `S_Region_Exit` and `S_Drop` produce a
  residue **value** of type `TEcho ⟨op⟩`. In Linear mode this value
  must be threaded into a `T_Observe` somewhere; in Affine mode it may
  be implicitly dropped (which itself produces a `TEcho ⟨affine-
  drop⟩`, but that is observed automatically by the runtime).
- The bookkeeping is hierarchical-via-fibration; no coherence
  obligations arise because each level is a thin poset (decoration
  commuting holds — `EchoLinear.agda:93-101`).

### 6.4 What L3 demands that L1+L2 must not contradict

To keep L3 viable as a future extension, the L1 and L2 design must:

1. **Not bake "irreversible step ⇒ no residue" into preservation.**
   The current `S_Region_Exit` has `expr_free_of_region r v` as a
   premise but no residue value. The L3 extension *adds* the residue
   value. Preservation as restated in §4.5 must not assume residue =
   nothing.
2. **Not introduce per-type "echo-ability" predicates.** Echo is a
   property of operations, not of types. Echo-types' canonical
   formulation (fiber-of-a-collapse) keeps the type former minimal.
3. **Not assume mode-monomorphic typing rules.** The L1/L2 rules are
   modality-polymorphic; L3's `T_Observe` is the one rule that splits
   per mode (Linear-`T_Observe` consumes; Affine-`T_Observe` doesn't).

§4 and §5 as drafted satisfy all three.

---

## 7. Layer 4 — Dyadic interaction (the mother–child distinction)

The user's note —

> Linear Ephapax is the exact-consumption / obligation-preserving
> regime and is the true home of strict dyadic semantics. Affine
> Ephapax permits weakening and graceful abandonment, so its
> dyadicity is relaxed/degradable rather than fully obligation-
> symmetric.

— frames Linear and Affine ephapax not as "strict vs lax" but as the
**asymmetric pair** of a dyadic interaction: Linear is the obligation-
bearer (the *speaker* of the dyad), Affine is the obligation-relaxer
(the *listener*). Both must coexist because real programs require both
sides of the interaction.

This dyadicity is itself orthogonal to L1, L2, L3:

- L1 (region capabilities) is the *same* in both Linear and Affine —
  both must track region exit precisely for soundness.
- L2 (modality) gives the *direction* of the dyad — which side is
  obligation-bearing.
- L3 (echo) is the *protocol* of obligation discharge — what the
  observer must do with the residue.

L4 is **not a separate proof layer**. It is a labelling discipline at
the program / module level: a closed program is declared
ephapax-Linear or ephapax-Affine (or a designated module-boundary mix);
the corresponding judgment-mode (L2) is selected, and L3 follows from
that. No proofs change.

---

## 8. Proof-need separation: Linear vs Affine

Where the layers' proof needs differ:

| Property | Ephapax-Linear | Ephapax-Affine |
|---|---|---|
| **Preservation** (L1) | identical statement; proof via L1 threading | identical statement; follows from Linear via modality-weakening |
| **Progress** | values + closed contexts step | values + closed contexts step; affine "ambient drop" rule may fire |
| **Resource exactness** | `count_intro = count_consume` for linear-typed values | replaced by `count_consume ≤ count_intro` |
| **Sound region exit** (L1 corollary) | no derivation types a sibling reference to an exited region | same |
| **No-leak / leak-bounded** | no-leak strictly | leak-bounded (residue accumulated as Affine-echo) |
| **No-duplicate** | trivial corollary | structural induction on absence of `T_Copy` for linear types |
| **Echo observation closure** (L3) | every irreversible step's residue is observed by program end | every residue is observed-or-dropped; non-duplication holds |
| **Mode coherence** (L4) | a Linear program does not invoke Affine-mode rules | an Affine program may call Linear-typed functions via mode embedding |

The two sublanguages share **preservation and progress**. They differ
on resource counting and on echo observation. L3 is where the proof
needs genuinely split.

---

## 9. Counterexample examination, revisited

The verified counterexample (`Counterexample.v`) was a *single*
witness. The L1 architectural fix subsumes a family of related
configurations, all sharing the same shape. Cataloguing them
sharpens the design:

| Family | Generator | Variant of counterexample |
|---|---|---|
| **F1 — sibling re-references exited region** | `EPair (ERegion r v) (e[r])` with `r ∈ free_regions(type(e[r]))` | the proved counterexample |
| **F2 — let-body references exited region** | `ELet (ERegion r v) (e[r])` where the bound variable is unused but `r` appears | same shape via `T_Let` |
| **F3 — function-application sibling** | `EApp (ERegion r f) (ELoc _ r)` | `T_App`, same shape |
| **F4 — string-concat sibling** | `EStringConcat (ERegion r e1) (ELoc _ r)` | `T_StringConcat`, blocked by L1 because both children must type at the *same* `TString r`; second child is `ELoc _ r` requiring `r ∈ R_mid` |
| **F5 — case-branch references exited region** | `ECase (ERegion r e) (ELoc _ r) (ELoc _ r)` — both branches reference `r` | `T_Case`, blocked by L1 because branches must agree on `R_out`, and the scrutinee's `R_out` no longer contains `r` |
| **F6 — nested same-name region** | `ERegion r (EPair (ERegion r v) (ELoc _ r))` | distinguishes `T_Region` from `T_Region_Active`; under L1 both exits pop one `r` and the inner sibling is typed at the right shrunken `R` |

All six families derive from the same defect: sibling typings under a
sibling-shared `R`. L1's threading eliminates the entire family in one
structural change.

A family L1 does **not** address: sibling reference to a region
*introduced* (not exited) by a sibling — e.g.,
`EPair (ERegion r v) (ELoc _ r)` where the second sibling expects `r`
to be active. This is already disallowed by `T_Region`'s
`~ In r R` premise (the fresh `r` is local to the body, not visible
to the sibling). Verified separately that the second sibling would
require `r ∈ R_in`, but `r ∉ R_in` by `T_Region`'s premise — so this
is well-typedness, not preservation, and the existing rules already
reject it.

This confirms the diagnosis: **the asymmetry is region *exit*, not
region introduction**. L1's left-to-right threading is the exactly-
sufficient mechanism.

---

## 10. Implementation order

1. **L1 — region threading** (this design). Closes preservation.
   Days, not weeks. The hard part is re-stating ~80 lemmas; the
   substance of each is unchanged.
2. **L2 — modality parameter** (already present *in* the types via
   `is_linear_ty`; needs to be *promoted* to a judgment parameter
   plus the Linear ⇒ Affine weakening). Orthogonal to L1; can be
   done before or after.
3. **L3 — echo type former** (forward-looking; not required for
   preservation, progress, or the dyadic story). Bring in
   echo-types' `Echo`, `EchoR`, and `EchoLinear` mode poset
   verbatim; layer them via decoration-commuting.
4. **L4 — module-level mode declaration** (UX, not proof).

Each step's correctness is independent of the next. The decoration-
commuting recipe from echo-types (`composition.md` §Q5) guarantees
that adding L3 to a system that already has L1+L2 does not invalidate
any L1/L2 proof.

---

## 11. References

- The verified counterexample: `formal/Counterexample.v` (this repo).
- The diagnostic record of attempted patches: `formal/PRESERVATION-HANDOFF.md`.
- Echo definition: `~/developer/repos/echo-types/proofs/agda/Echo.agda` (line 14).
- Echo residue + non-recovery: `~/developer/repos/echo-types/proofs/agda/EchoResidue.agda` (lines 16–66).
- Linear/Affine mode poset: `~/developer/repos/echo-types/proofs/agda/EchoLinear.agda` (lines 30–101).
- Decoration commuting / orthogonality recipe: `~/developer/repos/echo-types/proofs/agda/EchoGraded.agda` (lines 73–86, 141–158) and `~/developer/repos/echo-types/docs/echo-types/composition.md` (§Q5).
- Disambiguation: `CLAUDE.md` (this repo) for ephapax-vs-AffineScript boundary; ephapax-linear and ephapax-affine are *internal sublanguages* of one project, not separate projects.

---

## 12. Documentation rollout — making the revised story legible

The L1–L4 redesign changes how Ephapax *is described*, not just how it
is implemented. The current documentation talks about "linear+affine
type system" as if the dyad were the whole story; under the new
architecture it is **one of four orthogonal layers**, and the more
interesting story is the layering itself. This section catalogues the
documents that frame "what ephapax is" and specifies the substantive
edits required, with draft text where the framing matters.

The rollout deliberately leaves implementation untouched. Documentation
that promises the new architecture without it being built would be
dishonest; documentation that describes the **direction** alongside
the current state is a roadmap. The text below is the roadmap form.

### 12.1 Tagline and one-line description (used by many surfaces)

The current GitHub repo description is:

> Dyadic linear+affine type system for compile-time WASM memory safety
> — no use-after-free, no leaks, region-based allocation. Mechanically
> proved in Coq and Idris2.

Proposed replacement (matches the four-layer story without overclaiming
unbuilt layers):

> A dyadic programming language for WebAssembly, where four orthogonal
> disciplines — structural (linear ↔ affine), region capabilities,
> irreversibility residue, and dyadic interaction mode — compose to
> guarantee compile-time memory safety without a garbage collector.
> Mechanically formalised in Coq and Idris2.

Short form (≤ 130 chars, for cards and `site:` listings):

> Ephapax: four-layer dyadic type system for WASM memory safety —
> linearity, regions, echo residue, dyadic mode. Coq + Idris2 proofs.

Lift this string verbatim into:

- GitHub repo description (`gh repo edit hyperpolymath/ephapax --description …`).
- `site/index.md` hero subtitle.
- `.well-known/funding.json` / any project-listing metadata.
- The Pages site `_config` (if any) and the GH wiki landing page.

### 12.2 README.adoc — repo front door

`README.adoc` (lines 43–96) is currently structured as "what this is
(table)" + "what this isn't" + "Hello, world". The table maps closely
onto L1–L4 once the framing is named. **Targeted edits, not a
rewrite:**

1. **Add a new section after `== What this is`** titled
   `== The four layers`, listing L1–L4 in the same `[cols="1,3"]` table
   style:

   ```adoc
   == The four layers

   Ephapax composes four orthogonal disciplines. Each is a thin-poset
   refinement, so they compose without coherence obligations
   (https://github.com/hyperpolymath/echo-types[echo-types] supplies
   the recipe).

   [cols="1,3"]
   |===
   | Layer | What it enforces

   | **L1 — Region capabilities**
   | Every live region is tracked in an input/output environment
     threaded through every expression. A region cannot be referenced
     after a sibling has exited it. Soundness proof in `formal/`.

   | **L2 — Structural discipline (linear ↔ affine)**
   | The *modality* of the surrounding program decides whether linear
     bindings must be consumed (Linear: ephapax-linear) or may be
     dropped (Affine: ephapax-affine). Same syntax, same semantics —
     different admissible derivations. Linear ⊆ Affine.

   | **L3 — Irreversibility residue (Echo)**
   | Operations that erase information (region exit, drop) produce
     proof-relevant residue — `Echo f y := Σ A (λ x → f x ≡ y)`. In
     Linear mode the residue must be observed; in Affine mode it
     may be silently lowered. Forward-looking; not yet in the typing
     rules.

   | **L4 — Dyadic interaction mode**
   | A project-level declaration of which side of the dyad the
     program speaks from. Selects the L2 modality and the L3
     observation discipline. No proof obligations of its own.
   |===
   ```

2. **Update the "Dyadic discipline" row of the existing table** to
   cross-reference the new section:

   > **Dyadic discipline** | This is **L2** (see "The four layers"
   > below). Each binding is *either* affine (`let` — used at most
   > once, weakening allowed) *or* linear (`let!` — used exactly once,
   > weakening forbidden). Type checker enforces.

3. **Replace "Region-based memory" row** with the L1 framing:

   > **Region-based memory (L1)** | Allocations live in named regions
   > (`region r: ...`). The type system threads a region-capability
   > environment through every expression so a sibling cannot read
   > from a region another sibling has just exited. When a region's
   > scope ends, the runtime bulk-frees every resource in it.

4. **Add a footnote-style block** linking to this design document
   for readers who want the soundness story:

   ```adoc
   .Soundness story
   ****
   The four-layer separation is **not** decorative — it exists
   because the original "linear+affine + regions" framing admitted a
   verified counterexample to preservation (see
   `formal/Counterexample.v` and `formal/PRESERVATION-DESIGN.md`).
   The four-layer redesign restores soundness by making each
   discipline's invariants explicit and orthogonal.
   ****
   ```

5. **Do not** change the disambiguation block (lines 19–41). It is
   correct and load-bearing.

### 12.3 EXPLAINME.adoc — receipts

`EXPLAINME.adoc` is the "show me the evidence" companion to the
README. Today it backs up the dyadic + two-AST + pattern-matching +
dual-grammar + region claims. Under the new architecture it must
back up two new claims and weaken one:

- **New (L1)**: "The region capability environment is threaded
  through every compound expression." Evidence pointer: cite
  `formal/PRESERVATION-DESIGN.md §4` and `formal/Counterexample.v`
  (until the Coq side is implemented, the evidence is the **design
  doc + counterexample**, not a passing proof — say so honestly).
- **New (L3, planned)**: "Irreversible operations produce residue
  witnesses." Evidence pointer: `formal/PRESERVATION-DESIGN.md §6`
  and the upstream echo-types proofs at
  `~/developer/repos/echo-types/proofs/agda/EchoLinear.agda`. Mark as
  **planned** until ephapax has its own `formal/Echo.v`.
- **Weaken**: the existing "Dyadic Type System" claim should now
  point to `EPHAPAX-VISION.adoc` and to the L2 description in the
  README, rather than presenting L2 in isolation.

Add a new top-level section after "Claim: Region-Based Memory":

```adoc
== Claim: Sibling-safe region capabilities (L1)

*Evidence*: Region capabilities are threaded as input/output
environments through every compound typing rule. A sibling cannot
reference a region a previous sibling has exited.

* Counterexample at `formal/Counterexample.v` (all three lemmas
  `Qed`) demonstrates the soundness gap the threading fixes.
* Design rationale at `formal/PRESERVATION-DESIGN.md §3-§4`.
* Reference implementation: forthcoming — see `ROADMAP.adoc` for
  the order in which L1 lands in `formal/` and in
  `src/ephapax-typing/`.

== Claim: Irreversibility residue is first-class (L3, planned)

*Evidence (planned)*: Operations that erase information will produce
typed residue witnesses, following the
https://github.com/hyperpolymath/echo-types[echo-types]
formulation. Linear mode requires the residue to be observed;
Affine mode permits silent lowering.

* Upstream theory at
  `~/developer/repos/echo-types/proofs/agda/EchoLinear.agda` (lines
  30–101), already mechanised.
* Forward-looking design at `formal/PRESERVATION-DESIGN.md §6`.
* Status: **planned** — no ephapax rule yet introduces `TEcho`. The
  L3 extension follows L1.
```

### 12.4 docs/vision/EPHAPAX-VISION.adoc — the design vision

The vision doc already articulates the dyad beautifully (mother /
child, "ephapax means once for all" double-meaning, "Linear ⊂ Affine
in valid programs", "one language, one feel"). The four-layer story
*extends* this; it does not replace it.

**Insert a new section between the existing `== The Dyad` and
`== One Language, One Feel`**:

```adoc
== The Dyad and the Layers

The dyad — linear mother, affine child — is one of *four orthogonal
disciplines* that together define Ephapax. The other three are
silent partners in the dyad: each is enforced independently, but
each takes its **defaults** from which side of the dyad you are on.

[cols="1,3", options="header"]
|===
| Layer | What the dyad says about it

| L1 — Region capabilities
| Same in both. The mother and the child both forbid use-after-exit;
  the dyadic mode does not relax this. (This is the layer whose
  *absence* admitted the verified counterexample to preservation.)

| L2 — Structural discipline
| The dyad *is* this layer. Linear is the mother; Affine is the
  child. Linear derivations are a subset of Affine derivations.

| L3 — Irreversibility residue
| The mother demands the residue be *observed*. The child permits
  it to be *lowered* — present but trivial. The same residue value,
  two observation disciplines.

| L4 — Dyadic interaction
| The declaration of which side you speak from. The mother answers
  to the linear discipline; the child to the affine. Every closed
  program has one.
|===

The four layers compose without coherence obligations because each
is a *thin poset* — propositional ordering kills the categorical
overhead that would otherwise demand pentagon laws and the like. The
construction is taken verbatim from
https://github.com/hyperpolymath/echo-types[echo-types]'
decoration-commuting recipe.

The dyad remains primary. The layers are how the dyad's promises
are *enforced*.
```

The existing prose ("one mother, one child, one dyad", "the child is
not deficient", "as Ephapax matures, the affine form must mature into
itself") is unchanged. The layer story extends it; it doesn't replace
it.

### 12.5 ROADMAP.adoc — sequencing

The current ROADMAP carries the **preservation closure plan** at the
top. The redesign supersedes that plan. New top section:

```adoc
== Four-layer redesign (2026-05-26 → )

The verified preservation counterexample
(`formal/Counterexample.v`) closed the original closure plan as
unreachable in the current rules. The new plan separates four
orthogonal layers; each is implemented in sequence.

. **L1 — Region capability threading**
  - Restate `has_type` to thread `R_in / R_out`.
  - Update every typing rule + every supporting lemma in
    `Semantics.v`, `Typing.v`.
  - Reprove preservation against `Counterexample.v` as a regression.
  - Land as one PR per cluster (typing-rule changes, semantics
    re-statement, lemma migration, preservation reproof).
. **L2 — Modality parameter**
  - Promote `is_linear_ty` from a per-type predicate to a judgment
    parameter `ℓ ∈ {Linear, Affine}`.
  - Implement `weaken_modality : Linear → Affine` as a single
    induction.
  - Restate the existing dual-grammar story (in `ephapax-linear/`)
    in terms of the modality.
. **L3 — Echo residue**
  - Add `formal/Echo.v` mirroring `echo-types/proofs/agda/Echo.agda`.
  - Introduce `TEcho ⟨op⟩` and the `T_Observe` rule.
  - Modify `S_Region_Exit` and `S_Drop` to produce residue values.
. **L4 — Mode declaration**
  - Project-level metadata (`Cargo.toml` or `ephapax.toml`).
  - Type checker reads the declaration and selects the L2 modality.
  - No proof obligations.

The previous "Preservation closure plan" section is **archived** —
see `formal/PRESERVATION-HANDOFF.md` for the historical record.
```

### 12.6 spec/SPEC.md and spec/ephapax-spec.md — the canonical spec

The spec is the binding contract for implementers. It must:

- Define `R_in / R_out` threading on the typing judgment.
- State the L1 sibling-safety invariant as a theorem.
- Mark L3 (Echo) as "future extension; not normative".
- Reference `EPHAPAX-VISION.adoc` for the dyad framing.

Add an introduction paragraph:

> Ephapax's type system has four orthogonal disciplines: **L1**
> region capabilities, **L2** structural modality (linear/affine),
> **L3** irreversibility residue (Echo Types — planned), and **L4**
> dyadic interaction mode (project-level declaration). This
> specification is normative for L1 and L2 and forward-looking for
> L3 and L4.

### 12.7 ephapax-linear/README.md — sublanguage docs

`ephapax-linear/` hosts both the linear and affine checkers (the
crate name predates the dyadic naming). Its README currently compares
the two grammars. Add a banner at the top:

```markdown
> **Naming note.** This crate is called `ephapax-linear` for
> historical reasons; it implements **both** L2 modalities
> (Linear and Affine). The two are not different languages — they
> are two admissible-derivation regimes over the same syntax and
> semantics. See `docs/vision/EPHAPAX-VISION.adoc` for the dyad,
> and `formal/PRESERVATION-DESIGN.md §5` for the L2 layer.
```

Update the comparison table title from "Dual Substructural Grammars"
to "Two L2 Modalities".

### 12.8 CLAUDE.md — agent guidance

CLAUDE.md already has the AffineScript disambiguation (correct, keep).
Add a section after the disambiguation block:

```markdown
## The four orthogonal layers

When working in this repo, the typing system has four layers. Knowing
which layer a question touches is the first step in answering it:

| Layer | One-line question to ask |
|---|---|
| L1 — Region capabilities | "Does this involve `R_in`, `R_out`, or `In r R`?" |
| L2 — Structural modality | "Is this about consumption, weakening, or Linear vs Affine?" |
| L3 — Echo residue | "Is this about *what was lost* when an irreversible step fired?" |
| L4 — Dyadic mode | "Is this a project-level mode declaration question?" |

Most questions touch exactly one layer. The design rationale is in
`formal/PRESERVATION-DESIGN.md`. The verified counterexample that
forced the redesign is in `formal/Counterexample.v`.

Standing rule: if a proposed change appears to require a side
condition on a compound typing rule (e.g. "the sibling doesn't
reference this region"), pause — the four-layer threading should make
that side condition *derivable*, not stated.
```

### 12.9 CHANGELOG.md — the next entry

```markdown
## [Unreleased]

### Architecture

- **Four-layer typing redesign** (`formal/PRESERVATION-DESIGN.md`).
  The original "linear+affine + regions" framing admitted a verified
  counterexample to preservation (`formal/Counterexample.v`). The
  redesign separates four orthogonal disciplines: region capabilities
  (L1), structural modality (L2), irreversibility residue (L3,
  planned), and dyadic interaction mode (L4). Each is a thin-poset
  decoration, composing without coherence obligations.

### Proof / theory

- Verified counterexample to preservation in the current rules
  (`formal/Counterexample.v` — three lemmas `Qed`). The
  counterexample is the canonical regression test for the L1 fix.

### Docs

- New design document: `formal/PRESERVATION-DESIGN.md`.
- README, EXPLAINME, EPHAPAX-VISION, ROADMAP, CLAUDE updated to
  reflect the four-layer story.
- Repo description and tagline updated.
```

### 12.10 site/index.md and the GH Pages homepage

Wherever the homepage exists (`site/index.md` is the current
candidate; the repo also has `homepage = https://hyperpolymath.github.io/ephapax/`),
update the hero block:

```markdown
# Ephapax

> Four-layer dyadic type system for WebAssembly memory safety.

Four orthogonal disciplines compose to guarantee compile-time
memory safety without a garbage collector:

- **Regions** (L1) — capabilities threaded through every expression.
- **Linear ↔ Affine** (L2) — the dyad, mother and child.
- **Echo** (L3, planned) — irreversibility leaves typed residue.
- **Dyadic mode** (L4) — declare which side you speak from.

Mechanically formalised in Coq and Idris2. See
[design](formal/PRESERVATION-DESIGN.md) ·
[vision](docs/vision/EPHAPAX-VISION.adoc) ·
[spec](spec/SPEC.md) ·
[roadmap](ROADMAP.adoc).
```

### 12.11 TOPOLOGY.md — the map

TOPOLOGY.md describes the repo's directory layout. Add a column
mapping each top-level dir to which layer(s) it implements:

```markdown
| Path | Purpose | Layer(s) |
|---|---|---|
| `src/ephapax-typing/` | type checker | L1, L2 |
| `src/ephapax-syntax/`, `src/ephapax-surface/` | AST | L1, L2 (same syntax) |
| `ephapax-linear/` | dual grammars + checkers | L2 |
| `formal/` | Coq mechanisation | L1 (L2 + L3 planned) |
| `idris2/`, `src/abi/Ephapax/` | Idris2 mechanisation | L1 |
| `docs/vision/`, `EPHAPAX-VISION.adoc` | dyad framing | L4 |
| `spec/` | normative spec | L1, L2 |
| (future) `formal/Echo.v` | residue mechanisation | L3 |
```

### 12.12 .machine_readable/6a2/*.a2ml — the structured metadata

These files (`STATE.a2ml`, `META.a2ml`, `ECOSYSTEM.a2ml`,
`AGENTIC.a2ml`, `NEUROSYM.a2ml`, `PLAYBOOK.a2ml`) feed downstream
tooling (hypatia, k9, the cartridge story). Each needs a structural
update:

| File | Update |
|---|---|
| `STATE.a2ml` | Add `@architecture: four-layer-typing-redesign` block; mark L1 in-flight, L2 partial-existing, L3 planned, L4 planned. |
| `META.a2ml` | Add `@layers:` array listing L1–L4 with one-line descriptions. Cross-reference echo-types as upstream theory dependency. |
| `ECOSYSTEM.a2ml` | Add `@relates_to: echo-types` (theory) and update `@guarantees:` to name L1 + L2 invariants. |
| `AGENTIC.a2ml` | Add a disambiguation block: "L1/L2/L3/L4 are layer names; ephapax-linear/ephapax-affine are L2 modes; Linear/Affine in echo-types are L3 modes — names overlap deliberately because the underlying poset is the same; agents must disambiguate by context." |
| `NEUROSYM.a2ml` | If it carries proof-state vectors, update preservation status: `closed-with-redesign-planned` (was `open-12-admits`). |
| `PLAYBOOK.a2ml` | Add an entry: "when a proof attempt requires sibling region disjointness as a side condition, escalate to L1 redesign rather than patching." |

### 12.13 GitHub wiki

`gh repo view` confirms wiki is enabled (`hasWikiEnabled: true`) but
the wiki has no content surveyed in this session. Recommended page
structure (clone `git clone git@github.com:hyperpolymath/ephapax.wiki.git`
locally, or create via the wiki UI):

| Page | Content |
|---|---|
| `Home` | Hero + four-layer summary + links into the repo (vision, design, spec, roadmap). |
| `The-Four-Layers` | Long-form explainer of L1–L4, with diagrams. Same content as the new README §"The four layers" but expanded with motivating examples. |
| `The-Dyad` | Excerpt + adapt from `EPHAPAX-VISION.adoc`'s "The Dyad" and "One Language, One Feel" sections. Public-facing. |
| `Region-Capabilities` | Long-form L1 explainer with the counterexample walked through (this is the **selling point** for the redesign — make it visceral). |
| `Echo-Types-and-Residue` | L3 explainer, citing echo-types as upstream. Mark as "planned" prominently. |
| `Dyadic-Mode-Declaration` | L4 page; mode declarations, when each fits. |
| `Soundness` | Index of what is proved, where, and at what status. Cross-references `formal/PRESERVATION-DESIGN.md` and `Counterexample.v`. |
| `FAQ` | Includes the disambiguation against AffineScript, the relationship to echo-types, why four layers (not three or five), and why the redesign was forced rather than chosen. |
| `Glossary` | Terms: region capability, modality, echo, residue, dyadic mode, thin-poset decoration. |

Wiki updates should happen **after** the repo-side docs land, so the
wiki can link to merged sources rather than to in-flight files.

### 12.14 Cross-cutting: language for new framing (drop-ins)

These passages are written once and dropped wherever needed:

**One-sentence what-this-is**:
> Ephapax is a dyadic programming language whose type system composes
> four orthogonal disciplines — region capabilities, structural
> modality, irreversibility residue, and dyadic mode — to guarantee
> compile-time WebAssembly memory safety without a garbage collector.

**One-paragraph what-this-is**:
> Ephapax is a programming language for WebAssembly with a
> mechanically verified type system. Four orthogonal disciplines
> compose to give the safety guarantees: **region capabilities** (L1)
> thread an explicit live-region set through every expression so a
> sibling cannot reference a region another sibling has exited;
> **structural modality** (L2) chooses between Linear (every linear
> binding must be consumed) and Affine (linear bindings may be
> dropped); **irreversibility residue** (L3, planned) makes the
> information lost by region exit and drop into a first-class,
> proof-relevant value; and **dyadic mode** (L4) declares, at the
> project level, which side of the linear/affine dyad the program
> speaks from. The four layers compose without coherence obligations
> because each is a thin-poset decoration, a construction borrowed
> verbatim from the `echo-types` mechanisation.

**Why four layers (FAQ-shaped)**:
> Q: Why four layers, not three or five?
>
> A: The four are what the soundness story demands. L1 is forced by
> a verified counterexample to preservation: sibling-safe region
> exit cannot be enforced without explicit capability threading. L2
> already exists in the implementation as the linear/affine split;
> the redesign promotes it from a per-type to a per-judgment notion
> and proves it Linear ⊆ Affine. L3 is required because Linear mode
> demands that irreversibility be *witnessed*, not silently
> performed; echo-types supplies the formal machinery. L4 is the
> project-level dial that selects which way L2 and L3 default. Drop
> any one and the architecture has a hole; add a fifth and you
> duplicate an existing layer.

**Why not just patch preservation (FAQ)**:
> Q: Why redesign the type system rather than patch the proof?
>
> A: `formal/Counterexample.v` is `Qed`: it exhibits a well-typed
> input that single-steps to an untypable output, at the same outer
> type. That is preservation *failing*, not preservation
> *unproven*. The fix isn't a tactic; it's a missing invariant. We
> add the invariant explicitly (L1 threading) rather than via ad-hoc
> side conditions on every compound rule, because sibling-region-
> disjointness should be a *theorem* about the new threading, not a
> premise on every rule.

### 12.15 Proof debt: what is proved today, what is **not**, and what this redesign will / will not change

This subsection is required reading before any future claim about
"ephapax preservation" or "ephapax soundness" is made — by a human
or by an agent. The architecture above describes the **target**;
this subsection describes the **current state**, which is much
narrower than the target.

#### 12.15.1 What is mechanised today

| Mechanisation | Scope | Status |
|---|---|---|
| `formal/Semantics.v`, `formal/Typing.v`, `formal/Syntax.v` (Coq) | A **single** typing judgment `R; G ⊢ e : T -| G'` and its small-step operational semantics | Builds with `coqc 8.18.0` |
| `formal/Counterexample.v` | A verified counterexample to preservation **as currently stated** | All three lemmas `Qed` |
| `preservation` theorem in `Semantics.v` | Soundness under the current single judgment | **`Admitted.`** — 11 cascading goals open (see `PRESERVATION-HANDOFF.md`) |
| `src/abi/Ephapax/…/*.idr` (Idris2) | Selected structural-safety claims | Per file; see `idris2 --check` |

#### 12.15.2 What the single judgment **is not**

The current `has_type` judgment **does not distinguish** Linear from
Affine ephapax. It is a single typing relation, parameterised over a
linearity context `G` whose entries carry a `(ty, bool)` consumption
flag. `is_linear_ty` returns a per-type tag. There is **no judgment
parameter** for L2 modality; there is **no proof** that Linear
derivations form a subset of Affine derivations; there is **no
mechanised ephapax-affine type system** at all.

Concretely: the Rust crate `ephapax-linear/` contains a
`LinearChecker` and an `AffineChecker`, with EBNF grammars and
behavioural tests proving they diverge on identical programs. That is
the implementation side of the dyad. The **proofs side** has not
caught up: the Coq + Idris2 formalisation models *one* judgment,
which behaviourally resembles the linear discipline (it requires
linear-typed bindings to be consumed) but is not labelled as such
and has no proven dual.

#### 12.15.3 What this redesign **will** establish

If executed as designed, the redesign closes:

- **L1 — region capabilities**: a new threading discipline + a
  reproof of preservation under the new rules. This is the central
  deliverable. The verified counterexample becomes a passing
  regression.
- **L2 promotion**: the judgment gains an `ℓ ∈ {Linear, Affine}`
  parameter, and a `weaken_modality : Linear ⇒ Affine` lemma. This
  is what *introduces* a mechanised ephapax-affine into the formal
  development for the first time.

#### 12.15.4 What this redesign **will not** establish

Equally explicitly — so future sessions, agents, and PR reviewers do
not assume otherwise:

- **The ephapax-affine type proofs are not done today, and the L1
  redesign on its own does not finish them.** L1 closes preservation
  under the *single* judgment that already exists. L2's
  modality-weakening lemma, once proved, will lift L1's preservation
  to the affine side — but that lift is a *separate* lemma that has
  not been written and is not part of the L1 patch. Until L2 lands
  *and* the weakening lemma is `Qed`, **no ephapax-affine soundness
  property is mechanised**.
- **No L3 (Echo / residue) proof obligation is closed.** L3 is
  forward-looking. Until `formal/Echo.v` exists and references it
  from the operational semantics, the Linear-echo "mandatory
  observation" property and the Affine-echo "non-duplicable
  residue" property are *aspirations*, not theorems.
- **No proof that the Rust `AffineChecker` agrees with any
  mechanised affine judgment.** The implementation-side dual exists;
  the mechanisation-side dual does not. Cross-checking the two is a
  third, independent body of work.
- **No proof of the L4 mode declaration's consistency** (e.g., that
  a program declared Linear cannot accidentally invoke an Affine-
  typed library through a hole in mode-elaboration). L4 is a UX
  layer in this design; making it sound requires further work that
  is not scoped here.

#### 12.15.5 The honest one-line summary

> **Ephapax's mechanised soundness story today is: one judgment,
> resembling linear discipline, with preservation `Admitted`. The
> verified counterexample shows preservation false as stated. The L1
> redesign in this document closes that counterexample. Ephapax-
> affine proofs as a distinct mechanised body of theorems are not
> done, will not be done by L1 alone, and will require L2 plus a
> follow-up weakening lemma before any "ephapax-affine is sound"
> claim is honest.**

Cite this subsection by section number (`§12.15`) whenever the
question of "what is proved" is asked. Do not paraphrase the bounds
upward.

### 12.16 Future research track — "Echo as foundation" (v2)

The four-layer design in this document treats **Echo as L3**: a residue
layer over the existing operational primitives (region exit, drop).
This is interpretation **B** of the question "can Echo replace the
reclamation model in ephapax?" — Echo *augments* the existing region
model; it does not replace it.

Interpretation **A** is a coherent research direction, but a much
larger one: making Echo the **operational foundation** itself. In an
A-shaped calculus:

- `ERelease v` becomes a primitive operation: yields a residue value
  of type `TEcho ⟨op⟩` *and* releases the underlying memory.
- `region r { … }` becomes **syntactic sugar** for a sequence of
  releases at scope exit, in reverse-allocation order.
- The operational semantics' primitive step is the release event,
  not the region exit.
- Linear-mode discharge becomes a **termination invariant**: a
  closed Linear program with no outstanding echo obligations is
  provably leak-free.
- Surface-language UX research is required: implicit-at-scope-exit
  vs explicit `release x` vs both. Borrow semantics under deferred
  release is a real theory question, not a notation question.

**This is a sibling v2 calculus, not a patch.** It will require its
own Coq development (`formal/Semantics_v2.v` or a separate
`ephapax-echo-foundation/` crate), its own design doc
(`formal/ECHO-AS-FOUNDATION.md`, currently not written), and its
own roadmap. The migration story (current ephapax programs ↦ v2
calculus) is itself a research question.

**Why this is staged separately from B:**

1. **B closes preservation in weeks; A is months.** Preservation is
   currently `Admitted` with a verified counterexample. Closing it
   is more urgent than v2 architectural exploration.
2. **B and A are not mutually exclusive.** Once B lands, A can be
   developed as a parallel branch using B's primitives. The L3 echo
   layer in B is a *prerequisite* for A's foundation rewrite —
   nothing wasted.
3. **Echo-types itself follows this restraint.** Its formal
   contribution is editorial reframing of homotopy fibers as
   irreversibility residues, not a new operational foundation. The
   same restraint applies here: Echo-as-L3 is the addition; Echo-as-
   foundation is a v2 design that earns its keep through
   experimentation, not by decree.

**Concrete next steps for A** (when undertaken; not now):

| Step | Output |
|---|---|
| 1. Design doc | `formal/ECHO-AS-FOUNDATION.md` — primitives, semantics, type rules |
| 2. Borrow-under-release theory | Resolve how borrows extend across release points; mechanise |
| 3. Coq prototype | `formal/Semantics_v2.v` with `ERelease` / `EObserve` primitives |
| 4. Linear discharge as termination invariant | Stronger than B's Linear-discharge theorem |
| 5. Region desugaring equivalence | Prove `region r { e }` ≡ sequenced releases of e's allocations |
| 6. Surface-syntax UX research | Implicit-vs-explicit release; default-scope semantics; ergonomic patterns |
| 7. WasmGC interop boundary | Explicit boundary types between echo-tracked and GC-tracked values |
| 8. Migration plan | Map v1 ephapax programs ↦ v2; most code should be syntactic-sugar-preserved |

**Tracking**: when the time comes, file as an issue
`ephapax: research — Echo as operational foundation (v2 calculus)`
with this section as the seed. Roadmap entry below.

Add to `ROADMAP.adoc` under "Future research tracks":

```adoc
=== Echo as operational foundation (v2)

The four-layer redesign (`formal/PRESERVATION-DESIGN.md`) treats Echo
as a residue layer (L3) over regions. A coherent v2 research direction
makes Echo the *foundation* itself: `ERelease` as a primitive
operation, regions desugared to sequenced releases, Linear-mode
discharge as a termination invariant.

**Not scheduled.** This is a months-long research effort, staged
after the L1+L2+L3 layer-redesign lands. See
`formal/PRESERVATION-DESIGN.md §12.16` for the seed; an
`ECHO-AS-FOUNDATION.md` design doc will be opened when the work
begins.
```

### 12.17 Execution order

The user has not asked for these edits to be made yet. Execution
order, when they are:

1. Land `formal/PRESERVATION-DESIGN.md` (this document).
2. Update README + EXPLAINME + EPHAPAX-VISION in one PR
   ("docs: introduce four-layer framing").
3. Update ROADMAP + CHANGELOG in one PR ("docs: roadmap reflects
   four-layer redesign; counterexample as regression").
4. Update CLAUDE + .machine_readable a2ml in one PR ("docs(agent):
   layer-aware guidance").
5. Update spec/ in one PR ("spec: introduce L1 R-threading; L3
   forward-looking").
6. Update site/index.md + repo description + tagline in one PR ("site:
   four-layer hero").
7. Wiki updates last, out-of-band (wiki commits don't go through PR
   review).

All in-repo PRs follow standing policy: GPG-signed, auto-merge ON,
GH conventions matched.

