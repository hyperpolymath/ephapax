||| SPDX-License-Identifier: MPL-2.0
-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| Ephapax ABI: Correctness-Critical Invariants
|||
||| Type-level statements of the invariants the Ephapax compiler
||| pipeline must uphold at its trust boundaries (typing pass, IR
||| lowering, WASM emit, FFI marshal). Each invariant is stated as an
||| Idris2 type/proposition. Where the property is a discharged proof
||| elsewhere in the repo, it is cited; where it is OWED or PARTIAL,
||| it is marked as an erased postulate and tracked in PROOF-NEEDS.md.
|||
||| Naming: this seam lists the invariants whose breach silently
||| corrupts compiled programs — the language-implementation analogue
||| of proof-of-work's I1–I7 verifier-soundness register.
|||
||| Authoritative per-ID status: PROOF-NEEDS.md § Invariant register.
||| This file is the type-level statement of those obligations.

module Ephapax.ABI.Invariants

import Ephapax.ABI.Types

%default total

--------------------------------------------------------------------------------
-- E1. Type preservation
--
-- Source: formal/Semantics.v `preservation`,
--         formal/Typing.v step-respects-typing supporting lemmas.
--
-- Statement (informal): if `well_typed t T` and `t ⇒ t'` then
-- `well_typed t' T`. Currently `Admitted` in Coq — the proof script at
-- formal/Semantics.v L3215–L3326 leaves residual open goals
-- (`coqc` 8.18.0 rejects the `Qed.` with "Attempt to save an incomplete
-- proof"). This Idris2 seam states the obligation; discharge happens on
-- the Coq side.
--------------------------------------------------------------------------------

||| Abstract typing relation. The Coq formalisation `formal/Typing.v`
||| carries the inductive `well_typed` (`HasType`) judgement; this is
||| its seam-level abstraction.
public export
data WellTyped : TypeCtx -> Term -> Ty -> Type where
  -- Intentionally abstract: the seam states the obligation, not the
  -- judgement's rules (those live in formal/Typing.v). A SPARK/Ada side
  -- consuming the seam only needs the *interface* of `WellTyped`, not
  -- its constructors.

||| Abstract one-step reduction. Mirrors the Coq `step` relation in
||| formal/Semantics.v. Like WellTyped, declared abstractly at the seam.
public export
data Step : Term -> Term -> Type where

||| E1 (OWED — Coq side). If `t` is well-typed at `T` in `g` and steps
||| to `t'`, then `t'` is also well-typed at `T` in `g`. **The Coq
||| `preservation` theorem in formal/Semantics.v is currently Admitted**
||| (see PROOF-NEEDS.md L1–L18). The Idris2 seam states the obligation
||| so a SPARK/Ada implementation sees what is owed.
public export
0 typePreservation :
  (g : TypeCtx) -> (t, t' : Term) -> (T : Ty) ->
  WellTyped g t T -> Step t t' -> WellTyped g t' T

--------------------------------------------------------------------------------
-- E2. Linear-binding consumption coverage
--
-- Source: src/formal/Ephapax/Formal/Qualifier.idr `splitLinearCoverage`
--         (DISCHARGED, MERGED 2026-05-19 via ephapax#85).
--
-- Statement: in any context split (e.g. across a `let` boundary or a
-- pair-elimination), every linear binding in the original context
-- appears in exactly one side of the split. The discharged version
-- proves this for arbitrary positions in the context (not just the
-- head, the form `nonDiminishment` had). The general form across
-- *control-flow* paths (effect handlers, region exit, exceptions)
-- remains OWED.
--------------------------------------------------------------------------------

||| E2 (PARTIAL — head/position form DISCHARGED, control-flow form OWED).
||| The position-form discharge lives in
||| `src/formal/Ephapax/Formal/Qualifier.idr` as `splitLinearCoverage`
||| (a real proof, no escape hatches). At the seam we only state the
||| OWED control-flow generalisation: a linear binding consumed in one
||| branch of a conditional / one arm of pattern-match / one exit of
||| a region must also be consumed in every other branch.
public export
0 linearConsumptionAcrossControlFlow :
  (g : TypeCtx) -> (t : Term) -> (T : Ty) ->
  WellTyped g t T -> Type

--------------------------------------------------------------------------------
-- E3. No region escape (narrow form discharged)
--
-- Source: src/formal/Ephapax/Formal/RegionLinear.idr `noEscapeTheorem`
--         (DISCHARGED, real proof — case analysis on NoRegionInType).
--
-- The discharged form proves the narrow case
--   `NoRegionInType r (Scoped r a) -> Void`
-- (a value scoped to r cannot itself claim "no region r appears in my
-- type"). The general statement — values scoped to r never appear
-- outside r's lexical extent at runtime — is OWED at the operational-
-- semantics level (it needs E1 type-preservation as a lemma).
--------------------------------------------------------------------------------

||| Abstract "term references region r" predicate. Mirrors the Rust
||| typing pass's region-membership check.
public export
0 ReferencesRegion : RegionId -> Term -> Type

||| E3 (OWED — operational form). If a region-block exits with result
||| value `v` and the region `r` is no longer in scope, then `v` does
||| not reference `r` at runtime. The static form
||| (`noEscapeTheorem` on types) is discharged in
||| `Ephapax.Formal.RegionLinear.noEscapeTheorem`; the operational
||| form rests on E1 type-preservation across `ERegion` reduction.
public export
0 regionNoRuntimeEscape :
  (r : RegionId) -> (body, result : Term) ->
  Step (ERegion r body) result ->
  ReferencesRegion r result -> Void

--------------------------------------------------------------------------------
-- E4. Vacuous wrappers in formal/ — flagged, NOT a seam invariant
--
-- Source: src/formal/Ephapax/Formal/RegionLinear.idr
--         `regionSafetyExtract`, `noGCExtract`.
--
-- ROADMAP.adoc / PROOF-NEEDS.md cite these as "regionSafetyTheorem" /
-- "noGCTheorem" being complete. Their bodies are tautological wrappers:
--   regionSafetyExtract r ctx t ne lc = ne
--   noGCExtract        r ctx t ne lc = (ne, lc)
-- — they return their inputs unchanged. The proofs are sound (no
-- escape hatches) but the *content* is vacuous: they don't establish
-- region safety, they just extract a witness that was already given.
--
-- The honest seam invariants are E3 (real no-escape, OWED at the
-- operational level) and a NEW E4 (below) for the GC-freedom property
-- that `noGCExtract` only names. Both are OWED; the wrappers should be
-- separately replaced or honestly demoted (tracked, NOT in this seam).
--------------------------------------------------------------------------------

||| E4 (OWED). Operational GC-freedom: no run-time garbage collector is
||| needed because every heap-allocated value's lifetime is statically
||| bounded by an enclosing region. The current Idris2 `noGCExtract`
||| tautologically returns its inputs and does not establish this.
public export
0 noRuntimeGC :
  (g : TypeCtx) -> (t : Term) -> (T : Ty) ->
  WellTyped g t T -> Type

--------------------------------------------------------------------------------
-- E5. WASM compilation correctness
--
-- Source: src/ephapax-wasm/ (compile_term : Term → WasmExpr).
--
-- Invariant: the Rust WASM backend's lowering preserves typing and
-- semantics. No Idris2 or Coq counterpart for `compile_term` exists in
-- the repo today (the formalisation stops at the source language); the
-- entire claim is OWED.
--------------------------------------------------------------------------------

||| Abstract WASM typing judgement (would mirror the WebAssembly spec's
||| validation rules).
public export
0 WasmTyped : WasmExpr -> Ty -> Type

||| Abstract compilation function. The Rust `compile_term` lives in
||| src/ephapax-wasm/; the seam states the obligation, not the algorithm.
public export
0 compile : Term -> WasmExpr

||| E5 (OWED). If a source term is well-typed at `T`, its WASM
||| compilation is also well-typed at `T`. No formalisation of
||| `compile` exists in this repo today (neither Idris2 nor Coq);
||| this is the highest-leverage compiler-correctness gap.
public export
0 wasmCompilationPreservesTyping :
  (g : TypeCtx) -> (t : Term) -> (T : Ty) ->
  WellTyped g t T -> WasmTyped (compile t) T

--------------------------------------------------------------------------------
-- E6. IR lowering correctness
--
-- Source: src/ephapax-ir/ (lower : Term → SExpr).
--
-- The IR lowering is qualifier-erasing (the S-expression form drops
-- linear/affine annotations because the discipline check has already
-- run). Invariant: lowering preserves *operational* semantics — every
-- reduction in the source corresponds to a reduction in the IR.
-- OWED; the IR has no formalisation today.
--------------------------------------------------------------------------------

||| Abstract IR-level reduction.
public export
0 SStep : SExpr -> SExpr -> Type

||| Abstract IR lowering function.
public export
0 lowerIR : Term -> SExpr

||| E6 (OWED). Source reduction implies IR reduction: every step in the
||| source operational semantics corresponds to one (or more) steps in
||| the IR. No formalisation today.
public export
0 irLoweringPreservesSemantics :
  (t, t' : Term) -> Step t t' ->
  (s' : SExpr ** SStep (lowerIR t) s')
