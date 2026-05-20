||| SPDX-License-Identifier: PMPL-1.0-or-later
||| Ephapax ABI: Boundary Types
|||
||| Idris2 statements of the data types that the Ephapax Rust pipeline
||| moves across its trust boundaries (typing, IR, WASM compilation,
||| Zig FFI token buffer). These mirror Rust types in:
|||   - src/ephapax-syntax/    (Term, Type, Qualifier)
|||   - src/ephapax-typing/    (Discipline, TypeEnv)
|||   - src/ephapax-ir/        (SExpr)
|||   - src/ephapax-wasm/      (WasmExpr, FuncIdx)
|||
||| This module is the ABI/FFI seam mandated by
||| standards/rhodium-standard-repositories/spec/LANGUAGE-POLICY.adoc
||| §Terminology: the Rust here is "Rust/SPARK" and must be DESIGNED to
||| admit SPARK/Ada modules across an Idris2-typed boundary. Nothing in
||| the Rust crates is itself the ABI; this file is.
|||
||| Verification scope: this file is a faithful, total Idris2 model of
||| the boundary data. The existing formalisation in `src/formal/` deals
||| with region/linear-type metatheory, but did not previously expose a
||| named ABI seam — this module fills that gap.

module Ephapax.ABI.Types

import Data.List
import Data.String
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Qualifier (mirror of Rust enum Qual, src/ephapax-syntax/ qualifier)
--------------------------------------------------------------------------------

||| Resource qualifier on a binding. Mirrors the dyadic-type-system
||| `Qual` enum: `Linear` = exactly-once, `Affine` = at-most-once,
||| `Unrestricted` = unrestricted use. Constructor order is ABI-
||| significant.
public export
data Qual : Type where
  Linear       : Qual
  Affine       : Qual
  Unrestricted : Qual

public export
DecEq Qual where
  decEq Linear       Linear       = Yes Refl
  decEq Affine       Affine       = Yes Refl
  decEq Unrestricted Unrestricted = Yes Refl
  decEq Linear       Affine       = No (\case Refl impossible)
  decEq Linear       Unrestricted = No (\case Refl impossible)
  decEq Affine       Linear       = No (\case Refl impossible)
  decEq Affine       Unrestricted = No (\case Refl impossible)
  decEq Unrestricted Linear       = No (\case Refl impossible)
  decEq Unrestricted Affine       = No (\case Refl impossible)

--------------------------------------------------------------------------------
-- Region identifier (mirror of src/formal/Ephapax/Formal/Region.idr RegionId)
--------------------------------------------------------------------------------

||| A region identifier — named, depth-tagged scope. Re-stated at the
||| seam (rather than imported from Ephapax.Formal.Region) so the ABI is
||| self-contained: a SPARK/Ada side need not depend on the metatheory
||| package to read the seam.
public export
record RegionId where
  constructor MkRegionId
  name  : String
  depth : Nat

--------------------------------------------------------------------------------
-- Types (mirror of Rust enum Type, src/ephapax-syntax/types)
--------------------------------------------------------------------------------

||| Ephapax types. Constructor order is ABI-significant. `TArrow` carries
||| the qualifier of the function value itself (the binder's qualifier
||| lives on the binder). `TScoped` is the region-bound type — the
||| metatheory's `Scoped r a` (`src/formal/Ephapax/Formal/Region.idr`).
public export
data Ty : Type where
  TUnit    : Ty
  TBool    : Ty
  TInt     : Ty
  TString  : Ty
  TArrow   : (q : Qual) -> (dom : Ty) -> (cod : Ty) -> Ty
  TPair    : (l : Ty) -> (r : Ty) -> Ty
  TScoped  : (region : RegionId) -> (inner : Ty) -> Ty

--------------------------------------------------------------------------------
-- Terms (mirror of Rust enum Term, src/ephapax-syntax/)
--------------------------------------------------------------------------------

||| Ephapax surface terms. Constructor order is ABI-significant. The
||| interpreter (src/ephapax-interp/), the typing pass (src/ephapax-typing/)
||| and the IR lowering (src/ephapax-ir/) all walk this shape.
public export
data Term : Type where
  EVar      : (name : String) -> Term
  ELit      : (value : String) -> Term
  ELam      : (q : Qual) -> (param : String) -> (paramTy : Ty) -> (body : Term) -> Term
  EApp      : (fn : Term) -> (arg : Term) -> Term
  ELet      : (q : Qual) -> (name : String) -> (rhs : Term) -> (body : Term) -> Term
  EPair     : (l : Term) -> (r : Term) -> Term
  ERegion   : (region : RegionId) -> (body : Term) -> Term

--------------------------------------------------------------------------------
-- Typing context (mirror of Rust struct TypeEnv, src/ephapax-typing/)
--------------------------------------------------------------------------------

||| A typing context entry: name × qualifier × type. The Rust
||| `TypeEnv` is a `Vec<(String, Qual, Type)>` walked left-to-right by
||| the discipline checker.
public export
record CtxEntry where
  constructor MkCtxEntry
  name : String
  qual : Qual
  ty   : Ty

public export
TypeCtx : Type
TypeCtx = List CtxEntry

--------------------------------------------------------------------------------
-- IR S-expressions (mirror of Rust enum SExpr, src/ephapax-ir/)
--------------------------------------------------------------------------------

||| The Ephapax IR is an S-expression intermediate form between the
||| surface AST and the WASM backend. The shape is intentionally simpler
||| than `Term` (no qualifier annotations — those are erased after
||| type-checking, and the IR is the "discipline-erased" form).
public export
data SExpr : Type where
  SAtom : (token : String) -> SExpr
  SList : (children : List SExpr) -> SExpr

--------------------------------------------------------------------------------
-- WASM expressions (mirror of Rust src/ephapax-wasm/ minimal surface)
--------------------------------------------------------------------------------

||| WebAssembly function index — bounded `u32`. The range obligation is
||| discharged at the Foreign boundary (see Foreign.idr `InU32`).
public export
FuncIdx : Type
FuncIdx = Nat

||| Minimal WASM expression surface. The real Rust backend emits a much
||| richer set (control flow, memory ops, table refs); the ABI only
||| names the constructs whose typing/semantics must be preserved by
||| the lowering, so the compiler-correctness invariant E6 has somewhere
||| to live without committing to a particular emit form.
public export
data WasmExpr : Type where
  WI32Const   : (value : Nat) -> WasmExpr
  WLocalGet   : (idx : Nat) -> WasmExpr
  WLocalSet   : (idx : Nat) -> (rhs : WasmExpr) -> WasmExpr
  WCall       : (fn : FuncIdx) -> (args : List WasmExpr) -> WasmExpr
  WBlock      : (body : List WasmExpr) -> WasmExpr
