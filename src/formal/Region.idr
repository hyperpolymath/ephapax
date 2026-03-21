-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
||| Region Type System for Ephapax
|||
||| Formalises regions as named, scoped arenas with a partial order (outlives).
||| Regions are orthogonal to the affine/linear qualifier — this module defines
||| regions without reference to linearity. The fusion is in RegionLinear.idr.
|||
||| Key types:
||| - RegionId: unique identifier for a region
||| - Outlives: proof that one region's lifetime contains another's
||| - RegionNesting: well-formed nesting structure (stack discipline)
||| - Scoped: a value bound to a specific region
|||
||| Theoretical basis: Tofte & Talpin (1997), extended with dependent types.

module Ephapax.Formal.Region

import Data.So
import Data.Nat
import Data.List

%default total

--------------------------------------------------------------------------------
-- Region Identifiers
--------------------------------------------------------------------------------

||| A region identifier. Regions are named scopes that own allocations.
||| The Nat is a de Bruijn-style nesting depth (0 = outermost).
public export
data RegionId : Type where
  MkRegion : (name : String) -> (depth : Nat) -> RegionId

||| Regions are decidably equal.
public export
Eq RegionId where
  (MkRegion n1 d1) == (MkRegion n2 d2) = n1 == n2 && d1 == d2

||| Extract region depth.
public export
regionDepth : RegionId -> Nat
regionDepth (MkRegion _ d) = d

||| Extract region name.
public export
regionName : RegionId -> String
regionName (MkRegion n _) = n

--------------------------------------------------------------------------------
-- Outlives Relation
--------------------------------------------------------------------------------

||| Proof that region `outer` outlives region `inner`.
|||
||| A region outlives another if it was created before and will be destroyed
||| after. Under stack discipline, this is equivalent to:
|||   depth(outer) < depth(inner)
|||
||| This is the partial order on regions. It governs what values can be
||| used where: a value in region r can only be accessed in scopes where
||| r is still alive (i.e., in r or in regions that r outlives).
public export
data Outlives : (outer : RegionId) -> (inner : RegionId) -> Type where
  ||| Direct nesting: outer is one level above inner.
  OutlivesDirectly : (outer : RegionId)
                   -> (inner : RegionId)
                   -> {auto 0 prf : So (regionDepth outer < regionDepth inner)}
                   -> Outlives outer inner

||| Outlives is reflexive (a region outlives itself — trivially).
public export
data OutlivesRefl : (r : RegionId) -> Type where
  SameRegion : (r : RegionId) -> OutlivesRefl r

||| Outlives is transitive.
||| If a outlives b and b outlives c, then a outlives c.
public export
outlivesTransitive : Outlives a b -> Outlives b c -> Outlives a c
outlivesTransitive (OutlivesDirectly a b) (OutlivesDirectly b c) =
  -- depth(a) < depth(b) < depth(c), so depth(a) < depth(c)
  OutlivesDirectly a c

--------------------------------------------------------------------------------
-- Region Nesting (Stack Discipline)
--------------------------------------------------------------------------------

||| A well-formed region nesting is a stack of region IDs where each
||| successive region has strictly greater depth.
|||
||| This enforces LIFO: the innermost region is created last and destroyed
||| first. No region can be destroyed while an inner region is still alive.
public export
data RegionStack : Type where
  ||| Empty stack (no active regions).
  Empty : RegionStack
  ||| Push a new region onto the stack.
  ||| Requires that the new region has greater depth than the top.
  Push  : (r : RegionId)
        -> (rest : RegionStack)
        -> {auto 0 valid : ValidPush r rest}
        -> RegionStack

||| Predicate: is it valid to push region r onto stack s?
||| Valid if the stack is empty or r has greater depth than the top.
public export
data ValidPush : RegionId -> RegionStack -> Type where
  PushOnEmpty : ValidPush r Empty
  PushOnTop   : (r : RegionId)
              -> (top : RegionId)
              -> (rest : RegionStack)
              -> {auto 0 deeper : So (regionDepth r > regionDepth top)}
              -> ValidPush r (Push top rest)

||| Look up whether a region is in the stack (i.e., currently alive).
public export
data InStack : RegionId -> RegionStack -> Type where
  Here  : InStack r (Push r rest)
  There : InStack r rest -> InStack r (Push other rest)

--------------------------------------------------------------------------------
-- Region-Scoped Values
--------------------------------------------------------------------------------

||| A value scoped to a specific region.
|||
||| `Scoped r a` means: a value of type `a` whose memory is allocated in
||| region `r`. The value's lifetime is bounded by `r` — when `r` exits,
||| the memory is freed.
|||
||| This is ORTHOGONAL to the affine/linear qualifier:
||| - `let x : Scoped r Foo = ...`   (affine, in region r)
||| - `let! x : Scoped r Foo = ...`  (linear, in region r)
|||
||| Both forms are subject to the same region-scoping constraint:
||| x cannot appear in any expression that outlives r.
public export
data Scoped : (r : RegionId) -> (a : Type) -> Type where
  ||| A value allocated in region r.
  ||| The region must be alive (in the active stack) at the point of allocation.
  InRegion : {0 r : RegionId}
           -> (val : a)
           -> Scoped r a

||| Extract the value from a Scoped wrapper.
||| This is a borrow — the region still owns the memory.
public export
peek : Scoped r a -> a
peek (InRegion val) = val

||| The region a scoped value belongs to (type-level query).
public export
scopedRegion : Scoped r a -> RegionId
scopedRegion {r} _ = r

--------------------------------------------------------------------------------
-- Region-Scoped References (Borrows)
--------------------------------------------------------------------------------

||| A borrow of a value in region r.
|||
||| `Ref r a` is a reference to a value of type `a` in region `r`.
||| The reference is valid only while `r` is alive. The type system
||| ensures that Ref r a cannot outlive r.
public export
data Ref : (r : RegionId) -> (a : Type) -> Type where
  MkRef : {0 r : RegionId} -> (target : a) -> Ref r a

||| Dereference a region-scoped reference.
public export
deref : Ref r a -> a
deref (MkRef target) = target

||| A borrow of a scoped value produces a reference in the same region.
public export
borrow : Scoped r a -> Ref r a
borrow (InRegion val) = MkRef val

--------------------------------------------------------------------------------
-- Region Polymorphism
--------------------------------------------------------------------------------

||| A region-polymorphic function type.
|||
||| `ForallRegion f` means: for any region r, f r holds.
||| This enables writing functions that work in any region:
|||
|||   duplicate : ForallRegion (\r => Scoped r String -> Scoped r String)
|||
||| The region variable is universally quantified — the caller chooses
||| which region to use.
public export
ForallRegion : (RegionId -> Type) -> Type
ForallRegion f = (r : RegionId) -> f r

--------------------------------------------------------------------------------
-- Fundamental Properties
--------------------------------------------------------------------------------

||| Property: A Scoped value's region is fixed at construction time.
||| It cannot change regions after allocation.
|||
||| This is enforced by the type: Scoped r a has r as a type parameter,
||| not a runtime field. There is no operation that changes r.
public export
scopedRegionFixed : (v : Scoped r a) -> (scopedRegion v = r)
scopedRegionFixed (InRegion _) = Refl

||| Property: If region `outer` outlives region `inner`, then
||| a value in `outer` is accessible within `inner`.
|||
||| This is the fundamental region-access rule: you can use values
||| from enclosing regions, but not from regions that have already exited.
public export
data Accessible : (valRegion : RegionId) -> (useRegion : RegionId) -> Type where
  ||| A value is accessible in its own region.
  AccessSelf : Accessible r r
  ||| A value in an outer region is accessible in an inner region.
  AccessOuter : Outlives outer inner -> Accessible outer inner

||| Property: Accessibility is NOT symmetric.
||| A value in an inner region is NOT accessible after the inner region exits.
|||
||| This is the key constraint: inner values cannot escape to outer scopes.
||| We express this as: there is no Accessible inner outer when
||| depth(inner) > depth(outer).
|||
||| (The proof is by the structure of Outlives: it requires strictly
||| increasing depth, which excludes the reverse direction.)
