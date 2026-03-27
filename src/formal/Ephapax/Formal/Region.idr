-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
||| Region Type System for Ephapax
|||
||| Formalises regions as named, scoped arenas with a partial order (outlives).
||| Uses propositional equality (DecEq) throughout for proof robustness.
|||
||| Theoretical basis: Tofte & Talpin (1997), extended with dependent types.

module Ephapax.Formal.Region

import Data.Nat
import Data.List
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Region Identifiers
--------------------------------------------------------------------------------

||| A region identifier. Regions are named scopes that own allocations.
public export
data RegionId : Type where
  MkRegion : (name : String) -> (depth : Nat) -> RegionId

||| Decidable equality for RegionId.
||| This is the foundation for all propositional proofs about regions.
public export
DecEq RegionId where
  decEq (MkRegion n1 d1) (MkRegion n2 d2) =
    case decEq n1 n2 of
      Yes pn => case decEq d1 d2 of
        Yes pd => Yes (rewrite pn in rewrite pd in Refl)
        No  nd => No (\eq => nd (case eq of Refl => Refl))
      No  nn => No (\eq => nn (case eq of Refl => Refl))

||| Boolean equality (derived from DecEq).
public export
Eq RegionId where
  r1 == r2 = case decEq r1 r2 of
    Yes _ => True
    No _  => False

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
||| Uses propositional LT instead of So.
public export
data Outlives : (outer : RegionId) -> (inner : RegionId) -> Type where
  OutlivesDirectly : (outer : RegionId)
                   -> (inner : RegionId)
                   -> {auto 0 prf : LT (regionDepth outer) (regionDepth inner)}
                   -> Outlives outer inner

||| Outlives is transitive (via LT transitivity).
public export
outlivesTransitive : Outlives a b -> Outlives b c -> Outlives a c
outlivesTransitive (OutlivesDirectly a b {prf=p1}) (OutlivesDirectly b c {prf=p2}) =
  OutlivesDirectly a c {prf = transitive p1 (lteSuccLeft p2)}

--------------------------------------------------------------------------------
-- Region Nesting (Stack Discipline)
--------------------------------------------------------------------------------

||| A region stack (LIFO nesting).
public export
data RegionStack : Type where
  Empty : RegionStack
  Push  : (r : RegionId) -> (rest : RegionStack) -> RegionStack

||| Look up whether a region is in the stack.
public export
data InStack : RegionId -> RegionStack -> Type where
  Here  : InStack r (Push r rest)
  There : InStack r rest -> InStack r (Push other rest)

--------------------------------------------------------------------------------
-- Region-Scoped Values
--------------------------------------------------------------------------------

||| A value scoped to a specific region.
||| `Scoped r a` means: memory allocated in region `r`.
public export
data Scoped : (r : RegionId) -> (a : Type) -> Type where
  InRegion : {0 r : RegionId} -> (val : a) -> Scoped r a

||| Extract the value from a Scoped wrapper (borrow).
public export
peek : Scoped r a -> a
peek (InRegion val) = val

--------------------------------------------------------------------------------
-- Region-Scoped References (Borrows)
--------------------------------------------------------------------------------

||| A borrowed reference to a value in region r.
public export
data RegionRef : (r : RegionId) -> (a : Type) -> Type where
  BorrowRef : {0 r : RegionId} -> (ref : a) -> RegionRef r a

||| Dereference a borrowed reference.
public export
deref : RegionRef r a -> a
deref (BorrowRef ref) = ref

||| Region polymorphism: a function that works for any region.
public export
ForallRegion : (RegionId -> Type) -> Type
ForallRegion f = (r : RegionId) -> f r

--------------------------------------------------------------------------------
-- Accessibility
--------------------------------------------------------------------------------

||| A value in region `target` is accessible from region `scope`.
public export
data Accessible : (target : RegionId) -> (scope : RegionId) -> Type where
  AccessSelf : Accessible r r
  AccessOuter : Outlives outer inner -> Accessible outer inner

-- Accessibility is NOT symmetric: inner values cannot escape to outer scopes.
-- This is enforced by Outlives requiring strictly increasing depth.
