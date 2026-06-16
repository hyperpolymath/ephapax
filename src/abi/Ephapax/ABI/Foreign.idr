||| SPDX-License-Identifier: MPL-2.0
-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| Ephapax ABI: FFI Boundary Obligations
|||
||| The Zig/WASM-FFI side of the Ephapax ABI seam. The Rust pipeline
||| uses fixed-width integers across two boundaries:
|||   1. Zig FFI token buffer (`Ephapax.Parse.ZigBuffer` in the Idris2
||| 	  Parse package) — `u32` offsets/lengths into the input source.
|||   2. WASM lowering (`src/ephapax-wasm/`) — `u32` function indices,
|||      `u32` local indices, `i32` literal values.
|||
||| The Idris2 model in Types.idr uses `Nat` for these. This module
||| states the range obligations that the boundary must discharge when
||| marshalling between the Rust representation and the typed model,
||| plus the C-ABI result codes any FFI entry-point should expose.
|||
||| Per LANGUAGE-POLICY.adoc §Terminology and §"Rust is never the ABI":
||| the boundary is Idris2 (this seam) + Zig (FFI). Rust/SPARK is the
||| application logic on one side; a future SPARK/Ada code generator
||| could sit on the other side of THIS contract without changing it.

module Ephapax.ABI.Foreign

import Ephapax.ABI.Types
import Ephapax.ABI.Invariants
import Data.Nat
import Data.So

%default total

--------------------------------------------------------------------------------
-- Fixed-width range obligations
--
-- Bounds are `Integer`, not `Nat` — the proof-of-work `Foreign.idr`
-- learned the hard way (PR proof-of-work#63, 2026-05-20) that a `Nat`
-- bound of 2^32 forces the Idris2 0.8.0 data-constructor elaborator to
-- reduce the literal under `LT n bound` inside the constructor's type,
-- which expands ~4×10^9 `S` ctors and hangs `--build`. The boundary
-- predicate is therefore expressed as `So (natToInteger n < bound)`,
-- propositionally equivalent (the Rust `u32` round-trips to precisely
-- the Nats with `natToInteger n < 2^32`) but does not trigger unary
-- expansion. Do not rewrite back to `LT n bound`.
--------------------------------------------------------------------------------

||| u32 upper bound (2^32). WASM function indices, local indices and
||| Zig token-buffer offsets/lengths crossing the FFI must fit; the
||| Rust types guarantee this, the Idris2 Nat model does not, so the
||| obligation is made explicit here.
public export
u32Max : Integer
u32Max = 4294967296

||| Proof-carrying "this Nat fits in a u32".
public export
data InU32 : Nat -> Type where
  MkInU32 : (n : Nat) -> So (natToInteger n < Foreign.u32Max) -> InU32 n

||| i32 signed-range upper bound (2^31). WASM `i32.const` literals must
||| fit; the magnitude bound below is the absolute value (sign is
||| tracked separately by the producer).
public export
i32Max : Integer
i32Max = 2147483648

public export
data InI32Magnitude : Nat -> Type where
  MkInI32Mag : (n : Nat) -> So (natToInteger n < Foreign.i32Max) -> InI32Magnitude n

||| A WASM function index is FFI-marshalable iff it fits in u32.
public export
MarshalableFuncIdx : FuncIdx -> Type
MarshalableFuncIdx fi = InU32 fi

--------------------------------------------------------------------------------
-- C-ABI result codes for compile/typecheck entry points
--------------------------------------------------------------------------------

||| Stable C integer result for a typecheck/compile call across the FFI.
||| Constructor order is ABI-significant.
public export
data CompileResult : Type where
  CompileOk          : CompileResult   -- typecheck + lowering succeeded
  CompileTypeError   : CompileResult   -- discipline check rejected the term
  CompileRegionError : CompileResult   -- region-safety check rejected the term
  CompileLowerError  : CompileResult   -- IR/WASM lowering failed (should never
                                       -- happen on a well-typed term — E6)
  CompileMalformed   : CompileResult   -- input failed surface parse

public export
compileResultToInt : CompileResult -> Nat
compileResultToInt CompileOk          = 0
compileResultToInt CompileTypeError   = 1
compileResultToInt CompileRegionError = 2
compileResultToInt CompileLowerError  = 3
compileResultToInt CompileMalformed   = 4

public export
compileResultFromInt : Nat -> Maybe CompileResult
compileResultFromInt 0 = Just CompileOk
compileResultFromInt 1 = Just CompileTypeError
compileResultFromInt 2 = Just CompileRegionError
compileResultFromInt 3 = Just CompileLowerError
compileResultFromInt 4 = Just CompileMalformed
compileResultFromInt _ = Nothing

||| Round-trip proof for the result-code mapping (the one property
||| fully dischargeable here, by case analysis).
public export
compileResultRoundTrip :
  (r : CompileResult) -> compileResultFromInt (compileResultToInt r) = Just r
compileResultRoundTrip CompileOk          = Refl
compileResultRoundTrip CompileTypeError   = Refl
compileResultRoundTrip CompileRegionError = Refl
compileResultRoundTrip CompileLowerError  = Refl
compileResultRoundTrip CompileMalformed   = Refl

--------------------------------------------------------------------------------
-- The FFI contract any compile entry-point must honour
--------------------------------------------------------------------------------

||| The boundary obligation: a `CompileOk` result handed back across the
||| FFI must be backed by an E5 `WasmTyped (compile t) T` certificate
||| for the submitted term. This ties the C-ABI return value to the
||| Idris2 compiler-correctness statement. The Rust does not yet
||| *produce* the witness (PROOF-NEEDS.md E5); the type records exactly
||| what is owed.
public export
0 compileOkImpliesWasmTyped :
  (g : TypeCtx) -> (t : Term) -> (T : Ty) ->
  (r : CompileResult) ->
  r = CompileOk ->
  WellTyped g t T ->
  WasmTyped (compile t) T
