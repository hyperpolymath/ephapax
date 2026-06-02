-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.Parse.Stream

import Ephapax.Parse.Lexer
import Ephapax.Parse.ZigBuffer

%default total

public export
record Stream where
  constructor MkStream
  buf : TokBuf
  len : Int
  index : Int
  peekCount : Int
  popCount : Int
  expectCount : Int

public export
fromBuffer : TokBuf -> Stream
fromBuffer buf = MkStream buf (bufLen buf) 0 0 0 0

public export
peekTok : Stream -> Maybe Token
peekTok s =
  if s.index < 0 || s.index >= s.len then Nothing
  else Just (MkToken (getTokKind s.buf s.index) (getTokPos s.buf s.index))

public export
popTok : Stream -> Maybe (Token, Stream)
popTok s =
  if s.index < 0 || s.index >= s.len then Nothing
  else
    let tok = MkToken (getTokKind s.buf s.index) (getTokPos s.buf s.index) in
    Just (tok, MkStream s.buf s.len (s.index + 1) s.peekCount (s.popCount + 1) s.expectCount)

public export
posOf : Stream -> Maybe Pos
posOf s = case peekTok s of
  Nothing => Nothing
  Just t => Just t.pos

public export
atEnd : Stream -> Bool
atEnd s = s.index >= s.len

public export
remaining : Stream -> List Token
remaining s = buildFuel (integerToNat (cast (s.len - s.index))) s.index
  where
    buildFuel : Nat -> Int -> List Token
    buildFuel Z _ = []
    buildFuel (S k) i =
      if i >= s.len then []
      else MkToken (getTokKind s.buf i) (getTokPos s.buf i) :: buildFuel k (i + 1)

public export
at : Int -> Stream -> Maybe Token
at i s =
  if i < 0 || i >= s.len then Nothing
  else Just (MkToken (getTokKind s.buf i) (getTokPos s.buf i))

public export
withPeek : Stream -> Stream
withPeek s = MkStream s.buf s.len s.index (s.peekCount + 1) s.popCount s.expectCount

public export
withExpect : Stream -> Stream
withExpect s = MkStream s.buf s.len s.index s.peekCount s.popCount (s.expectCount + 1)

public export
stats : Stream -> (Int, Int, Int)
stats s = (s.peekCount, s.popCount, s.expectCount)
