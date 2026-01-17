module Ephapax.Parse.ZigBuffer

import System
import Ephapax.Parse.Lexer

%default total

public export
data TokBuf : Type where
  MkTokBuf : AnyPtr -> TokBuf

%foreign "C:eph_tokbuf_new,libephapax_tokbuf"
prim__tokbuf_new : Int -> AnyPtr

%foreign "C:eph_tokbuf_free,libephapax_tokbuf"
prim__tokbuf_free : AnyPtr -> PrimIO ()

%foreign "C:eph_tokbuf_push,libephapax_tokbuf"
prim__tokbuf_push : AnyPtr -> Int -> String -> Int -> Int -> Int -> Int -> PrimIO ()

%foreign "C:eph_tokbuf_len,libephapax_tokbuf"
prim__tokbuf_len : AnyPtr -> Int

%foreign "C:eph_tokbuf_kind,libephapax_tokbuf"
prim__tokbuf_kind : AnyPtr -> Int -> Int

%foreign "C:eph_tokbuf_str_ptr,libephapax_tokbuf"
prim__tokbuf_str : AnyPtr -> Int -> String

%foreign "C:eph_tokbuf_str_len,libephapax_tokbuf"
prim__tokbuf_str_len : AnyPtr -> Int -> Int

%foreign "C:eph_tokbuf_bool,libephapax_tokbuf"
prim__tokbuf_bool : AnyPtr -> Int -> Int

%foreign "C:eph_tokbuf_line,libephapax_tokbuf"
prim__tokbuf_line : AnyPtr -> Int -> Int

%foreign "C:eph_tokbuf_col,libephapax_tokbuf"
prim__tokbuf_col : AnyPtr -> Int -> Int

public export
newBuf : Int -> TokBuf
newBuf cap = MkTokBuf (prim__tokbuf_new cap)

public export
freeBuf : TokBuf -> IO ()
freeBuf (MkTokBuf p) = primIO (prim__tokbuf_free p)

public export
bufLen : TokBuf -> Int
bufLen (MkTokBuf p) = prim__tokbuf_len p

strLen : String -> Int
strLen s = cast (length (unpack s))

encodeKind : TokKind -> (Int, String, Int, Int)
encodeKind k =
  case k of
    TkIdent s => (1, s, strLen s, 0)
    TkInt s => (2, s, strLen s, 0)
    TkFloat s => (3, s, strLen s, 0)
    TkString s => (4, s, strLen s, 0)
    TkBool b => (5, "", 0, if b then 1 else 0)
    TkUnit => (6, "", 0, 0)
    TkKw s => (7, s, strLen s, 0)
    TkLParen => (8, "", 0, 0)
    TkRParen => (9, "", 0, 0)
    TkLBrace => (10, "", 0, 0)
    TkRBrace => (11, "", 0, 0)
    TkLBracket => (12, "", 0, 0)
    TkRBracket => (13, "", 0, 0)
    TkComma => (14, "", 0, 0)
    TkColon => (15, "", 0, 0)
    TkArrow => (16, "", 0, 0)
    TkAt => (17, "", 0, 0)
    TkDot => (18, "", 0, 0)
    TkEq => (19, "", 0, 0)
    TkPlus => (20, "", 0, 0)
    TkMinus => (21, "", 0, 0)
    TkStar => (22, "", 0, 0)
    TkSlash => (23, "", 0, 0)
    TkPercent => (24, "", 0, 0)
    TkEqEq => (25, "", 0, 0)
    TkNe => (26, "", 0, 0)
    TkLt => (27, "", 0, 0)
    TkLe => (28, "", 0, 0)
    TkGt => (29, "", 0, 0)
    TkGe => (30, "", 0, 0)
    TkAndAnd => (31, "", 0, 0)
    TkOrOr => (32, "", 0, 0)
    TkBang => (33, "", 0, 0)
    TkAmp => (34, "", 0, 0)

decodeKind : Int -> String -> Int -> TokKind
decodeKind tag s b =
  case tag of
    1 => TkIdent s
    2 => TkInt s
    3 => TkFloat s
    4 => TkString s
    5 => TkBool (b == 1)
    6 => TkUnit
    7 => TkKw s
    8 => TkLParen
    9 => TkRParen
    10 => TkLBrace
    11 => TkRBrace
    12 => TkLBracket
    13 => TkRBracket
    14 => TkComma
    15 => TkColon
    16 => TkArrow
    17 => TkAt
    18 => TkDot
    19 => TkEq
    20 => TkPlus
    21 => TkMinus
    22 => TkStar
    23 => TkSlash
    24 => TkPercent
    25 => TkEqEq
    26 => TkNe
    27 => TkLt
    28 => TkLe
    29 => TkGt
    30 => TkGe
    31 => TkAndAnd
    32 => TkOrOr
    33 => TkBang
    34 => TkAmp
    _ => TkIdent s

public export
pushTok : TokBuf -> TokKind -> Pos -> IO ()
pushTok (MkTokBuf p) kind pos =
  let (tag, s, sLen, b) = encodeKind kind in
  primIO (prim__tokbuf_push p tag s sLen b pos.line pos.col)

public export
getTokKind : TokBuf -> Int -> TokKind
getTokKind (MkTokBuf p) idx = decodeKind (prim__tokbuf_kind p idx) (prim__tokbuf_str p idx) (prim__tokbuf_bool p idx)

public export
getTokPos : TokBuf -> Int -> Pos
getTokPos (MkTokBuf p) idx = MkPos (prim__tokbuf_line p idx) (prim__tokbuf_col p idx)
