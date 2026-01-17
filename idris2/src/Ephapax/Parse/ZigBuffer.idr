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
    TkSemi => (16, "", 0, 0)
    TkArrow => (17, "", 0, 0)
    TkAt => (18, "", 0, 0)
    TkDot => (19, "", 0, 0)
    TkEq => (20, "", 0, 0)
    TkPlus => (21, "", 0, 0)
    TkMinus => (22, "", 0, 0)
    TkStar => (23, "", 0, 0)
    TkSlash => (24, "", 0, 0)
    TkPercent => (25, "", 0, 0)
    TkEqEq => (26, "", 0, 0)
    TkNe => (27, "", 0, 0)
    TkLt => (28, "", 0, 0)
    TkLe => (29, "", 0, 0)
    TkGt => (30, "", 0, 0)
    TkGe => (31, "", 0, 0)
    TkAndAnd => (32, "", 0, 0)
    TkOrOr => (33, "", 0, 0)
    TkBang => (34, "", 0, 0)
    TkAmp => (35, "", 0, 0)

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
    16 => TkSemi
    17 => TkArrow
    18 => TkAt
    19 => TkDot
    20 => TkEq
    21 => TkPlus
    22 => TkMinus
    23 => TkStar
    24 => TkSlash
    25 => TkPercent
    26 => TkEqEq
    27 => TkNe
    28 => TkLt
    29 => TkLe
    30 => TkGt
    31 => TkGe
    32 => TkAndAnd
    33 => TkOrOr
    34 => TkBang
    35 => TkAmp
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
