module Ephapax.IR.Decode

import Data.List
import Data.String
import Ephapax.IR.SExpr
import Ephapax.IR.AST

%default partial

baseToAtom : BaseTy -> String
baseToAtom Unit = "unit"
baseToAtom Bool = "bool"
baseToAtom I32 = "i32"
baseToAtom I64 = "i64"
baseToAtom F32 = "f32"
baseToAtom F64 = "f64"

atomToBase : String -> Either ParseError BaseTy
atomToBase "unit" = Right Unit
atomToBase "bool" = Right Bool
atomToBase "i32" = Right I32
atomToBase "i64" = Right I64
atomToBase "f32" = Right F32
atomToBase "f64" = Right F64
atomToBase _ = Left (Invalid "unknown base type")

linearityToAtom : Linearity -> String
linearityToAtom Linear = "linear"
linearityToAtom Unrestricted = "unrestricted"

atomToLinearity : String -> Either ParseError Linearity
atomToLinearity "linear" = Right Linear
atomToLinearity "unrestricted" = Right Unrestricted
atomToLinearity _ = Left (Invalid "unknown linearity")

binopToAtom : BinOp -> String
binopToAtom Add = "add"
binopToAtom Sub = "sub"
binopToAtom Mul = "mul"
binopToAtom Div = "div"
binopToAtom Mod = "mod"
binopToAtom Lt = "lt"
binopToAtom Le = "le"
binopToAtom Gt = "gt"
binopToAtom Ge = "ge"
binopToAtom Eq = "eq"
binopToAtom Ne = "ne"
binopToAtom And = "and"
binopToAtom Or = "or"

atomToBinop : String -> Either ParseError BinOp
atomToBinop "add" = Right Add
atomToBinop "sub" = Right Sub
atomToBinop "mul" = Right Mul
atomToBinop "div" = Right Div
atomToBinop "mod" = Right Mod
atomToBinop "lt" = Right Lt
atomToBinop "le" = Right Le
atomToBinop "gt" = Right Gt
atomToBinop "ge" = Right Ge
atomToBinop "eq" = Right Eq
atomToBinop "ne" = Right Ne
atomToBinop "and" = Right And
atomToBinop "or" = Right Or
atomToBinop _ = Left (Invalid "unknown binop")

unaryToAtom : UnaryOp -> String
unaryToAtom Not = "not"
unaryToAtom Neg = "neg"

atomToUnary : String -> Either ParseError UnaryOp
atomToUnary "not" = Right Not
atomToUnary "neg" = Right Neg
atomToUnary _ = Left (Invalid "unknown unary op")

escape : String -> String
escape s =
  pack (go (unpack s))
  where
    esc : Char -> List Char
    esc '\n' = ['\\', 'n']
    esc '\t' = ['\\', 't']
    esc '\r' = ['\\', 'r']
    esc '"' = ['\\', '"']
    esc '\\' = ['\\', '\\']
    esc c = [c]

    go : List Char -> List Char
    go [] = []
    go (c :: rest) = esc c ++ go rest

unescape : String -> String
unescape s =
  decode (unpack s)
  where
    unesc : Char -> Char
    unesc 'n' = '\n'
    unesc 't' = '\t'
    unesc 'r' = '\r'
    unesc '"' = '"'
    unesc '\\' = '\\'
    unesc c = c

    decode : List Char -> String
    decode [] = ""
    decode ('\\' :: c :: rest) = pack [unesc c] ++ decode rest
    decode (c :: rest) = pack [c] ++ decode rest

encodeLit : Literal -> SExpr
encodeLit LUnit = Atom "unit"
encodeLit (LBool v) = List [Atom "bool", Atom (if v then "true" else "false")]
encodeLit (LI32 v) = List [Atom "i32", Atom v]
encodeLit (LI64 v) = List [Atom "i64", Atom v]
encodeLit (LF32 v) = List [Atom "f32", Atom v]
encodeLit (LF64 v) = List [Atom "f64", Atom v]
encodeLit (LString s) = List [Atom "string", Atom (escape s)]

decodeLit : SExpr -> Either ParseError Literal
decodeLit (Atom "unit") = pure LUnit
decodeLit (List [Atom "bool", Atom v]) = pure (LBool (v == "true"))
decodeLit (List [Atom "i32", Atom v]) = pure (LI32 v)
decodeLit (List [Atom "i64", Atom v]) = pure (LI64 v)
decodeLit (List [Atom "f32", Atom v]) = pure (LF32 v)
decodeLit (List [Atom "f64", Atom v]) = pure (LF64 v)
decodeLit (List [Atom "string", Atom v]) = pure (LString (unescape v))
decodeLit _ = Left (Invalid "unknown literal")

encodeTy : Ty -> SExpr
encodeTy (Base b) = List [Atom "base", Atom (baseToAtom b)]
encodeTy (StringTy r) = List [Atom "string", Atom r]
encodeTy (Ref lin inner) =
  List [Atom "ref", Atom (linearityToAtom lin), encodeTy inner]
encodeTy (Fun a b) = List [Atom "fun", encodeTy a, encodeTy b]
encodeTy (Prod a b) = List [Atom "prod", encodeTy a, encodeTy b]
encodeTy (Sum a b) = List [Atom "sum", encodeTy a, encodeTy b]
encodeTy (Region r t) = List [Atom "region-type", Atom r, encodeTy t]
encodeTy (Borrow t) = List [Atom "borrow", encodeTy t]
encodeTy (Var v) = List [Atom "var", Atom v]

decodeTy : SExpr -> Either ParseError Ty
decodeTy (List [Atom "base", Atom b]) = do
  base <- atomToBase b
  pure (Base base)
decodeTy (List [Atom "string", Atom r]) = pure (StringTy r)
decodeTy (List [Atom "ref", Atom lin, inner]) = do
  linearity <- atomToLinearity lin
  innerTy <- decodeTy inner
  pure (Ref linearity innerTy)
decodeTy (List [Atom "fun", a, b]) = pure (Fun !(decodeTy a) !(decodeTy b))
decodeTy (List [Atom "prod", a, b]) = pure (Prod !(decodeTy a) !(decodeTy b))
decodeTy (List [Atom "sum", a, b]) = pure (Sum !(decodeTy a) !(decodeTy b))
decodeTy (List [Atom "region-type", Atom r, inner]) = pure (Region r !(decodeTy inner))
decodeTy (List [Atom "borrow", inner]) = pure (Borrow !(decodeTy inner))
decodeTy (List [Atom "var", Atom v]) = pure (Var v)
decodeTy _ = Left (Invalid "unknown type")

encodeExpr : Expr -> SExpr
encodeExpr (Lit lit) = List [Atom "lit", encodeLit lit]
encodeExpr (VarE name) = List [Atom "var", Atom name]
encodeExpr (StringNew r v) = List [Atom "string-new", Atom r, Atom (escape v)]
encodeExpr (StringConcat a b) = List [Atom "string-concat", encodeExpr a, encodeExpr b]
encodeExpr (StringLen e) = List [Atom "string-len", encodeExpr e]
encodeExpr (Let n _ v b) = List [Atom "let", Atom n, encodeExpr v, encodeExpr b]
encodeExpr (LetLin n _ v b) = List [Atom "letlin", Atom n, encodeExpr v, encodeExpr b]
encodeExpr (Lambda p ty body) = List [Atom "lambda", Atom p, encodeTy ty, encodeExpr body]
encodeExpr (App f a) = List [Atom "app", encodeExpr f, encodeExpr a]
encodeExpr (Pair a b) = List [Atom "pair", encodeExpr a, encodeExpr b]
encodeExpr (Fst e) = List [Atom "fst", encodeExpr e]
encodeExpr (Snd e) = List [Atom "snd", encodeExpr e]
encodeExpr (Inl ty e) = List [Atom "inl", encodeTy ty, encodeExpr e]
encodeExpr (Inr ty e) = List [Atom "inr", encodeTy ty, encodeExpr e]
encodeExpr (Case scr (lv, lb) (rv, rb)) =
  List [Atom "case", encodeExpr scr, List [Atom lv, encodeExpr lb], List [Atom rv, encodeExpr rb]]
encodeExpr (If c t f) = List [Atom "if", encodeExpr c, encodeExpr t, encodeExpr f]
encodeExpr (RegionExpr r e) = List [Atom "region", Atom r, encodeExpr e]
encodeExpr (BorrowE e) = List [Atom "borrow", encodeExpr e]
encodeExpr (Deref e) = List [Atom "deref", encodeExpr e]
encodeExpr (Drop e) = List [Atom "drop", encodeExpr e]
encodeExpr (Copy e) = List [Atom "copy", encodeExpr e]
encodeExpr (Block es) = List (Atom "block" :: map encodeExpr es)
encodeExpr (BinOpE op a b) = List [Atom "binop", Atom (binopToAtom op), encodeExpr a, encodeExpr b]
encodeExpr (UnOpE op e) = List [Atom "unop", Atom (unaryToAtom op), encodeExpr e]

decodeExpr : SExpr -> Either ParseError Expr
decodeExpr (List (Atom tag :: rest)) =
  case tag of
    "lit" => case rest of
      [lit] => pure (Lit !(decodeLit lit))
      _ => Left (Invalid "(lit ...) shape")
    "var" => case rest of
      [Atom n] => pure (VarE n)
      _ => Left (Invalid "(var name)")
    "string-new" => case rest of
      [Atom r, Atom s] => pure (StringNew r (unescape s))
      _ => Left (Invalid "(string-new r \"s\")")
    "string-concat" => case rest of
      [a, b] => pure (StringConcat !(decodeExpr a) !(decodeExpr b))
      _ => Left (Invalid "(string-concat a b)")
    "string-len" => case rest of
      [a] => pure (StringLen !(decodeExpr a))
      _ => Left (Invalid "(string-len a)")
    "let" => case rest of
      [Atom n, v, b] => pure (Let n Nothing !(decodeExpr v) !(decodeExpr b))
      _ => Left (Invalid "(let n v b)")
    "letlin" => case rest of
      [Atom n, v, b] => pure (LetLin n Nothing !(decodeExpr v) !(decodeExpr b))
      _ => Left (Invalid "(letlin n v b)")
    "lambda" => case rest of
      [Atom p, ty, b] => pure (Lambda p !(decodeTy ty) !(decodeExpr b))
      _ => Left (Invalid "(lambda p ty body)")
    "app" => case rest of
      [f, a] => pure (App !(decodeExpr f) !(decodeExpr a))
      _ => Left (Invalid "(app f a)")
    "pair" => case rest of
      [a, b] => pure (Pair !(decodeExpr a) !(decodeExpr b))
      _ => Left (Invalid "(pair a b)")
    "fst" => case rest of
      [e] => pure (Fst !(decodeExpr e))
      _ => Left (Invalid "(fst e)")
    "snd" => case rest of
      [e] => pure (Snd !(decodeExpr e))
      _ => Left (Invalid "(snd e)")
    "inl" => case rest of
      [ty, e] => pure (Inl !(decodeTy ty) !(decodeExpr e))
      _ => Left (Invalid "(inl ty e)")
    "inr" => case rest of
      [ty, e] => pure (Inr !(decodeTy ty) !(decodeExpr e))
      _ => Left (Invalid "(inr ty e)")
    "case" => case rest of
      [scr, List [Atom lv, lb], List [Atom rv, rb]] =>
        pure (Case !(decodeExpr scr) (lv, !(decodeExpr lb)) (rv, !(decodeExpr rb)))
      _ => Left (Invalid "(case scr (x e1) (y e2))")
    "if" => case rest of
      [c, t, f] => pure (If !(decodeExpr c) !(decodeExpr t) !(decodeExpr f))
      _ => Left (Invalid "(if c t f)")
    "region" => case rest of
      [Atom r, e] => pure (RegionExpr r !(decodeExpr e))
      _ => Left (Invalid "(region r e)")
    "borrow" => case rest of
      [e] => pure (BorrowE !(decodeExpr e))
      _ => Left (Invalid "(borrow e)")
    "deref" => case rest of
      [e] => pure (Deref !(decodeExpr e))
      _ => Left (Invalid "(deref e)")
    "drop" => case rest of
      [e] => pure (Drop !(decodeExpr e))
      _ => Left (Invalid "(drop e)")
    "copy" => case rest of
      [e] => pure (Copy !(decodeExpr e))
      _ => Left (Invalid "(copy e)")
    "block" => pure (Block !(traverse decodeExpr rest))
    "binop" => case rest of
      [Atom op, a, b] =>
        case atomToBinop op of
          Left err => Left err
          Right bop => pure (BinOpE bop !(decodeExpr a) !(decodeExpr b))
      _ => Left (Invalid "(binop op a b)")
    "unop" => case rest of
      [Atom op, e] =>
        case atomToUnary op of
          Left err => Left err
          Right uop => pure (UnOpE uop !(decodeExpr e))
      _ => Left (Invalid "(unop op e)")
    _ => Left (Invalid ("unknown expr tag: " ++ tag))
decodeExpr _ = Left (Invalid "expected expr list")

encodeParam : (String, Ty) -> SExpr
encodeParam (name, ty) = List [Atom name, encodeTy ty]

decodeParam : SExpr -> Either ParseError (String, Ty)
decodeParam (List [Atom name, ty]) = do
  t <- decodeTy ty
  pure (name, t)
decodeParam _ = Left (Invalid "param must be (name ty)")

encodeDecl : Decl -> SExpr
encodeDecl (Fn name params ret body) =
  List [Atom "fn", Atom name, List (map encodeParam params), encodeTy ret, encodeExpr body]
encodeDecl (TypeDecl name ty) =
  List [Atom "type", Atom name, encodeTy ty]

decodeDecl : SExpr -> Either ParseError Decl
decodeDecl (List (Atom "fn" :: Atom name :: List params :: ret :: body :: [])) = do
  ps <- traverse decodeParam params
  rty <- decodeTy ret
  expr <- decodeExpr body
  pure (Fn name ps rty expr)
decodeDecl (List (Atom "type" :: Atom name :: ty :: [])) = do
  t <- decodeTy ty
  pure (TypeDecl name t)
decodeDecl _ = Left (Invalid "unknown decl")

public export
fromSExpr : SExpr -> Either ParseError Module
fromSExpr (List (Atom "module" :: Atom name :: List decls :: [])) = do
  ds <- traverse decodeDecl decls
  pure (MkModule name ds)
fromSExpr _ = Left (Invalid "expected (module name (decls...))")

public export
toSExpr : Module -> SExpr
toSExpr (MkModule name decls) =
  List [Atom "module", Atom name, List (map encodeDecl decls)]

public export
encode : Module -> String
encode = show . toSExpr
