module Ephapax.Parse.Parser

import Data.List
import Ephapax.Parse.Lexer
import Ephapax.Parse.Stream
import Ephapax.Parse.Util
import Ephapax.Parse.ZigBuffer
import Ephapax.IR.AST

%default partial

parseDecl : Parser Decl
parseFnDecl : Parser Decl
parseTypeDecl : Parser Decl
parseParams : Parser (List (String, Ty))
parseParam : Parser (String, Ty)

parseType : Parser Ty
parseSumType : Parser Ty
parseTypeAtom : Parser Ty

parseExpr : Parser Expr
parseLet : Bool -> Parser Expr
parseIf : Parser Expr
parseCase : Parser Expr
parseRegion : Parser Expr
parseLambda : Parser Expr
parseBinary : Int -> Parser Expr
parseUnary : Parser Expr
parsePostfix : Parser Expr
parsePrimary : Parser Expr
parseStringNew : Parser Expr
parseStringConcat : Parser Expr
parseStringLen : Parser Expr
parseDrop : Parser Expr
parseCopy : Parser Expr
parseInl : Parser Expr
parseInr : Parser Expr
parseParenOrPair : Parser Expr
parseOp : Stream -> Maybe (BinOp, Int, Stream)

parseModule : Stream -> Either ParseError (Module, Stream)
parseModule stream = do
  (decls, rest) <- many parseDecl stream
  case remaining rest of
    [] => Right (MkModule "input" decls, rest)
    _ => Left (PE ("unexpected tokens at end: " ++ show (remaining rest)) (posOf rest))

public export
parseModuleTokens : TokBuf -> Either ParseError Module
parseModuleTokens buf =
  case parseModule (fromBuffer buf) of
    Left err => Left err
    Right (m, _) => Right m

public export
parseModuleTokensWithStats : TokBuf -> Either ParseError (Module, (Int, Int, Int))
parseModuleTokensWithStats buf =
  case parseModule (fromBuffer buf) of
    Left err => Left err
    Right (m, s) => Right (m, stats s)

parseDecl toks =
  choice [parseFnDeclKw, parseTypeDeclKw] toks
  where
    parseFnDeclKw : Parser Decl
    parseFnDeclKw toks = do
      (_, rest) <- expectKw "fn" toks
      parseFnDecl rest

    parseTypeDeclKw : Parser Decl
    parseTypeDeclKw toks = do
      (_, rest) <- expectKw "type" toks
      parseTypeDecl rest

parseFnDecl stream = do
  (name, s1) <- expectIdent stream
  case peekTok s1 of
    Just t =>
      case t.kind of
        TkUnit => do
          (_, s2) <- expect TkUnit s1
          (_, s3) <- expect TkColon s2
          (retTy, s4) <- parseType s3
          (_, s5) <- expect TkEq s4
          (body, s6) <- parseExpr s5
          Right (Fn name [] retTy body, s6)
        _ => do
          (_, s2) <- expect TkLParen s1
          (params, s3) <- parseParams s2
          (_, s4) <- expect TkRParen s3
          (_, s5) <- expect TkColon s4
          (retTy, s6) <- parseType s5
          (_, s7) <- expect TkEq s6
          (body, s8) <- parseExpr s7
          Right (Fn name params retTy body, s8)
    Nothing => Left (PE "expected function parameters" (posOf s1))

parseTypeDecl stream = do
  (name, s1) <- expectIdent stream
  (_, s2) <- expect TkEq s1
  (ty, s3) <- parseType s2
  Right (TypeDecl name ty, s3)

parseParams stream = sepBy parseParam (expect TkComma) stream

parseParam stream = do
  (name, s1) <- expectIdent stream
  (_, s2) <- expect TkColon s1
  (ty, s3) <- parseType s2
  Right ((name, ty), s3)

parseType stream = do
  (lhs, s1) <- parseSumType stream
  case peekTok s1 of
    Just t =>
      case t.kind of
        TkArrow => do
          (_, s2) <- expect TkArrow s1
          (rhs, s3) <- parseType s2
          Right (Fun lhs rhs, s3)
        _ => Right (lhs, s1)
    Nothing => Right (lhs, s1)

parseSumType stream = do
  (parts, rest) <- sepBy1 parseTypeAtom (expect TkPlus) stream
  case parts of
    [] => Left (PE "expected type" (posOf stream))
    t :: ts => Right (foldl Sum t ts, rest)

parseTypeAtom stream =
  case peekTok stream of
    Nothing => Left (PE ("expected type (one of: " ++ typeStarts ++ ")") (posOf stream))
    Just t =>
      if isTypeStart t.kind then
        choice
          [ parseStringType
          , parseRegionType
          , parseBorrowType
          , parseProductType
          , parseBaseType
          , parseTypeVar
          ] stream
      else Left (PE ("expected type (one of: " ++ typeStarts ++ ")") (Just t.pos))
  where
    typeStarts : String
    typeStarts = "String, region, &, (, Bool, I32, I64, F32, F64, (), <ident>"

    isTypeStart : TokKind -> Bool
    isTypeStart k =
      case k of
        TkIdent _ => True
        TkKw "region" => True
        TkAmp => True
        TkLParen => True
        TkUnit => True
        _ => False
    parseStringType : Parser Ty
    parseStringType stream = do
      (_, s1) <- expectIdentEq "String" stream
      (_, s2) <- expect TkAt s1
      (r, s3) <- expectIdent s2
      Right (StringTy r, s3)

    parseRegionType : Parser Ty
    parseRegionType stream = do
      (_, s1) <- expectKw "region" stream
      (r, s2) <- expectIdent s1
      (_, s3) <- expect TkLBrace s2
      (inner, s4) <- parseType s3
      (_, s5) <- expect TkRBrace s4
      Right (Region r inner, s5)
    parseBorrowType : Parser Ty
    parseBorrowType stream =
      case peekTok stream of
        Just t =>
          case t.kind of
            TkAmp => do
              (_, s1) <- expect TkAmp stream
              (inner, s2) <- parseTypeAtom s1
              Right (Borrow inner, s2)
            _ => Left (PE "expected borrow type" (posOf stream))
        Nothing => Left (PE "expected borrow type" (posOf stream))

    parseProductType : Parser Ty
    parseProductType stream =
      case peekTok stream of
        Just t =>
          case t.kind of
            TkLParen => do
              (_, s1) <- expect TkLParen stream
              (left, s2) <- parseType s1
              (_, s3) <- expect TkComma s2
              (right, s4) <- parseType s3
              (_, s5) <- expect TkRParen s4
              Right (Prod left right, s5)
            _ => Left (PE "expected product type" (posOf stream))
        Nothing => Left (PE "expected product type" (posOf stream))

    parseBaseType : Parser Ty
    parseBaseType stream =
      choice
        [ \t => do { (_, r) <- expectIdentEq "Bool" t; Right (Base Bool, r) }
        , \t => do { (_, r) <- expectIdentEq "I32" t; Right (Base I32, r) }
        , \t => do { (_, r) <- expectIdentEq "I64" t; Right (Base I64, r) }
        , \t => do { (_, r) <- expectIdentEq "F32" t; Right (Base F32, r) }
        , \t => do { (_, r) <- expectIdentEq "F64" t; Right (Base F64, r) }
        , \t => do { (_, r) <- expect TkUnit t; Right (Base Unit, r) }
        ] stream

    parseTypeVar : Parser Ty
    parseTypeVar stream =
      case expectIdent stream of
        Right (v, rest) => Right (Var v, rest)
        Left _ => Left (PE "expected type variable" (posOf stream))

parseExpr stream =
  choice
    [ parseLetKw
    , parseLetLinKw
    , parseIfKw
    , parseCaseKw
    , parseRegionKw
    , parseLambdaKw
    , parseBinary 0
    ] stream
  where
    parseLetKw : Parser Expr
    parseLetKw stream = do
      (_, s1) <- expectKw "let" stream
      parseLet False s1

    parseLetLinKw : Parser Expr
    parseLetLinKw stream = do
      (_, s1) <- expectKw "let!" stream
      parseLet True s1

    parseIfKw : Parser Expr
    parseIfKw stream = do
      (_, s1) <- expectKw "if" stream
      parseIf s1

    parseCaseKw : Parser Expr
    parseCaseKw stream = do
      (_, s1) <- expectKw "case" stream
      parseCase s1

    parseRegionKw : Parser Expr
    parseRegionKw stream = do
      (_, s1) <- expectKw "region" stream
      parseRegion s1

    parseLambdaKw : Parser Expr
    parseLambdaKw stream = do
      (_, s1) <- expectKw "fn" stream
      parseLambda s1

parseLet isLin stream = do
  (name, s1) <- expectIdent stream
  (_, s2) <- expect TkEq s1
  (val, s3) <- parseExpr s2
  (_, s4) <- expectKw "in" s3
  (body, s5) <- parseExpr s4
  Right (if isLin then LetLin name Nothing val body else Let name Nothing val body, s5)

parseIf stream = do
  (cond, s1) <- parseExpr stream
  (_, s2) <- expectKw "then" s1
  (thenE, s3) <- parseExpr s2
  (_, s4) <- expectKw "else" s3
  (elseE, s5) <- parseExpr s4
  Right (If cond thenE elseE, s5)

parseCase stream = do
  (scrutinee, s1) <- parseExpr stream
  (_, s2) <- expectKw "of" s1
  (_, s3) <- expectKw "inl" s2
  (_, s4) <- expect TkLParen s3
  (lv, s5) <- expectIdent s4
  (_, s6) <- expect TkRParen s5
  (_, s7) <- expect TkArrow s6
  (lb, s8) <- parseExpr s7
  (_, s9) <- expectKw "inr" s8
  (_, s10) <- expect TkLParen s9
  (rv, s11) <- expectIdent s10
  (_, s12) <- expect TkRParen s11
  (_, s13) <- expect TkArrow s12
  (rb, s14) <- parseExpr s13
  Right (Case scrutinee (lv, lb) (rv, rb), s14)

parseRegion stream = do
  (name, s1) <- expectIdent stream
  (_, s2) <- expect TkLBrace s1
  (body, s3) <- parseExpr s2
  (_, s4) <- expect TkRBrace s3
  Right (RegionExpr name body, s4)

parseLambda stream = do
  (_, s1) <- expect TkLParen stream
  (param, s2) <- expectIdent s1
  (_, s3) <- expect TkColon s2
  (pty, s4) <- parseType s3
  (_, s5) <- expect TkRParen s4
  (_, s6) <- expect TkArrow s5
  (body, s7) <- parseExpr s6
  Right (Lambda param pty body, s7)

parseBinary minPrec stream = do
  (lhs, s1) <- parseUnary stream
  parseBinTail lhs minPrec s1
  where
    parseBinTail : Expr -> Int -> Parser Expr
    parseBinTail left prec stream =
      case parseOp stream of
        Nothing => Right (left, stream)
        Just (op, opPrec, rest) =>
          if opPrec < prec then Right (left, stream)
          else do
            (right, rest2) <- parseBinary (opPrec + 1) rest
            parseBinTail (BinOpE op left right) prec rest2

parseUnary stream =
  case peekTok stream of
    Just t =>
      case t.kind of
        TkBang => do
          (_, s1) <- expect TkBang stream
          (expr, s2) <- parseUnary s1
          Right (UnOpE Not expr, s2)
        TkMinus => do
          (_, s1) <- expect TkMinus stream
          (expr, s2) <- parseUnary s1
          Right (UnOpE Neg expr, s2)
        TkAmp => do
          (_, s1) <- expect TkAmp stream
          (expr, s2) <- parseUnary s1
          Right (BorrowE expr, s2)
        _ => parsePostfix stream
    Nothing => parsePostfix stream

parsePostfix stream = do
  (primary, s1) <- parsePrimary stream
  parsePostfixTail primary s1
  where
    mutual
      parsePostfixTail : Expr -> Parser Expr
      parsePostfixTail expr toks =
        choice
          [ parseCall expr
          , parseFst expr
          , parseSnd expr
          , \t => Right (expr, t)
          ] toks

      parseCall : Expr -> Parser Expr
      parseCall expr stream =
        case peekTok stream of
          Just t =>
            case t.kind of
              TkLParen => do
                (_, s1) <- expect TkLParen stream
                (arg, s2) <- parseExpr s1
                (_, s3) <- expect TkRParen s2
                parsePostfixTail (App expr arg) s3
              _ => Left (PE "expected call" (posOf stream))
          Nothing => Left (PE "expected call" (posOf stream))

      parseFst : Expr -> Parser Expr
      parseFst expr stream =
        case popTok stream of
          Just (t1, s1) =>
            case t1.kind of
              TkDot =>
                case popTok s1 of
                  Just (t2, s2) =>
                    case t2.kind of
                      TkInt "0" => parsePostfixTail (Fst expr) s2
                      _ => Left (PE "expected .0" (Just t2.pos))
                  Nothing => Left (PE "expected .0" (posOf s1))
              _ => Left (PE "expected .0" (Just t1.pos))
          Nothing => Left (PE "expected .0" (posOf stream))

      parseSnd : Expr -> Parser Expr
      parseSnd expr stream =
        case popTok stream of
          Just (t1, s1) =>
            case t1.kind of
              TkDot =>
                case popTok s1 of
                  Just (t2, s2) =>
                    case t2.kind of
                      TkInt "1" => parsePostfixTail (Snd expr) s2
                      _ => Left (PE "expected .1" (Just t2.pos))
                  Nothing => Left (PE "expected .1" (posOf s1))
              _ => Left (PE "expected .1" (Just t1.pos))
          Nothing => Left (PE "expected .1" (posOf stream))

parsePrimary stream =
  case peekTok stream of
    Nothing => Left (PE ("expected primary expression (one of: " ++ exprStarts ++ ")") (posOf stream))
    Just t =>
      if isExprStart t.kind then
        choice
          [ parseStringNew
          , parseStringConcat
          , parseStringLen
          , parseDrop
          , parseCopy
          , parseInl
          , parseInr
          , parseParenOrPair
          , parseLiteral
          , parseVar
          ] stream
      else Left (PE ("expected primary expression (one of: " ++ exprStarts ++ ")") (Just t.pos))
  where
    exprStarts : String
    exprStarts = "<ident>, literal, (, drop, copy, inl, inr"

    isExprStart : TokKind -> Bool
    isExprStart k =
      case k of
        TkIdent _ => True
        TkInt _ => True
        TkFloat _ => True
        TkString _ => True
        TkBool _ => True
        TkUnit => True
        TkLParen => True
        TkKw "drop" => True
        TkKw "copy" => True
        TkKw "inl" => True
        TkKw "inr" => True
        _ => False
    isLiteral : Token -> Bool
    isLiteral tok =
      case tok.kind of
        TkInt _ => True
        TkFloat _ => True
        TkString _ => True
        TkBool _ => True
        TkUnit => True
        _ => False

    parseLiteral : Parser Expr
    parseLiteral stream = do
      (tok, rest) <- satisfy isLiteral stream
      case tok.kind of
        TkInt n => Right (Lit (LI32 n), rest)
        TkFloat n => Right (Lit (LF64 n), rest)
        TkString s => Right (Lit (LString s), rest)
        TkBool b => Right (Lit (LBool b), rest)
        TkUnit => Right (Lit LUnit, rest)
        _ => Left (PE "expected literal" (posOf stream))

    parseVar : Parser Expr
    parseVar stream = do
      (name, rest) <- expectIdent stream
      Right (VarE name, rest)

parseStringNew stream = do
  (_, s1) <- expectIdentEq "String.new" stream
  (_, s2) <- expect TkAt s1
  (r, s3) <- expectIdent s2
  (_, s4) <- expect TkLParen s3
  (s, s5) <- expectString s4
  (_, s6) <- expect TkRParen s5
  Right (StringNew r s, s6)

parseStringConcat stream = do
  (_, s1) <- expectIdentEq "String.concat" stream
  (_, s2) <- expect TkLParen s1
  (a, s3) <- parseExpr s2
  (_, s4) <- expect TkComma s3
  (b, s5) <- parseExpr s4
  (_, s6) <- expect TkRParen s5
  Right (StringConcat a b, s6)

parseStringLen stream = do
  (_, s1) <- expectIdentEq "String.len" stream
  (_, s2) <- expect TkLParen s1
  (a, s3) <- parseExpr s2
  (_, s4) <- expect TkRParen s3
  Right (StringLen a, s4)

parseDrop stream = do
  (_, s1) <- expectKw "drop" stream
  (_, s2) <- expect TkLParen s1
  (a, s3) <- parseExpr s2
  (_, s4) <- expect TkRParen s3
  Right (Drop a, s4)

parseCopy stream = do
  (_, s1) <- expectKw "copy" stream
  (_, s2) <- expect TkLParen s1
  (a, s3) <- parseExpr s2
  (_, s4) <- expect TkRParen s3
  Right (Copy a, s4)

parseInl stream = do
  (_, s1) <- expectKw "inl" stream
  (_, s2) <- expect TkLBracket s1
  (ty, s3) <- parseType s2
  (_, s4) <- expect TkRBracket s3
  (_, s5) <- expect TkLParen s4
  (e, s6) <- parseExpr s5
  (_, s7) <- expect TkRParen s6
  Right (Inl ty e, s7)

parseInr stream = do
  (_, s1) <- expectKw "inr" stream
  (_, s2) <- expect TkLBracket s1
  (ty, s3) <- parseType s2
  (_, s4) <- expect TkRBracket s3
  (_, s5) <- expect TkLParen s4
  (e, s6) <- parseExpr s5
  (_, s7) <- expect TkRParen s6
  Right (Inr ty e, s7)

parseParenOrPair stream =
  case peekTok stream of
    Just t =>
      case t.kind of
        TkLParen => do
          (_, s1) <- expect TkLParen stream
          (first, s2) <- parseExpr s1
          case peekTok s2 of
            Just t2 =>
              case t2.kind of
                TkComma => do
                  (_, s3) <- expect TkComma s2
                  (second, s4) <- parseExpr s3
                  (_, s5) <- expect TkRParen s4
                  Right (Pair first second, s5)
                _ => do
                  (_, s3) <- expect TkRParen s2
                  Right (first, s3)
            Nothing => Left (PE "expected parenthesized expression" (posOf s2))
        _ => Left (PE "expected parenthesized expression" (posOf stream))
    Nothing => Left (PE "expected parenthesized expression" (posOf stream))

parseOp stream =
  case peekTok stream of
    Just t =>
      case t.kind of
        TkOrOr => consume Or 1 TkOrOr
        TkAndAnd => consume And 2 TkAndAnd
        TkEqEq => consume Eq 3 TkEqEq
        TkNe => consume Ne 3 TkNe
        TkLt => consume Lt 4 TkLt
        TkLe => consume Le 4 TkLe
        TkGt => consume Gt 4 TkGt
        TkGe => consume Ge 4 TkGe
        TkPlus => consume Add 5 TkPlus
        TkMinus => consume Sub 5 TkMinus
        TkStar => consume Mul 6 TkStar
        TkSlash => consume Div 6 TkSlash
        TkPercent => consume Mod 6 TkPercent
        _ => Nothing
    Nothing => Nothing
  where
    consume : BinOp -> Int -> TokKind -> Maybe (BinOp, Int, Stream)
    consume op prec kind =
      case expect kind stream of
        Right (_, rest) => Just (op, prec, rest)
        Left _ => Nothing

-- expect/expectKw/expectIdent/many moved to Ephapax.Parse.Util
