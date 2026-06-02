-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.Parse.Lexer

import Data.List

%default total

public export
record Pos where
  constructor MkPos
  line : Int
  col : Int

public export
data TokKind
  = TkIdent String
  | TkInt String
  | TkFloat String
  | TkString String
  | TkBool Bool
  | TkUnit
  | TkKw String
  | TkLParen | TkRParen
  | TkLBrace | TkRBrace
  | TkLBracket | TkRBracket
  | TkComma | TkColon | TkSemi | TkArrow | TkAt | TkDot | TkEq
  | TkPlus | TkMinus | TkStar | TkSlash | TkPercent
  | TkEqEq | TkNe | TkLt | TkLe | TkGt | TkGe
  | TkAndAnd | TkOrOr | TkBang | TkAmp

public export
Eq TokKind where
  (==) (TkIdent a) (TkIdent b) = a == b
  (==) (TkInt a) (TkInt b) = a == b
  (==) (TkFloat a) (TkFloat b) = a == b
  (==) (TkString a) (TkString b) = a == b
  (==) (TkBool a) (TkBool b) = a == b
  (==) TkUnit TkUnit = True
  (==) (TkKw a) (TkKw b) = a == b
  (==) TkLParen TkLParen = True
  (==) TkRParen TkRParen = True
  (==) TkLBrace TkLBrace = True
  (==) TkRBrace TkRBrace = True
  (==) TkLBracket TkLBracket = True
  (==) TkRBracket TkRBracket = True
  (==) TkComma TkComma = True
  (==) TkColon TkColon = True
  (==) TkSemi TkSemi = True
  (==) TkArrow TkArrow = True
  (==) TkAt TkAt = True
  (==) TkDot TkDot = True
  (==) TkEq TkEq = True
  (==) TkPlus TkPlus = True
  (==) TkMinus TkMinus = True
  (==) TkStar TkStar = True
  (==) TkSlash TkSlash = True
  (==) TkPercent TkPercent = True
  (==) TkEqEq TkEqEq = True
  (==) TkNe TkNe = True
  (==) TkLt TkLt = True
  (==) TkLe TkLe = True
  (==) TkGt TkGt = True
  (==) TkGe TkGe = True
  (==) TkAndAnd TkAndAnd = True
  (==) TkOrOr TkOrOr = True
  (==) TkBang TkBang = True
  (==) TkAmp TkAmp = True
  (==) _ _ = False

public export
Show TokKind where
  show (TkIdent s) = "TkIdent " ++ show s
  show (TkInt s) = "TkInt " ++ show s
  show (TkFloat s) = "TkFloat " ++ show s
  show (TkString s) = "TkString " ++ show s
  show (TkBool b) = "TkBool " ++ show b
  show TkUnit = "TkUnit"
  show (TkKw s) = "TkKw " ++ show s
  show TkLParen = "TkLParen"
  show TkRParen = "TkRParen"
  show TkLBrace = "TkLBrace"
  show TkRBrace = "TkRBrace"
  show TkLBracket = "TkLBracket"
  show TkRBracket = "TkRBracket"
  show TkComma = "TkComma"
  show TkColon = "TkColon"
  show TkSemi = "TkSemi"
  show TkArrow = "TkArrow"
  show TkAt = "TkAt"
  show TkDot = "TkDot"
  show TkEq = "TkEq"
  show TkPlus = "TkPlus"
  show TkMinus = "TkMinus"
  show TkStar = "TkStar"
  show TkSlash = "TkSlash"
  show TkPercent = "TkPercent"
  show TkEqEq = "TkEqEq"
  show TkNe = "TkNe"
  show TkLt = "TkLt"
  show TkLe = "TkLe"
  show TkGt = "TkGt"
  show TkGe = "TkGe"
  show TkAndAnd = "TkAndAnd"
  show TkOrOr = "TkOrOr"
  show TkBang = "TkBang"
  show TkAmp = "TkAmp"

public export
record Token where
  constructor MkToken
  kind : TokKind
  pos : Pos

public export
Show Token where
  show (MkToken k (MkPos l c)) =
    show k ++ "@" ++ show l ++ ":" ++ show c

public export
data LexError
  = UnexpectedChar Char Pos
  | UnterminatedString

public export
Show LexError where
  show (UnexpectedChar c (MkPos l col)) =
    "unexpected character: " ++ pack [c] ++ " at " ++ show l ++ ":" ++ show col
  show UnterminatedString = "unterminated string literal"

public export
lex : String -> Either LexError (List Token)
lex input =
  let cs = unpack input in
  go (length cs) (MkPos 1 1) cs []
  where
    isSpaceChar : Char -> Bool
    isSpaceChar ch = ch == ' ' || ch == '\t' || ch == '\r'

    isAlphaChar : Char -> Bool
    isAlphaChar ch =
      (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')

    isDigitChar : Char -> Bool
    isDigitChar ch = ch >= '0' && ch <= '9'

    isAlphaNumChar : Char -> Bool
    isAlphaNumChar ch = isAlphaChar ch || isDigitChar ch

    isIdentChar : Char -> Bool
    isIdentChar ch = isAlphaNumChar ch || ch == '_' || ch == '\''

    isNumChar : Char -> Bool
    isNumChar ch = isDigitChar ch || ch == '.'

    unescape : Char -> Char
    unescape 'n' = '\n'
    unescape 't' = '\t'
    unescape 'r' = '\r'
    unescape '"' = '"'
    unescape '\\' = '\\'
    unescape c = c

    advance : Pos -> Char -> Pos
    advance (MkPos l c) ch =
      if ch == '\n' then MkPos (l + 1) 1 else MkPos l (c + 1)

    advanceN : Pos -> List Char -> Pos
    advanceN pos [] = pos
    advanceN pos (x :: xs) = advanceN (advance pos x) xs

    readString : Pos -> List Char -> Either LexError (String, List Char, Pos)
    readString pos cs = goStr pos [] cs
      where
        goStr : Pos -> List Char -> List Char -> Either LexError (String, List Char, Pos)
        goStr _ acc [] = Left UnterminatedString
        goStr pos acc ('"' :: rest) = Right (pack (reverse acc), rest, advance pos '"')
        goStr pos acc ('\\' :: c :: rest) =
          let pos' = advanceN pos ['\\', c] in
          goStr pos' (unescape c :: acc) rest
        goStr pos acc (c :: rest) = goStr (advance pos c) (c :: acc) rest

    go : Nat -> Pos -> List Char -> List Token -> Either LexError (List Token)
    go Z _ _ acc = Right (reverse acc)
    go (S k) _ [] acc = Right (reverse acc)
    go (S k) pos ('-' :: '-' :: rest) acc =
      let (skipped, more) = span (/= '\n') rest in
      let (consumed, tail) = case more of
            '\n' :: tail' => (skipped ++ ['\n'], tail')
            _ => (skipped, more)
      in go k (advanceN pos ('-' :: '-' :: consumed)) tail acc
    go (S k) pos (c :: rest) acc =
      if isSpaceChar c then go k (advance pos c) rest acc
      else if c == '\n' then
        let nextPos = advance pos c in
        go k nextPos rest (MkToken TkSemi pos :: acc)
      else if isAlphaChar c || c == '_' then
        let (identChars, more) = span isIdentChar (c :: rest) in
        let ident = pack identChars in
        let tokPos = pos in
        let nextPos = advanceN pos identChars in
        case ident of
          "true" => go k nextPos more (MkToken (TkBool True) tokPos :: acc)
          "false" => go k nextPos more (MkToken (TkBool False) tokPos :: acc)
          "let" =>
            case more of
              '!' :: tail =>
                let nextPos2 = advance nextPos '!' in
                go k nextPos2 tail (MkToken (TkKw "let!") tokPos :: acc)
              _ => go k nextPos more (MkToken (TkKw "let") tokPos :: acc)
          "fn" => go k nextPos more (MkToken (TkKw "fn") tokPos :: acc)
          "if" => go k nextPos more (MkToken (TkKw "if") tokPos :: acc)
          "then" => go k nextPos more (MkToken (TkKw "then") tokPos :: acc)
          "else" => go k nextPos more (MkToken (TkKw "else") tokPos :: acc)
          "in" => go k nextPos more (MkToken (TkKw "in") tokPos :: acc)
          "region" => go k nextPos more (MkToken (TkKw "region") tokPos :: acc)
          "drop" => go k nextPos more (MkToken (TkKw "drop") tokPos :: acc)
          "copy" => go k nextPos more (MkToken (TkKw "copy") tokPos :: acc)
          "inl" => go k nextPos more (MkToken (TkKw "inl") tokPos :: acc)
          "inr" => go k nextPos more (MkToken (TkKw "inr") tokPos :: acc)
          "case" => go k nextPos more (MkToken (TkKw "case") tokPos :: acc)
          "of" => go k nextPos more (MkToken (TkKw "of") tokPos :: acc)
          "type" => go k nextPos more (MkToken (TkKw "type") tokPos :: acc)
          _ =>
            case more of
              '.' :: rest2 =>
                let (tailChars, rest3) = span isIdentChar rest2 in
                let full = identChars ++ ['.'] ++ tailChars in
                let fullStr = pack full in
                let nextPos2 = advanceN pos full in
                go k nextPos2 rest3 (MkToken (TkIdent fullStr) tokPos :: acc)
              _ => go k nextPos more (MkToken (TkIdent ident) tokPos :: acc)
      else if isDigitChar c then
        let (numChars, more) = span isNumChar (c :: rest) in
        let tokPos = pos in
        let nextPos = advanceN pos numChars in
        if elem '.' numChars
          then go k nextPos more (MkToken (TkFloat (pack numChars)) tokPos :: acc)
          else go k nextPos more (MkToken (TkInt (pack numChars)) tokPos :: acc)
      else case c of
        '(' =>
          case rest of
            ')' :: tail =>
              let nextPos = advanceN pos ['(', ')'] in
              go k nextPos tail (MkToken TkUnit pos :: acc)
            _ =>
              let nextPos = advance pos '(' in
              go k nextPos rest (MkToken TkLParen pos :: acc)
        ')' =>
          let nextPos = advance pos ')' in
          go k nextPos rest (MkToken TkRParen pos :: acc)
        '{' =>
          let nextPos = advance pos '{' in
          go k nextPos rest (MkToken TkLBrace pos :: acc)
        '}' =>
          let nextPos = advance pos '}' in
          go k nextPos rest (MkToken TkRBrace pos :: acc)
        '[' =>
          let nextPos = advance pos '[' in
          go k nextPos rest (MkToken TkLBracket pos :: acc)
        ']' =>
          let nextPos = advance pos ']' in
          go k nextPos rest (MkToken TkRBracket pos :: acc)
        ',' =>
          let nextPos = advance pos ',' in
          go k nextPos rest (MkToken TkComma pos :: acc)
        ':' =>
          let nextPos = advance pos ':' in
          go k nextPos rest (MkToken TkColon pos :: acc)
        ';' =>
          let nextPos = advance pos ';' in
          go k nextPos rest (MkToken TkSemi pos :: acc)
        '@' =>
          let nextPos = advance pos '@' in
          go k nextPos rest (MkToken TkAt pos :: acc)
        '.' =>
          let nextPos = advance pos '.' in
          go k nextPos rest (MkToken TkDot pos :: acc)
        '=' =>
          case rest of
            '=' :: tail =>
              let nextPos = advanceN pos ['=', '='] in
              go k nextPos tail (MkToken TkEqEq pos :: acc)
            _ =>
              let nextPos = advance pos '=' in
              go k nextPos rest (MkToken TkEq pos :: acc)
        '!' =>
          case rest of
            '=' :: tail =>
              let nextPos = advanceN pos ['!', '='] in
              go k nextPos tail (MkToken TkNe pos :: acc)
            _ =>
              let nextPos = advance pos '!' in
              go k nextPos rest (MkToken TkBang pos :: acc)
        '<' =>
          case rest of
            '=' :: tail =>
              let nextPos = advanceN pos ['<', '='] in
              go k nextPos tail (MkToken TkLe pos :: acc)
            _ =>
              let nextPos = advance pos '<' in
              go k nextPos rest (MkToken TkLt pos :: acc)
        '>' =>
          case rest of
            '=' :: tail =>
              let nextPos = advanceN pos ['>', '='] in
              go k nextPos tail (MkToken TkGe pos :: acc)
            _ =>
              let nextPos = advance pos '>' in
              go k nextPos rest (MkToken TkGt pos :: acc)
        '&' =>
          case rest of
            '&' :: tail =>
              let nextPos = advanceN pos ['&', '&'] in
              go k nextPos tail (MkToken TkAndAnd pos :: acc)
            _ =>
              let nextPos = advance pos '&' in
              go k nextPos rest (MkToken TkAmp pos :: acc)
        '|' =>
          case rest of
            '|' :: tail =>
              let nextPos = advanceN pos ['|', '|'] in
              go k nextPos tail (MkToken TkOrOr pos :: acc)
            _ => Left (UnexpectedChar '|' pos)
        '+' =>
          let nextPos = advance pos '+' in
          go k nextPos rest (MkToken TkPlus pos :: acc)
        '-' =>
          case rest of
            '>' :: tail =>
              let nextPos = advanceN pos ['-', '>'] in
              go k nextPos tail (MkToken TkArrow pos :: acc)
            _ =>
              let nextPos = advance pos '-' in
              go k nextPos rest (MkToken TkMinus pos :: acc)
        '*' =>
          let nextPos = advance pos '*' in
          go k nextPos rest (MkToken TkStar pos :: acc)
        '/' =>
          case rest of
            '/' :: tail =>
              let (comment, more) = span (\ch => ch /= '\n') tail in
              let skipped = '/' :: '/' :: comment in
              let nextPos = advanceN pos skipped in
              go k nextPos more acc
            _ =>
              let nextPos = advance pos '/' in
              go k nextPos rest (MkToken TkSlash pos :: acc)
        '%' =>
          let nextPos = advance pos '%' in
          go k nextPos rest (MkToken TkPercent pos :: acc)
        '"' =>
          case readString pos rest of
            Left err => Left err
            Right (s, more, nextPos) => go k nextPos more (MkToken (TkString s) pos :: acc)
        _ => Left (UnexpectedChar c pos)
