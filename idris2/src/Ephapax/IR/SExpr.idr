-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.IR.SExpr

import Data.List

%default total

isSpaceChar : Char -> Bool
isSpaceChar c =
  c == ' ' || c == '\n' || c == '\t' || c == '\r'

unwords : List String -> String
unwords [] = ""
unwords (x :: xs) = foldl (\acc, s => acc ++ " " ++ s) x xs

unescapeChar : Char -> Char
unescapeChar 'n' = '\n'
unescapeChar 't' = '\t'
unescapeChar 'r' = '\r'
unescapeChar '"' = '"'
unescapeChar '\\' = '\\'
unescapeChar c = c

public export
data SExpr = Atom String | List (List SExpr)

public export
covering
Show SExpr where
  show (Atom s) = s
  show (List xs) = "(" ++ unwords (map show xs) ++ ")"

public export
data ParseError
  = UnexpectedEof
  | UnexpectedToken String
  | Invalid String

public export
Show ParseError where
  show UnexpectedEof = "unexpected end of input"
  show (UnexpectedToken t) = "unexpected token: " ++ t
  show (Invalid msg) = "invalid s-expression: " ++ msg

parseAtom : List Char -> Either ParseError (String, List Char)
parseAtom input =
  let (atomChars, rest) = span isAtomChar input in
    if null atomChars then Left (Invalid "empty atom")
    else Right (pack atomChars, rest)
  where
    isAtomChar : Char -> Bool
    isAtomChar c = not (isSpaceChar c) && c /= '(' && c /= ')'

parseString : List Char -> Either ParseError (String, List Char)
parseString input = go [] input
  where
    go : List Char -> List Char -> Either ParseError (String, List Char)
    go acc [] = Left UnexpectedEof
    go acc ('"' :: rest) = Right (pack (reverse acc), rest)
    go acc ('\\' :: c :: rest) =
      go (unescapeChar c :: acc) rest
    go acc (c :: rest) = go (c :: acc) rest

-- Fueled mutual parser: an explicit Nat fuel parameter strictly decreases
-- on every recursive call, giving Idris2 a structural termination measure.
-- The public `parse` wrapper seeds fuel from `length input`, which suffices
-- because each successful primitive parser ([parseAtom], [parseString], the
-- '(' / ')' tokens) consumes at least one character from the input list.
-- Thus the original (unfueled) call graph cannot loop without exhausting
-- the character stream — fuel = list length is a sound bound.
mutual
  parseExprFuel : Nat -> List Char -> Either ParseError (SExpr, List Char)
  parseExprFuel Z _ = Left (Invalid "parser fuel exhausted")
  parseExprFuel (S k) input =
    case dropWhile isSpaceChar input of
      [] => Left UnexpectedEof
      '(' :: rest => parseListFuel k rest
      '"' :: rest =>
        case parseString rest of
          Left err => Left err
          Right (s, more) => Right (Atom ("\"" ++ s ++ "\""), more)
      cs =>
        case parseAtom cs of
          Left err => Left err
          Right (s, more) => Right (Atom s, more)

  parseListFuel : Nat -> List Char -> Either ParseError (SExpr, List Char)
  parseListFuel Z _ = Left (Invalid "parser fuel exhausted")
  parseListFuel (S k) input =
    listGo k [] (dropWhile isSpaceChar input)

  -- Lifted out of the `where` clause so its own fuel parameter can
  -- participate in the mutual termination measure. Each iteration of
  -- [listGo] either terminates (']', empty) or parses one element via
  -- [parseExprFuel k] and recurses on [listGo k]; both arms decrement
  -- fuel from (S k) → k, so totality is by structural recursion on the
  -- outer fuel of the enclosing mutual block.
  listGo : Nat -> List SExpr -> List Char -> Either ParseError (SExpr, List Char)
  listGo Z _ _ = Left (Invalid "parser fuel exhausted")
  listGo (S j) acc [] = Left UnexpectedEof
  listGo (S j) acc (')' :: rest) = Right (List (reverse acc), rest)
  listGo (S j) acc cs =
    case parseExprFuel j cs of
      Left err => Left err
      Right (expr, more) => listGo j (expr :: acc) more

public export
parse : String -> Either ParseError SExpr
parse input =
  let chars = unpack input
  in case parseExprFuel (length chars) chars of
       Left err => Left err
       Right (expr, rest) =>
         case dropWhile isSpaceChar rest of
           [] => Right expr
           xs => Left (UnexpectedToken (pack xs))
