module Ephapax.IR.SExpr

import Data.List

%default partial

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

mutual
  parseExpr : List Char -> Either ParseError (SExpr, List Char)
  parseExpr input =
    case dropWhile isSpaceChar input of
      [] => Left UnexpectedEof
      '(' :: rest => parseList rest
      '"' :: rest =>
        case parseString rest of
          Left err => Left err
          Right (s, more) => Right (Atom ("\"" ++ s ++ "\""), more)
      cs =>
        case parseAtom cs of
          Left err => Left err
          Right (s, more) => Right (Atom s, more)

  parseList : List Char -> Either ParseError (SExpr, List Char)
  parseList input =
    go [] (dropWhile isSpaceChar input)
    where
      go : List SExpr -> List Char -> Either ParseError (SExpr, List Char)
      go acc [] = Left UnexpectedEof
      go acc (')' :: rest) = Right (List (reverse acc), rest)
      go acc cs =
        case parseExpr cs of
          Left err => Left err
          Right (expr, more) => go (expr :: acc) more

public export
parse : String -> Either ParseError SExpr
parse input =
  case parseExpr (unpack input) of
    Left err => Left err
    Right (expr, rest) =>
      case dropWhile isSpaceChar rest of
        [] => Right expr
        xs => Left (UnexpectedToken (pack xs))
