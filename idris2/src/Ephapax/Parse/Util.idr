module Ephapax.Parse.Util

import Data.List
import Ephapax.Parse.Lexer
import Ephapax.Parse.Stream

%default partial

public export
data ParseError = PE String (Maybe Pos)

public export
Show ParseError where
  show (PE msg Nothing) = msg
  show (PE msg (Just (MkPos l c))) =
    msg ++ " at " ++ show l ++ ":" ++ show c

public export
Parser : Type -> Type
Parser a = Stream -> Either ParseError (a, Stream)

public export
expect : TokKind -> Parser ()
expect kind stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      if t.kind == kind
        then Right ((), rest)
        else Left (PE ("expected " ++ show kind ++ ", got " ++ show t.kind) (Just t.pos))
    Nothing => Left (PE "unexpected end of input" Nothing)

public export
expectKw : String -> Parser ()
expectKw kw stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      case t.kind of
        TkKw s => if s == kw then Right ((), rest)
                  else Left (PE ("expected keyword " ++ kw) (Just t.pos))
        _ => Left (PE ("expected keyword " ++ kw) (Just t.pos))
    Nothing => Left (PE ("expected keyword " ++ kw) Nothing)

public export
expectIdent : Parser String
expectIdent stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      case t.kind of
        TkIdent s => Right (s, rest)
        _ => Left (PE "expected identifier" (Just t.pos))
    Nothing => Left (PE "expected identifier" Nothing)

public export
many : Parser a -> Parser (List a)
many p stream =
  case p stream of
    Left _ => Right ([], stream)
    Right (v, rest) =>
      case many p rest of
        Left err => Left err
        Right (vs, rest2) => Right (v :: vs, rest2)

public export
optional : Parser a -> Parser (Maybe a)
optional p stream =
  case p stream of
    Left _ => Right (Nothing, stream)
    Right (v, rest) => Right (Just v, rest)

public export
peek : Parser (Maybe Token)
peek stream = Right (peekTok stream, withPeek stream)

public export
satisfy : (Token -> Bool) -> Parser Token
satisfy pred stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      if pred t then Right (t, rest)
      else Left (PE ("unexpected token: " ++ show t) (Just t.pos))
    Nothing => Left (PE "unexpected end of input" Nothing)

public export
choice : List (Parser a) -> Parser a
choice [] stream = Left (PE "no matching parse" (posOf stream))
choice (p :: ps) stream =
  case p stream of
    Right res => Right res
    Left _ => choice ps stream

public export
expectToken : (Token -> Maybe a) -> String -> Parser a
expectToken project expected stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      case project t of
        Just v => Right (v, rest)
        Nothing => Left (PE ("expected " ++ expected ++ ", got " ++ show t.kind) (Just t.pos))
    Nothing => Left (PE ("expected " ++ expected ++ ", got EOF") Nothing)

public export
expectInt : Parser String
expectInt = expectToken asInt "integer"
  where
    asInt : Token -> Maybe String
    asInt t = case t.kind of
      TkInt s => Just s
      _ => Nothing

public export
expectFloat : Parser String
expectFloat = expectToken asFloat "float"
  where
    asFloat : Token -> Maybe String
    asFloat t = case t.kind of
      TkFloat s => Just s
      _ => Nothing

public export
expectString : Parser String
expectString = expectToken asString "string"
  where
    asString : Token -> Maybe String
    asString t = case t.kind of
      TkString s => Just s
      _ => Nothing

public export
expectBool : Parser Bool
expectBool = expectToken asBool "bool"
  where
    asBool : Token -> Maybe Bool
    asBool t = case t.kind of
      TkBool b => Just b
      _ => Nothing

public export
expectIdentEq : String -> Parser String
expectIdentEq name stream =
  let s1 = withExpect stream in
  case popTok s1 of
    Just (t, rest) =>
      case t.kind of
        TkIdent s => if s == name then Right (s, rest)
                     else Left (PE ("expected " ++ name) (Just t.pos))
        _ => Left (PE ("expected " ++ name) (Just t.pos))
    Nothing => Left (PE ("expected " ++ name) Nothing)

public export
sepBy : Parser a -> Parser sep -> Parser (List a)
sepBy p sep stream =
  case p stream of
    Left _ => Right ([], stream)
    Right (v, rest) => sepTail [v] rest
  where
    sepTail : List a -> Parser (List a)
    sepTail acc stream2 =
      case sep stream2 of
        Left _ => Right (reverse acc, stream2)
        Right (_, rest) =>
          case p rest of
            Left err => Left err
            Right (v, rest2) => sepTail (v :: acc) rest2

public export
sepBy1 : Parser a -> Parser sep -> Parser (List a)
sepBy1 p sep stream =
  case p stream of
    Left err => Left err
    Right (v, rest) =>
      case sepBy p sep rest of
        Left err2 => Left err2
        Right (vs, rest2) => Right (v :: vs, rest2)

posOf : Stream -> Maybe Pos
posOf = Ephapax.Parse.Stream.posOf
