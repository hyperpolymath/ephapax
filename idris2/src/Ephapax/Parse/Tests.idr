module Ephapax.Parse.Tests

import Data.List
import Ephapax.Parse.Lexer
import Ephapax.Parse.Parser
import Ephapax.Parse.ZigBuffer
import Ephapax.IR.AST

%default total

record Failure where
  constructor MkFailure
  name : String
  msg : String

assertEq : (Eq a, Show a) => String -> a -> a -> List Failure
assertEq name expected actual =
  if expected == actual then []
  else [MkFailure name ("expected " ++ show expected ++ ", got " ++ show actual)]

assertTrue : String -> Bool -> List Failure
assertTrue name ok = if ok then [] else [MkFailure name "assertion failed"]

runTests : IO Int
runTests = do
  f1 <- pure testLexPositions
  f2 <- testParseModule
  f3 <- testBinaryPrecedence
  f4 <- testParseErrorPosition
  f5 <- testLetIfRegion
  f6 <- testCaseInlInr
  f7 <- testStringOps
  let failures = concat [f1, f2, f3, f4, f5, f6, f7]
  case failures of
    [] => do
      putStrLn "parse-tests: ok"
      pure 0
    _ => do
      putStrLn "parse-tests: failures"
      mapM_ (\f => putStrLn ("- " ++ f.name ++ ": " ++ f.msg)) failures
      pure (length failures)

-- Tests

testLexPositions : List Failure
testLexPositions =
  case Ephapax.Parse.Lexer.lex "let x = 1 in x" of
    Left err => [MkFailure "lex-positions" (show err)]
    Right toks =>
      case toks of
        (MkToken (TkKw "let") (MkPos 1 1)) ::
        (MkToken (TkIdent "x") (MkPos 1 5)) ::
        (MkToken TkEq (MkPos 1 7)) ::
        (MkToken (TkInt "1") (MkPos 1 9)) ::
        (MkToken (TkKw "in") (MkPos 1 11)) ::
        (MkToken (TkIdent "x") (MkPos 1 14)) :: _ => []
        _ => [MkFailure "lex-positions" "unexpected token positions"]


testParseModule : IO (List Failure)
testParseModule =
  case Ephapax.Parse.Lexer.lex "fn main() : I32 = 1" of
    Left err => pure [MkFailure "parse-module" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left err => pure [MkFailure "parse-module" (show err)]
        Right (MkModule _ decls) =>
          case decls of
            [Fn "main" [] (Base I32) (Lit (LI32 "1"))] => pure []
            _ => pure [MkFailure "parse-module" "unexpected AST"]


testBinaryPrecedence : IO (List Failure)
testBinaryPrecedence =
  case Ephapax.Parse.Lexer.lex "fn main() : I32 = 1 + 2 * 3" of
    Left err => pure [MkFailure "binary-precedence" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left err => pure [MkFailure "binary-precedence" (show err)]
        Right (MkModule _ decls) =>
          case decls of
            [Fn "main" [] (Base I32) body] =>
              let expected =
                BinOpE Add (Lit (LI32 "1")) (BinOpE Mul (Lit (LI32 "2")) (Lit (LI32 "3")))
              in pure (assertEq "binary-precedence" expected body)
            _ => pure [MkFailure "binary-precedence" "unexpected AST"]


testParseErrorPosition : IO (List Failure)
testParseErrorPosition =
  case Ephapax.Parse.Lexer.lex "fn main( : I32 = 1" of
    Left err => pure [MkFailure "parse-error-position" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left (PE _ (Just _)) => pure []
        Left _ => pure [MkFailure "parse-error-position" "missing error position"]
        Right _ => pure [MkFailure "parse-error-position" "expected parse error"]

testLetIfRegion : IO (List Failure)
testLetIfRegion =
  let source = "fn main() : I32 = region r { let x = 1 in if true then x else 2 }" in
  case Ephapax.Parse.Lexer.lex source of
    Left err => pure [MkFailure "let-if-region" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left err => pure [MkFailure "let-if-region" (show err)]
        Right (MkModule _ decls) =>
          case decls of
            [Fn "main" [] (Base I32) _] => pure []
            _ => pure [MkFailure "let-if-region" "unexpected AST"]

testCaseInlInr : IO (List Failure)
testCaseInlInr =
  let source = "fn main() : I32 = case inl[I32](1) of inl(x) -> x inr(y) -> y" in
  case Ephapax.Parse.Lexer.lex source of
    Left err => pure [MkFailure "case-inl-inr" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left err => pure [MkFailure "case-inl-inr" (show err)]
        Right (MkModule _ decls) =>
          case decls of
            [Fn "main" [] (Base I32) _] => pure []
            _ => pure [MkFailure "case-inl-inr" "unexpected AST"]

testStringOps : IO (List Failure)
testStringOps =
  let source = "fn main() : I32 = region r { let s = String.new@r(\"hi\") in String.len(s) }" in
  case Ephapax.Parse.Lexer.lex source of
    Left err => pure [MkFailure "string-ops" (show err)]
    Right toks => do
      parsed <- parseWithBuf toks
      case parsed of
        Left err => pure [MkFailure "string-ops" (show err)]
        Right (MkModule _ decls) =>
          case decls of
            [Fn "main" [] (Base I32) _] => pure []
            _ => pure [MkFailure "string-ops" "unexpected AST"]

parseWithBuf : List Token -> IO (Either ParseError Module)
parseWithBuf toks = do
  let buf = newBuf (length toks)
  _ <- traverse (\\t => pushTok buf t.kind t.pos) toks
  let parsed = parseModuleTokens buf
  freeBuf buf
  pure parsed
