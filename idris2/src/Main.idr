module Main

import System
import System.File.ReadWrite as FileRW
import System.File.Error
import Data.List
import Data.String
import Ephapax.IR.SExpr as SExpr
import Ephapax.IR.Decode
import Ephapax.IR.AST
import Ephapax.Parse.Lexer
import Ephapax.Parse.Parser
import Ephapax.Parse.ZigBuffer
import Ephapax.Parse.Util as PUtil
import Ephapax.Affine.Typecheck as TC
import Ephapax.Affine.Emit

%default partial

usage : String
usage = unlines [
  "ephapax-affine <input.eph> --mode affine|linear --out <output.sexpr> [--sexpr] [--parse-only] [--profile-parse]",
  "",
  "This stage parses Ephapax concrete syntax (default) or S-expression IR,",
  "type-checks (affine or linear), and writes S-expression IR for the Rust",
  "WASM backend."
  ]

record Options where
  constructor MkOptions
  input : String
  output : String
  mode : TC.Mode
  sexpr : Bool
  parseOnly : Bool
  profileParse : Bool

normalizeArgs : List String -> List String
normalizeArgs args =
  case args of
    exe :: rest =>
      if isSuffixOf "ephapax-affine" exe then rest else args
    _ => args

parseMode : String -> TC.Mode
parseMode "linear" = TC.Linear
parseMode _ = TC.Affine

setMode : Options -> TC.Mode -> Options
setMode (MkOptions inp out _ sx po pp) m = MkOptions inp out m sx po pp

setOutput : Options -> String -> Options
setOutput (MkOptions inp _ md sx po pp) out = MkOptions inp out md sx po pp

setSexpr : Options -> Options
setSexpr (MkOptions inp out md _ po pp) = MkOptions inp out md True po pp

setParseOnly : Options -> Options
setParseOnly (MkOptions inp out md sx _ pp) = MkOptions inp out md sx True pp

setProfileParse : Options -> Options
setProfileParse (MkOptions inp out md sx po _) = MkOptions inp out md sx po True

parseFlags : Options -> List String -> Either String Options
parseFlags opts [] =
  case opts of
    MkOptions _ out _ _ _ _ =>
      if out == "" then Left usage else Right opts
parseFlags opts ("--mode" :: modeStr :: rest) =
  parseFlags (setMode opts (parseMode modeStr)) rest
parseFlags opts ("--out" :: output :: rest) =
  parseFlags (setOutput opts output) rest
parseFlags opts ("--sexpr" :: rest) =
  parseFlags (setSexpr opts) rest
parseFlags opts ("--parse-only" :: rest) =
  parseFlags (setParseOnly opts) rest
parseFlags opts ("--profile-parse" :: rest) =
  parseFlags (setProfileParse opts) rest
parseFlags _ _ = Left usage

parseArgs : List String -> Either String Options
parseArgs args =
  case args of
    input :: rest => parseFlags (MkOptions input "" TC.Affine False False False) rest
    _ => Left usage

handleParseErr : SExpr.ParseError -> IO (Maybe Module)
handleParseErr err =
  putStrLn ("Parse error: " ++ show err) >> pure (the (Maybe Module) Nothing)

handleDecodeErr : SExpr.ParseError -> IO (Maybe Module)
handleDecodeErr err =
  putStrLn ("Decode error: " ++ show err) >> pure (the (Maybe Module) Nothing)

handleLexErr : LexError -> IO (Maybe Module)
handleLexErr err =
  putStrLn ("Lex error: " ++ show err) >> pure (the (Maybe Module) Nothing)

handleSexpr : SExpr.SExpr -> IO (Maybe Module)
handleSexpr sexpr =
  either handleDecodeErr (\m => pure (Just m)) (fromSExpr sexpr)

handleToks : Bool -> List Token -> IO (Maybe Module)
handleToks prof toks = do
  let buf = newBuf (cast (Prelude.Types.List.length toks))
  _ <- traverse (\t => pushTok buf t.kind t.pos) toks
  parsed <- if prof
    then do
      case parseModuleTokensWithStats buf of
        Left err => pure (Left err)
        Right (m, (peekCount, popCount, expectCount)) => do
          putStrLn ("Parser stats: peek=" ++ show peekCount ++ " pop=" ++ show popCount ++ " expect=" ++ show expectCount)
          pure (Right m)
    else pure (parseModuleTokens buf)
  freeBuf buf
  case the (Either PUtil.ParseError Module) parsed of
    Left err => do
      putStrLn ("Parse error: " ++ show err)
      pure (the (Maybe Module) Nothing)
    Right m => pure (Just m)

parseSexprInput : String -> IO (Maybe Module)
parseSexprInput input =
  either handleParseErr handleSexpr (SExpr.parse input)

parseConcreteInput : Bool -> String -> IO (Maybe Module)
parseConcreteInput prof input =
  either handleLexErr (handleToks prof) (Ephapax.Parse.Lexer.lex input)

main : IO Builtin.Unit
main = do
  args <- getArgs
  let args' = normalizeArgs args
  case parseArgs args' of
    Left msg => putStrLn msg
    Right opts => do
      let MkOptions inp out md isSexpr only prof = opts
      inputRes <- FileRW.readFile inp
      case inputRes of
        Left err => putStrLn ("Read error: " ++ show err)
        Right input => do
          modOrErr <- if isSexpr then parseSexprInput input else parseConcreteInput prof input
          case the (Maybe Module) modOrErr of
            Nothing => pure (the Builtin.Unit ())
            Just mod =>
              if only then
                putStrLn "Parsed ok."
              else
                case TC.checkModule md mod of
                  Left err => putStrLn ("Type error: " ++ show err)
                  Right _ => do
                    let emitted = emitModule mod
                    writeRes <- FileRW.writeFile out emitted
                    case the (Either FileError Builtin.Unit) writeRes of
                      Left err => putStrLn ("Write error: " ++ show err)
                      Right _ => putStrLn ("Wrote " ++ out)
