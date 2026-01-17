module Ephapax.Affine.Typecheck

import Data.List
import Data.Maybe
import Ephapax.IR.AST

%default partial

public export
data Mode = Affine | Linear

public export
Eq Mode where
  (==) Affine Affine = True
  (==) Linear Linear = True
  (==) _ _ = False

public export
Show Mode where
  show Affine = "affine"
  show Linear = "linear"

public export
data TypeError
  = LinearReused String
  | LinearNotConsumed String
  | UnboundVar String
  | InactiveRegion String
  | TypeMismatch Ty Ty
  | CannotCopyLinear Ty
  | UnnecessaryDrop
  | BranchMismatch String String String
  | RegionEscape String

public export
Show TypeError where
  show (LinearReused v) = "linear variable reused: " ++ v
  show (LinearNotConsumed v) = "linear variable not consumed: " ++ v
  show (UnboundVar v) = "unbound variable: " ++ v
  show (InactiveRegion r) = "inactive region: " ++ r
  show (TypeMismatch a b) = "type mismatch: expected " ++ show a ++ ", found " ++ show b
  show (CannotCopyLinear t) = "cannot copy linear type: " ++ show t
  show UnnecessaryDrop = "cannot drop unrestricted value"
  show (BranchMismatch v t e) =
    "branch linearity mismatch for " ++ v ++ " (then: " ++ t ++ ", else: " ++ e ++ ")"
  show (RegionEscape r) = "region escape: " ++ r

record Entry where
  constructor MkEntry
  name : String
  ty : Ty
  used : Bool

record Ctx where
  constructor MkCtx
  vars : List Entry
  regions : List String

litTy : Literal -> Ty
checkBlock : Mode -> Ctx -> List Expr -> Either TypeError (Ty, Ctx)
numeric : Ty -> Ctx -> Either TypeError (Ty, Ctx)

emptyCtx : Ctx
emptyCtx = MkCtx [] []

setVars : Ctx -> List Entry -> Ctx
setVars ctx vs = MkCtx vs (regions ctx)

setRegions : Ctx -> List String -> Ctx
setRegions ctx rs = MkCtx (vars ctx) rs

lookupVar : String -> List Entry -> Maybe Entry
lookupVar _ [] = Nothing
lookupVar name (e :: es) = if e.name == name then Just e else lookupVar name es

setUsed : String -> Bool -> List Entry -> List Entry
setUsed _ _ [] = []
setUsed name used (e :: es) =
  if e.name == name then MkEntry e.name e.ty used :: es
  else e :: setUsed name used es

removeVar : String -> List Entry -> List Entry
removeVar _ [] = []
removeVar name (e :: es) =
  if e.name == name then es else e :: removeVar name es

extendVar : Entry -> List Entry -> List Entry
extendVar e vars = e :: vars

regionActive : String -> List String -> Bool
regionActive name = elem name

checkAllLinearUsed : Mode -> List Entry -> Either TypeError Builtin.Unit
checkAllLinearUsed Affine _ = Right ()
checkAllLinearUsed Linear vars =
  case find (\e => isLinear e.ty && not e.used) vars of
    Just e => Left (LinearNotConsumed e.name)
    Nothing => Right ()

checkBoundUsed : Mode -> String -> List Entry -> Either TypeError Builtin.Unit
checkBoundUsed Affine _ _ = Right ()
checkBoundUsed Linear name vars =
  case lookupVar name vars of
    Just entry =>
      if isLinear entry.ty && not entry.used
        then Left (LinearNotConsumed name)
        else Right ()
    Nothing => Right ()

mergeAffine : List Entry -> List Entry -> List Entry
mergeLinear : List Entry -> List Entry -> Either TypeError (List Entry)

mergeBranches : Mode -> List Entry -> List Entry -> Either TypeError (List Entry)
mergeBranches Affine left right = Right (mergeAffine left right)
mergeBranches Linear left right = mergeLinear left right

mergeAffine left right = map mergeOne left
  where
    mergeOne : Entry -> Entry
    mergeOne e =
      case lookupVar e.name right of
        Just other => MkEntry e.name e.ty (e.used || other.used)
        Nothing => e

mergeLinear left right =
  case findMismatch left right of
    Just (v, t, e) => Left (BranchMismatch v t e)
    Nothing => Right left
  where
    findMismatch : List Entry -> List Entry -> Maybe (String, String, String)
    findMismatch [] _ = Nothing
    findMismatch (e :: es) other =
      if isLinear e.ty then
        case lookupVar e.name other of
          Just o =>
            if e.used == o.used then findMismatch es other
            else Just (e.name, if e.used then "consumed" else "not consumed",
                               if o.used then "consumed" else "not consumed")
          Nothing => Just (e.name, "missing", "missing")
      else findMismatch es other

check : Mode -> Ctx -> Expr -> Either TypeError (Ty, Ctx)
check mode ctx expr =
  case expr of
    Lit lit => Right (litTy lit, ctx)
    VarE name =>
      case lookupVar name ctx.vars of
        Nothing => Left (UnboundVar name)
        Just entry =>
          if isLinear entry.ty then
            if entry.used
              then Left (LinearReused name)
              else Right (entry.ty, setVars ctx (setUsed name True (vars ctx)))
          else Right (entry.ty, ctx)
    StringNew r _ =>
      if regionActive r ctx.regions
        then Right (StringTy r, ctx)
        else Left (InactiveRegion r)
    StringConcat a b => do
      (ta, ctx1) <- check mode ctx a
      (tb, ctx2) <- check mode ctx1 b
      case (ta, tb) of
        (StringTy ra, StringTy rb) =>
          if ra == rb then Right (StringTy ra, ctx2)
          else Left (TypeMismatch ta tb)
        _ => Left (TypeMismatch ta tb)
    StringLen e => do
      (t, ctx1) <- check mode ctx e
      case t of
        StringTy _ => Right (Base I32, ctx1)
        Borrow (StringTy _) => Right (Base I32, ctx1)
        _ => Left (TypeMismatch (StringTy "_") t)
    Let name _ val body => do
      (tv, ctx1) <- check mode ctx val
      let ctx2 = setVars ctx1 (extendVar (MkEntry name tv False) (vars ctx1))
      (tb, ctx3) <- check mode ctx2 body
      checkBoundUsed mode name ctx3.vars
      let ctx4 = setVars ctx3 (removeVar name (vars ctx3))
      Right (tb, ctx4)
    LetLin name _ val body =>
      check mode ctx (Let name Nothing val body)
    Lambda param ty body => do
      let ctx1 = setVars ctx (extendVar (MkEntry param ty False) (vars ctx))
      (tb, ctx2) <- check mode ctx1 body
      checkBoundUsed mode param ctx2.vars
      Right (Fun ty tb, setVars ctx2 (removeVar param (vars ctx2)))
    App f a => do
      (tf, ctx1) <- check mode ctx f
      (ta, ctx2) <- check mode ctx1 a
      case tf of
        Fun p r => if p == ta then Right (r, ctx2) else Left (TypeMismatch p ta)
        _ => Left (TypeMismatch (Fun ta (Base Unit)) tf)
    Pair a b => do
      (ta, ctx1) <- check mode ctx a
      (tb, ctx2) <- check mode ctx1 b
      Right (Prod ta tb, ctx2)
    Fst e => do
      (t, ctx1) <- check mode ctx e
      case t of
        Prod a b =>
          if mode == Linear && isLinear b
            then Left (LinearNotConsumed "_pair_snd")
            else Right (a, ctx1)
        _ => Left (TypeMismatch (Prod (Base Unit) (Base Unit)) t)
    Snd e => do
      (t, ctx1) <- check mode ctx e
      case t of
        Prod a b =>
          if mode == Linear && isLinear a
            then Left (LinearNotConsumed "_pair_fst")
            else Right (b, ctx1)
        _ => Left (TypeMismatch (Prod (Base Unit) (Base Unit)) t)
    Inl ty e => do
      (tv, ctx1) <- check mode ctx e
      Right (Sum tv ty, ctx1)
    Inr ty e => do
      (tv, ctx1) <- check mode ctx e
      Right (Sum ty tv, ctx1)
    Case scr (lv, lb) (rv, rb) => do
      (ts, ctx1) <- check mode ctx scr
      case ts of
        Sum l r => do
          let ctxL = setVars ctx1 (extendVar (MkEntry lv l False) (vars ctx1))
          (tl, ctxL2) <- check mode ctxL lb
          let ctxL3 = setVars ctxL2 (removeVar lv (vars ctxL2))
          let ctxR0 = ctx1
          let ctxR = setVars ctxR0 (extendVar (MkEntry rv r False) (vars ctxR0))
          (tr, ctxR2) <- check mode ctxR rb
          let ctxR3 = setVars ctxR2 (removeVar rv (vars ctxR2))
          case mergeBranches mode ctxL3.vars ctxR3.vars of
            Left err => Left err
            Right merged =>
              if tl == tr then Right (tl, setVars ctx1 merged)
              else Left (TypeMismatch tl tr)
        _ => Left (TypeMismatch (Sum (Base Unit) (Base Unit)) ts)
    If c t f => do
      (tc, ctx1) <- check mode ctx c
      if tc /= Base Bool then Left (TypeMismatch (Base Bool) tc) else do
        (tt, ctxThen) <- check mode ctx1 t
        (tf, ctxElse) <- check mode ctx1 f
        case mergeBranches mode ctxThen.vars ctxElse.vars of
          Left err => Left err
          Right merged =>
            if tt == tf then Right (tt, setVars ctx1 merged)
            else Left (TypeMismatch tt tf)
    RegionExpr r body => do
      let ctx1 = setRegions ctx (r :: regions ctx)
      (tb, ctx2) <- check mode ctx1 body
      let ctx3 = setRegions ctx2 (regions ctx)
      case tb of
        StringTy r2 => if r2 == r then Left (RegionEscape r) else Right (tb, ctx3)
        _ => Right (tb, ctx3)
    BorrowE e =>
      case e of
        VarE name =>
          case lookupVar name ctx.vars of
            Just entry => Right (Borrow entry.ty, ctx)
            Nothing => Left (UnboundVar name)
        _ => do
          (t, ctx1) <- check mode ctx e
          Right (Borrow t, ctx1)
    Deref e => do
      (t, ctx1) <- check mode ctx e
      case t of
        Borrow inner => Right (inner, ctx1)
        Ref _ inner => Right (inner, ctx1)
        _ => Left (TypeMismatch (Borrow (Base Unit)) t)
    Drop e => do
      (t, ctx1) <- check mode ctx e
      if isLinear t then Right (Base Unit, ctx1) else Left UnnecessaryDrop
    Copy e => do
      (t, ctx1) <- check mode ctx e
      if isLinear t then Left (CannotCopyLinear t) else Right (Prod t t, ctx1)
    Block es => checkBlock mode ctx es
    BinOpE op a b => do
      (ta, ctx1) <- check mode ctx a
      (tb, ctx2) <- check mode ctx1 b
      if ta /= tb then Left (TypeMismatch ta tb) else
        case op of
          Add => numeric ta ctx2
          Sub => numeric ta ctx2
          Mul => numeric ta ctx2
          Div => numeric ta ctx2
          Mod => numeric ta ctx2
          Lt => Right (Base Bool, ctx2)
          Le => Right (Base Bool, ctx2)
          Gt => Right (Base Bool, ctx2)
          Ge => Right (Base Bool, ctx2)
          Eq => Right (Base Bool, ctx2)
          Ne => Right (Base Bool, ctx2)
          And => if ta == Base Bool then Right (Base Bool, ctx2) else Left (TypeMismatch (Base Bool) ta)
          Or => if ta == Base Bool then Right (Base Bool, ctx2) else Left (TypeMismatch (Base Bool) ta)
    UnOpE op e => do
      (t, ctx1) <- check mode ctx e
      case op of
        Not => if t == Base Bool then Right (Base Bool, ctx1) else Left (TypeMismatch (Base Bool) t)
        Neg => numeric t ctx1

checkBlock _ ctx [] = Right (Base Unit, ctx)
checkBlock mode ctx [e] = check mode ctx e
checkBlock mode ctx (e :: es) =
  case check mode ctx e of
    Left err => Left err
    Right (_, ctx1) => checkBlock mode ctx1 es

numeric t ctx =
  case t of
    Base I32 => Right (t, ctx)
    Base I64 => Right (t, ctx)
    Base F32 => Right (t, ctx)
    Base F64 => Right (t, ctx)
    _ => Left (TypeMismatch (Base I32) t)

litTy LUnit = Base Unit
litTy (LBool _) = Base Bool
litTy (LI32 _) = Base I32
litTy (LI64 _) = Base I64
litTy (LF32 _) = Base F32
litTy (LF64 _) = Base F64
litTy (LString _) = StringTy "_"

public export
checkModule : Mode -> Module -> Either TypeError Builtin.Unit
checkModule mode (MkModule _ decls) =
  let ctx0 = emptyCtx in
  let fnCtx = foldl addFn ctx0 decls in
    checkDecls mode fnCtx decls
  where
    addFn : Ctx -> Decl -> Ctx
    addFn ctx (Fn name params ret _) =
      let fnTy = foldr (\(_, pty), acc => Fun pty acc) ret params in
      setVars ctx (extendVar (MkEntry name fnTy False) (vars ctx))
    addFn ctx _ = ctx

    checkDecls : Mode -> Ctx -> List Decl -> Either TypeError Builtin.Unit
    checkDecls _ _ [] = Right ()
    checkDecls mode ctx (d :: ds) =
      case d of
        Fn name params ret body =>
          let saved = ctx in
          let ctx1 = foldl (\c, (n, t) => setVars c (extendVar (MkEntry n t False) (vars c))) ctx params in
          case check mode ctx1 body of
            Left err => Left err
            Right (tb, ctx2) =>
              if tb /= ret then Left (TypeMismatch ret tb) else
                case checkAllLinearUsed mode ctx2.vars of
                  Left err => Left err
                  Right () => checkDecls mode saved ds
        TypeDecl _ _ => checkDecls mode ctx ds
