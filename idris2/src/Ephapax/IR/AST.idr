module Ephapax.IR.AST

%default partial

public export
data Linearity = Linear | Unrestricted

public export
Eq Linearity where
  (==) Linear Linear = True
  (==) Unrestricted Unrestricted = True
  (==) _ _ = False

public export
Show Linearity where
  show Linear = "Linear"
  show Unrestricted = "Unrestricted"

public export
data BaseTy = Unit | Bool | I32 | I64 | F32 | F64

public export
Eq BaseTy where
  (==) Unit Unit = True
  (==) Bool Bool = True
  (==) I32 I32 = True
  (==) I64 I64 = True
  (==) F32 F32 = True
  (==) F64 F64 = True
  (==) _ _ = False

public export
Show BaseTy where
  show Unit = "Unit"
  show Bool = "Bool"
  show I32 = "I32"
  show I64 = "I64"
  show F32 = "F32"
  show F64 = "F64"

public export
data Ty
  = Base BaseTy
  | StringTy String
  | Ref Linearity Ty
  | Fun Ty Ty
  | Prod Ty Ty
  | Sum Ty Ty
  | Region String Ty
  | Borrow Ty
  | Var String

public export
Eq Ty where
  (==) (Base a) (Base b) = a == b
  (==) (StringTy a) (StringTy b) = a == b
  (==) (Ref la ta) (Ref lb tb) = la == lb && ta == tb
  (==) (Fun a b) (Fun c d) = a == c && b == d
  (==) (Prod a b) (Prod c d) = a == c && b == d
  (==) (Sum a b) (Sum c d) = a == c && b == d
  (==) (Region ra ta) (Region rb tb) = ra == rb && ta == tb
  (==) (Borrow a) (Borrow b) = a == b
  (==) (Var a) (Var b) = a == b
  (==) _ _ = False

public export
Show Ty where
  show (Base b) = "Base " ++ show b
  show (StringTy r) = "String " ++ show r
  show (Ref l t) = "Ref " ++ show l ++ " " ++ show t
  show (Fun a b) = "Fun " ++ show a ++ " " ++ show b
  show (Prod a b) = "Prod " ++ show a ++ " " ++ show b
  show (Sum a b) = "Sum " ++ show a ++ " " ++ show b
  show (Region r t) = "Region " ++ show r ++ " " ++ show t
  show (Borrow t) = "Borrow " ++ show t
  show (Var v) = "Var " ++ show v

public export
isLinear : Ty -> Bool
isLinear (StringTy _) = True
isLinear (Ref Linear _) = True
isLinear (Region _ inner) = isLinear inner
isLinear _ = False

public export
data Literal
  = LUnit
  | LBool Bool
  | LI32 String
  | LI64 String
  | LF32 String
  | LF64 String
  | LString String

public export
Eq Literal where
  (==) LUnit LUnit = True
  (==) (LBool a) (LBool b) = a == b
  (==) (LI32 a) (LI32 b) = a == b
  (==) (LI64 a) (LI64 b) = a == b
  (==) (LF32 a) (LF32 b) = a == b
  (==) (LF64 a) (LF64 b) = a == b
  (==) (LString a) (LString b) = a == b
  (==) _ _ = False

public export
Show Literal where
  show LUnit = "LUnit"
  show (LBool b) = "LBool " ++ show b
  show (LI32 s) = "LI32 " ++ show s
  show (LI64 s) = "LI64 " ++ show s
  show (LF32 s) = "LF32 " ++ show s
  show (LF64 s) = "LF64 " ++ show s
  show (LString s) = "LString " ++ show s

public export
data BinOp
  = Add | Sub | Mul | Div | Mod
  | Lt | Le | Gt | Ge | Eq | Ne
  | And | Or

public export
Eq BinOp where
  (==) Add Add = True
  (==) Sub Sub = True
  (==) Mul Mul = True
  (==) Div Div = True
  (==) Mod Mod = True
  (==) Lt Lt = True
  (==) Le Le = True
  (==) Gt Gt = True
  (==) Ge Ge = True
  (==) Eq Eq = True
  (==) Ne Ne = True
  (==) And And = True
  (==) Or Or = True
  (==) _ _ = False

public export
Show BinOp where
  show Add = "Add"
  show Sub = "Sub"
  show Mul = "Mul"
  show Div = "Div"
  show Mod = "Mod"
  show Lt = "Lt"
  show Le = "Le"
  show Gt = "Gt"
  show Ge = "Ge"
  show Eq = "Eq"
  show Ne = "Ne"
  show And = "And"
  show Or = "Or"

public export
data UnaryOp = Not | Neg

public export
Eq UnaryOp where
  (==) Not Not = True
  (==) Neg Neg = True
  (==) _ _ = False

public export
Show UnaryOp where
  show Not = "Not"
  show Neg = "Neg"

public export
data Expr
  = Lit Literal
  | VarE String
  | StringNew String String
  | StringConcat Expr Expr
  | StringLen Expr
  | Let String (Maybe Ty) Expr Expr
  | LetLin String (Maybe Ty) Expr Expr
  | Lambda String Ty Expr
  | App Expr Expr
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  | Inl Ty Expr
  | Inr Ty Expr
  | Case Expr (String, Expr) (String, Expr)
  | If Expr Expr Expr
  | RegionExpr String Expr
  | BorrowE Expr
  | Deref Expr
  | Drop Expr
  | Copy Expr
  | Block (List Expr)
  | BinOpE BinOp Expr Expr
  | UnOpE UnaryOp Expr

public export
covering
Eq Expr where
  (==) (Lit a) (Lit b) = a == b
  (==) (VarE a) (VarE b) = a == b
  (==) (StringNew ra sa) (StringNew rb sb) = ra == rb && sa == sb
  (==) (StringConcat a b) (StringConcat c d) = a == c && b == d
  (==) (StringLen a) (StringLen b) = a == b
  (==) (Let na ta va ba) (Let nb tb vb bb) = na == nb && ta == tb && va == vb && ba == bb
  (==) (LetLin na ta va ba) (LetLin nb tb vb bb) = na == nb && ta == tb && va == vb && ba == bb
  (==) (Lambda na ta ba) (Lambda nb tb bb) = na == nb && ta == tb && ba == bb
  (==) (App a b) (App c d) = a == c && b == d
  (==) (Pair a b) (Pair c d) = a == c && b == d
  (==) (Fst a) (Fst b) = a == b
  (==) (Snd a) (Snd b) = a == b
  (==) (Inl ta ea) (Inl tb eb) = ta == tb && ea == eb
  (==) (Inr ta ea) (Inr tb eb) = ta == tb && ea == eb
  (==) (Case ea (na, ba) (nb, bb)) (Case eb (nc, bc) (nd, bd)) =
    ea == eb && na == nc && ba == bc && nb == nd && bb == bd
  (==) (If ca ta ea) (If cb tb eb) = ca == cb && ta == tb && ea == eb
  (==) (RegionExpr ra ea) (RegionExpr rb eb) = ra == rb && ea == eb
  (==) (BorrowE a) (BorrowE b) = a == b
  (==) (Deref a) (Deref b) = a == b
  (==) (Drop a) (Drop b) = a == b
  (==) (Copy a) (Copy b) = a == b
  (==) (Block a) (Block b) = a == b
  (==) (BinOpE oa la ra) (BinOpE ob lb rb) = oa == ob && la == lb && ra == rb
  (==) (UnOpE oa ea) (UnOpE ob eb) = oa == ob && ea == eb
  (==) _ _ = False

public export
covering
Show Expr where
  show (Lit a) = "Lit " ++ show a
  show (VarE a) = "VarE " ++ show a
  show (StringNew r s) = "StringNew " ++ show r ++ " " ++ show s
  show (StringConcat a b) = "StringConcat " ++ show a ++ " " ++ show b
  show (StringLen a) = "StringLen " ++ show a
  show (Let n t v b) = "Let " ++ show n ++ " " ++ show t ++ " " ++ show v ++ " " ++ show b
  show (LetLin n t v b) = "LetLin " ++ show n ++ " " ++ show t ++ " " ++ show v ++ " " ++ show b
  show (Lambda n t b) = "Lambda " ++ show n ++ " " ++ show t ++ " " ++ show b
  show (App a b) = "App " ++ show a ++ " " ++ show b
  show (Pair a b) = "Pair " ++ show a ++ " " ++ show b
  show (Fst a) = "Fst " ++ show a
  show (Snd a) = "Snd " ++ show a
  show (Inl t e) = "Inl " ++ show t ++ " " ++ show e
  show (Inr t e) = "Inr " ++ show t ++ " " ++ show e
  show (Case e (n1, b1) (n2, b2)) =
    "Case " ++ show e ++ " " ++ show (n1, b1) ++ " " ++ show (n2, b2)
  show (If c t e) = "If " ++ show c ++ " " ++ show t ++ " " ++ show e
  show (RegionExpr r e) = "RegionExpr " ++ show r ++ " " ++ show e
  show (BorrowE e) = "Borrow " ++ show e
  show (Deref e) = "Deref " ++ show e
  show (Drop e) = "Drop " ++ show e
  show (Copy e) = "Copy " ++ show e
  show (Block es) = "Block " ++ show es
  show (BinOpE o a b) = "BinOpE " ++ show o ++ " " ++ show a ++ " " ++ show b
  show (UnOpE o e) = "UnOpE " ++ show o ++ " " ++ show e

public export
data Decl
  = Fn String (List (String, Ty)) Ty Expr
  | TypeDecl String Ty

public export
covering
Eq Decl where
  (==) (Fn na pa ra ea) (Fn nb pb rb eb) = na == nb && pa == pb && ra == rb && ea == eb
  (==) (TypeDecl na ta) (TypeDecl nb tb) = na == nb && ta == tb
  (==) _ _ = False

public export
covering
Show Decl where
  show (Fn n ps r e) = "Fn " ++ show n ++ " " ++ show ps ++ " " ++ show r ++ " " ++ show e
  show (TypeDecl n t) = "TypeDecl " ++ show n ++ " " ++ show t

public export
record Module where
  constructor MkModule
  name : String
  decls : List Decl

public export
covering
Eq Module where
  (==) (MkModule n d) (MkModule n' d') = n == n' && d == d'

public export
covering
Show Module where
  show (MkModule n d) = "Module " ++ show n ++ " " ++ show d
