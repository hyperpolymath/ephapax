(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell *)

(** * Ephapax: A Linear Type System for Safe Memory Management

    Formal semantics in Coq using De Bruijn indices.

    Core principle: ephapax (once for all)
    Every linear resource must be used exactly once.

    De Bruijn indices eliminate variable shadowing, making
    typing_preserves_domain provable without name complications.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(** ** Variables and Names *)

(** Variables use De Bruijn indices — natural numbers indexing into
    the typing context. Index 0 is the most recently bound variable. *)
Definition var := nat.

(** Region names remain strings (they are not bound in the context). *)
Definition region_name := string.

(** ** Linearity Annotations *)

Inductive linearity : Type :=
  | Lin    (* Linear: must use exactly once *)
  | Unr.   (* Unrestricted: may use any number of times *)

(** ** Base Types *)

Inductive base_ty : Type :=
  | TUnit
  | TBool
  | TI32
  | TI64
  | TF32
  | TF64.

(** ** Types with Region Annotations *)

Inductive ty : Type :=
  | TBase   : base_ty -> ty
  | TString : region_name -> ty
  | TRef    : linearity -> ty -> ty
  | TFun    : ty -> ty -> ty
  | TProd   : ty -> ty -> ty
  | TSum    : ty -> ty -> ty
  | TRegion : region_name -> ty -> ty
  | TBorrow : ty -> ty.

(** ** Expressions *)

Inductive expr : Type :=
  (* Values *)
  | EUnit   : expr
  | EBool   : bool -> expr
  | EI32    : nat -> expr
  | EVar    : var -> expr                            (* De Bruijn index *)

  (* String operations *)
  | EStringNew    : region_name -> string -> expr
  | EStringConcat : expr -> expr -> expr
  | EStringLen    : expr -> expr

  (* Control flow — binders use index 0 for the bound variable *)
  | ELet    : expr -> expr -> expr                   (* let = e1 in e2 *)
  | ELetLin : expr -> expr -> expr                   (* let! = e1 in e2 *)
  | EIf     : expr -> expr -> expr -> expr

  (* Functions *)
  | ELam    : ty -> expr -> expr                     (* fn(:T) -> e *)
  | EApp    : expr -> expr -> expr

  (* Products *)
  | EPair   : expr -> expr -> expr
  | EFst    : expr -> expr
  | ESnd    : expr -> expr

  (* Sums *)
  | EInl    : ty -> expr -> expr
  | EInr    : ty -> expr -> expr
  | ECase   : expr -> expr -> expr -> expr           (* case e of inl -> e1 | inr -> e2 *)

  (* Regions *)
  | ERegion : region_name -> expr -> expr

  (* Borrowing *)
  | EBorrow : expr -> expr
  | EDeref  : expr -> expr

  (* Explicit resource management *)
  | EDrop   : expr -> expr
  | ECopy   : expr -> expr

  (* Runtime-only values *)
  | ELoc    : nat -> region_name -> expr.

(** ** Values *)

Inductive is_value : expr -> Prop :=
  | VUnit   : is_value EUnit
  | VBool   : forall b, is_value (EBool b)
  | VI32    : forall n, is_value (EI32 n)
  | VLam    : forall T e, is_value (ELam T e)
  | VPair   : forall v1 v2, is_value v1 -> is_value v2 -> is_value (EPair v1 v2)
  | VInl    : forall T v, is_value v -> is_value (EInl T v)
  | VInr    : forall T v, is_value v -> is_value (EInr T v)
  | VLoc    : forall l r, is_value (ELoc l r).

(** ** Typing Contexts (De Bruijn) *)

(** A typing context is a list of (type, used?) pairs.
    Position in the list IS the variable index.
    Index 0 = head of list = most recently bound. *)

Definition ctx := list (ty * bool).

(** Context lookup by De Bruijn index. *)
Definition ctx_lookup (G : ctx) (i : var) : option (ty * bool) :=
  nth_error G i.

(** Mark variable at index i as used. *)
Fixpoint ctx_mark_used (G : ctx) (i : var) : ctx :=
  match G, i with
  | [], _ => []
  | (T, _) :: G', 0 => (T, true) :: G'
  | entry :: G', S i' => entry :: ctx_mark_used G' i'
  end.

(** Extend context with a new binding (prepend — index 0). *)
Definition ctx_extend (G : ctx) (T : ty) : ctx :=
  (T, false) :: G.

(** Check if a type is linear *)
Fixpoint is_linear_ty (T : ty) : bool :=
  match T with
  | TString _ => true
  | TRef Lin _ => true
  | TRegion _ T' => is_linear_ty T'
  | _ => false
  end.

(** Check if all linear variables in context have been used *)
Fixpoint ctx_all_linear_used (G : ctx) : Prop :=
  match G with
  | [] => True
  | (T, used) :: G' =>
      (is_linear_ty T = true -> used = true) /\ ctx_all_linear_used G'
  end.

(** ** De Bruijn Shifting and Substitution

    Standard infrastructure for substitution-based operational semantics.

    shift c d e — increment free variables >= cutoff c by amount d
    subst k s e — replace variable k with expression s, decrement vars > k

    DESIGN NOTE (2026-03-28): The original environment-based semantics had
    an environment-leaking bug where congruence rules (S_Let_Step etc.)
    propagated environment extensions from sub-expression evaluation to
    sibling expressions, making preservation genuinely false for nested
    binding reductions. Substitution-based semantics eliminates this class
    of bugs by resolving bindings at reduction time. *)

(** Shift free variables >= cutoff by amount d *)
Fixpoint shift (c : nat) (d : nat) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EI32 n => EI32 n
  | EVar i => if Nat.leb c i then EVar (i + d) else EVar i
  | EStringNew r s => EStringNew r s
  | EStringConcat e1 e2 => EStringConcat (shift c d e1) (shift c d e2)
  | EStringLen e0 => EStringLen (shift c d e0)
  | ELet e1 e2 => ELet (shift c d e1) (shift (S c) d e2)
  | ELetLin e1 e2 => ELetLin (shift c d e1) (shift (S c) d e2)
  | EIf e1 e2 e3 => EIf (shift c d e1) (shift c d e2) (shift c d e3)
  | ELam T e0 => ELam T (shift (S c) d e0)
  | EApp e1 e2 => EApp (shift c d e1) (shift c d e2)
  | EPair e1 e2 => EPair (shift c d e1) (shift c d e2)
  | EFst e0 => EFst (shift c d e0)
  | ESnd e0 => ESnd (shift c d e0)
  | EInl T e0 => EInl T (shift c d e0)
  | EInr T e0 => EInr T (shift c d e0)
  | ECase e0 e1 e2 => ECase (shift c d e0) (shift (S c) d e1) (shift (S c) d e2)
  | ERegion r e0 => ERegion r (shift c d e0)
  | EBorrow e0 => EBorrow (shift c d e0)
  | EDeref e0 => EDeref (shift c d e0)
  | EDrop e0 => EDrop (shift c d e0)
  | ECopy e0 => ECopy (shift c d e0)
  | ELoc l r => ELoc l r
  end.

(** Substitution: replace variable k with s, decrementing vars > k.
    Under binders, k increments and s is shifted up. *)
Fixpoint subst (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EI32 n => EI32 n
  | EVar i => if Nat.eqb i k then s
              else if Nat.ltb k i then EVar (i - 1)
              else EVar i
  | EStringNew r str => EStringNew r str
  | EStringConcat e1 e2 => EStringConcat (subst k s e1) (subst k s e2)
  | EStringLen e0 => EStringLen (subst k s e0)
  | ELet e1 e2 => ELet (subst k s e1) (subst (S k) (shift 0 1 s) e2)
  | ELetLin e1 e2 => ELetLin (subst k s e1) (subst (S k) (shift 0 1 s) e2)
  | EIf e1 e2 e3 => EIf (subst k s e1) (subst k s e2) (subst k s e3)
  | ELam T e0 => ELam T (subst (S k) (shift 0 1 s) e0)
  | EApp e1 e2 => EApp (subst k s e1) (subst k s e2)
  | EPair e1 e2 => EPair (subst k s e1) (subst k s e2)
  | EFst e0 => EFst (subst k s e0)
  | ESnd e0 => ESnd (subst k s e0)
  | EInl T e0 => EInl T (subst k s e0)
  | EInr T e0 => EInr T (subst k s e0)
  | ECase e0 e1 e2 => ECase (subst k s e0)
                             (subst (S k) (shift 0 1 s) e1)
                             (subst (S k) (shift 0 1 s) e2)
  | ERegion r e0 => ERegion r (subst k s e0)
  | EBorrow e0 => EBorrow (subst k s e0)
  | EDeref e0 => EDeref (subst k s e0)
  | EDrop e0 => EDrop (subst k s e0)
  | ECopy e0 => ECopy (subst k s e0)
  | ELoc l r => ELoc l r
  end.

(** Shifting preserves the value property *)
Lemma shift_preserves_value :
  forall c d v, is_value v -> is_value (shift c d v).
Proof.
  intros c d v Hv. induction Hv; simpl; try constructor; auto.
Qed.

(** ** Region Environment *)

Definition region_env := list region_name.

Definition region_active (R : region_env) (r : region_name) : Prop :=
  In r R.
