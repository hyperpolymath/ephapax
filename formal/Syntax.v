(* SPDX-License-Identifier: EUPL-1.2 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)

(** * Ephapax: A Linear Type System for Safe Memory Management

    Formal semantics in Coq.

    Core principle: ephapax (once for all)
    Every linear resource must be used exactly once.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Variables and Names *)

Definition var := string.
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
  | TString : region_name -> ty                    (* String allocated in region *)
  | TRef    : linearity -> ty -> ty                (* Reference with linearity *)
  | TFun    : ty -> ty -> ty                       (* Function type A -> B *)
  | TProd   : ty -> ty -> ty                       (* Product type A * B *)
  | TSum    : ty -> ty -> ty                       (* Sum type A + B *)
  | TRegion : region_name -> ty -> ty              (* Region-scoped type *)
  | TBorrow : ty -> ty.                            (* Second-class borrow &T *)

(** ** Expressions *)

Inductive expr : Type :=
  (* Values *)
  | EUnit   : expr
  | EBool   : bool -> expr
  | EI32    : nat -> expr                          (* Simplified: using nat *)
  | EVar    : var -> expr

  (* String operations *)
  | EStringNew    : region_name -> string -> expr  (* String.new@r("...") *)
  | EStringConcat : expr -> expr -> expr           (* Consumes both operands *)
  | EStringLen    : expr -> expr                   (* Borrows operand *)

  (* Control flow *)
  | ELet    : var -> expr -> expr -> expr          (* let x = e1 in e2 *)
  | ELetLin : var -> expr -> expr -> expr          (* let! x = e1 in e2 (linear) *)
  | EIf     : expr -> expr -> expr -> expr

  (* Functions *)
  | ELam    : var -> ty -> expr -> expr            (* fn(x:T) -> e *)
  | EApp    : expr -> expr -> expr

  (* Products *)
  | EPair   : expr -> expr -> expr
  | EFst    : expr -> expr
  | ESnd    : expr -> expr

  (* Sums *)
  | EInl    : ty -> expr -> expr
  | EInr    : ty -> expr -> expr
  | ECase   : expr -> var -> expr -> var -> expr -> expr

  (* Regions *)
  | ERegion : region_name -> expr -> expr          (* region r: e *)

  (* Borrowing *)
  | EBorrow : expr -> expr                         (* &e *)
  | EDeref  : expr -> expr                         (* *e *)

  (* Explicit resource management *)
  | EDrop   : expr -> expr                         (* Explicitly consume/drop *)
  | ECopy   : expr -> expr.                        (* Explicit copy (unrestricted only) *)

(** ** Values *)

Inductive is_value : expr -> Prop :=
  | VUnit   : is_value EUnit
  | VBool   : forall b, is_value (EBool b)
  | VI32    : forall n, is_value (EI32 n)
  | VLam    : forall x T e, is_value (ELam x T e)
  | VPair   : forall v1 v2, is_value v1 -> is_value v2 -> is_value (EPair v1 v2)
  | VInl    : forall T v, is_value v -> is_value (EInl T v)
  | VInr    : forall T v, is_value v -> is_value (EInr T v).

(** ** Typing Contexts *)

(** A typing context tracks variables and their types, along with
    whether they have been "used" (for linear variables). *)

Definition ctx := list (var * ty * bool).  (* (name, type, used?) *)

(** Context operations *)

Fixpoint ctx_lookup (G : ctx) (x : var) : option (ty * bool) :=
  match G with
  | [] => None
  | (y, T, u) :: G' =>
      if String.eqb x y then Some (T, u)
      else ctx_lookup G' x
  end.

Fixpoint ctx_mark_used (G : ctx) (x : var) : ctx :=
  match G with
  | [] => []
  | (y, T, u) :: G' =>
      if String.eqb x y then (y, T, true) :: G'
      else (y, T, u) :: ctx_mark_used G' x
  end.

Definition ctx_extend (G : ctx) (x : var) (T : ty) : ctx :=
  (x, T, false) :: G.

(** Check if all linear variables in context have been used *)

Fixpoint is_linear_ty (T : ty) : bool :=
  match T with
  | TString _ => true
  | TRef Lin _ => true
  | TRegion _ T' => is_linear_ty T'
  | _ => false
  end.

Fixpoint ctx_all_linear_used (G : ctx) : Prop :=
  match G with
  | [] => True
  | (_, T, used) :: G' =>
      (is_linear_ty T = true -> used = true) /\ ctx_all_linear_used G'
  end.

(** ** Region Environment *)

Definition region_env := list region_name.

Definition region_active (R : region_env) (r : region_name) : Prop :=
  In r R.
