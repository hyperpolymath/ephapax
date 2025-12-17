(* SPDX-License-Identifier: EUPL-1.2 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)

(** * Ephapax Typing Rules

    Linear typing judgement: R; G |- e : T -| G'

    Where:
    - R is the active region environment
    - G is the input context
    - e is the expression
    - T is the type
    - G' is the output context (tracking linear resource consumption)
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Syntax.

(** ** Helper: extract variable from simple expressions *)

Definition var_of_expr (e : expr) : var :=
  match e with
  | EVar x => x
  | _ => ""%string  (* Fallback - real impl would be partial *)
  end.

(** ** Linear Typing Judgement *)

Reserved Notation "R ';' G '|-' e ':' T '-|' G'"
  (at level 70, G at next level, e at next level, T at next level).

Inductive has_type : region_env -> ctx -> expr -> ty -> ctx -> Prop :=

  (** ===== Values ===== *)

  | T_Unit : forall R G,
      R; G |- EUnit : TBase TUnit -| G

  | T_Bool : forall R G b,
      R; G |- EBool b : TBase TBool -| G

  | T_I32 : forall R G n,
      R; G |- EI32 n : TBase TI32 -| G

  (** ===== Variables ===== *)

  (** Linear variable: must mark as used *)
  | T_Var_Lin : forall R G x T,
      ctx_lookup G x = Some (T, false) ->
      is_linear_ty T = true ->
      R; G |- EVar x : T -| ctx_mark_used G x

  (** Unrestricted variable: no change to context *)
  | T_Var_Unr : forall R G x T u,
      ctx_lookup G x = Some (T, u) ->
      is_linear_ty T = false ->
      R; G |- EVar x : T -| G

  (** ===== Strings ===== *)

  (** String allocation in region *)
  | T_StringNew : forall R G r s,
      region_active R r ->
      R; G |- EStringNew r s : TString r -| G

  (** String concatenation: consumes both operands (linear) *)
  | T_StringConcat : forall R G G' G'' e1 e2 r,
      R; G  |- e1 : TString r -| G' ->
      R; G' |- e2 : TString r -| G'' ->
      R; G  |- EStringConcat e1 e2 : TString r -| G''

  (** String length: borrows the string (does not consume) *)
  | T_StringLen : forall R G G' e r,
      R; G |- EBorrow e : TBorrow (TString r) -| G' ->
      R; G |- EStringLen e : TBase TI32 -| G'

  (** ===== Let Bindings ===== *)

  (** Standard let: binds result of e1, uses in e2 *)
  | T_Let : forall R G G' G'' x e1 e2 T1 T2,
      R; G |- e1 : T1 -| G' ->
      R; ctx_extend G' x T1 |- e2 : T2 -| (x, T1, true) :: G'' ->
      R; G |- ELet x e1 e2 : T2 -| G''

  (** Linear let: explicitly marks binding as linear *)
  | T_LetLin : forall R G G' G'' x e1 e2 T1 T2,
      is_linear_ty T1 = true ->
      R; G |- e1 : T1 -| G' ->
      R; ctx_extend G' x T1 |- e2 : T2 -| (x, T1, true) :: G'' ->
      R; G |- ELetLin x e1 e2 : T2 -| G''

  (** ===== Functions ===== *)

  (** Lambda abstraction *)
  | T_Lam : forall R G x T1 T2 e,
      R; ctx_extend G x T1 |- e : T2 -| (x, T1, true) :: G ->
      R; G |- ELam x T1 e : TFun T1 T2 -| G

  (** Function application *)
  | T_App : forall R G G' G'' e1 e2 T1 T2,
      R; G  |- e1 : TFun T1 T2 -| G' ->
      R; G' |- e2 : T1 -| G'' ->
      R; G  |- EApp e1 e2 : T2 -| G''

  (** ===== Products ===== *)

  | T_Pair : forall R G G' G'' e1 e2 T1 T2,
      R; G  |- e1 : T1 -| G' ->
      R; G' |- e2 : T2 -| G'' ->
      R; G  |- EPair e1 e2 : TProd T1 T2 -| G''

  (** Projections consume the pair if either component is linear *)
  | T_Fst : forall R G G' e T1 T2,
      R; G |- e : TProd T1 T2 -| G' ->
      is_linear_ty T2 = false ->  (* T2 must be droppable *)
      R; G |- EFst e : T1 -| G'

  | T_Snd : forall R G G' e T1 T2,
      R; G |- e : TProd T1 T2 -| G' ->
      is_linear_ty T1 = false ->  (* T1 must be droppable *)
      R; G |- ESnd e : T2 -| G'

  (** ===== Sums ===== *)

  | T_Inl : forall R G G' e T1 T2,
      R; G |- e : T1 -| G' ->
      R; G |- EInl T2 e : TSum T1 T2 -| G'

  | T_Inr : forall R G G' e T1 T2,
      R; G |- e : T2 -| G' ->
      R; G |- EInr T1 e : TSum T1 T2 -| G'

  (** Case: both branches must consume linear resources identically *)
  | T_Case : forall R G G' G_final e x1 e1 x2 e2 T1 T2 T,
      R; G |- e : TSum T1 T2 -| G' ->
      R; ctx_extend G' x1 T1 |- e1 : T -| (x1, T1, true) :: G_final ->
      R; ctx_extend G' x2 T2 |- e2 : T -| (x2, T2, true) :: G_final ->
      R; G |- ECase e x1 e1 x2 e2 : T -| G_final

  (** ===== Conditionals ===== *)

  (** Both branches must produce same output context *)
  | T_If : forall R G G' G'' e1 e2 e3 T,
      R; G |- e1 : TBase TBool -| G' ->
      R; G' |- e2 : T -| G'' ->
      R; G' |- e3 : T -| G'' ->
      R; G |- EIf e1 e2 e3 : T -| G''

  (** ===== Regions ===== *)

  (** Region introduction: all allocations in e scoped to r *)
  | T_Region : forall R G G' r e T,
      ~ In r R ->  (* Fresh region name *)
      (r :: R); G |- e : T -| G' ->
      (* All strings allocated in r must be consumed before region exit *)
      R; G |- ERegion r e : T -| G'

  (** ===== Borrowing ===== *)

  (** Create a borrow: does not consume the resource *)
  | T_Borrow : forall R G e T,
      ctx_lookup G (var_of_expr e) = Some (T, false) ->
      R; G |- EBorrow e : TBorrow T -| G

  (** ===== Explicit Resource Management ===== *)

  (** Drop: explicitly consume a linear resource *)
  | T_Drop : forall R G G' e T,
      is_linear_ty T = true ->
      R; G |- e : T -| G' ->
      R; G |- EDrop e : TBase TUnit -| G'

  (** Copy: only allowed for unrestricted types *)
  | T_Copy : forall R G G' e T,
      is_linear_ty T = false ->
      R; G |- e : T -| G' ->
      R; G |- ECopy e : TProd T T -| G'

where "R ';' G '|-' e ':' T '-|' G'" := (has_type R G e T G').

(** ** Linearity Theorem (statement)

    If R; G |- e : T -| G' and e evaluates to a value,
    then all linear resources in G have been used exactly once.
*)

Theorem linearity_preservation :
  forall R G e T G',
    R; G |- e : T -| G' ->
    ctx_all_linear_used G'.
Proof.
  (* Proof by induction on typing derivation - stubbed *)
Admitted.
