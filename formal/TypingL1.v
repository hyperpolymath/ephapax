(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Ephapax Typing Rules — L1 redesign (region capability threading)

    This file contains the **new** typing judgment as specified in
    [formal/PRESERVATION-DESIGN.md §4]. It coexists with the legacy
    [Typing.v] (`has_type`) so that the migration is incremental: old
    lemmas in [Semantics.v] continue to compile against the legacy
    judgment, and [Counterexample.v] gains a new lemma proving the
    L1 fix blocks the bad input.

    The judgment shape is:

      [R_in ; G ⊢ e : T -| R_out ; G']

    where [R_in] is the live-region capability set at the start of
    evaluating [e] and [R_out] is the live-region capability set
    after [e] has reduced to a value. Compound rules thread R
    left-to-right through sub-expressions, mirroring the existing
    G-threading. Region introduction / re-entry rules expose the
    capability shift caused by S_Region_Exit.

    Known limitation (documented for future work):
    - T_Lam_L1 requires the lambda body to be **R-preserving** (body's
      R_in = R_out). Without this, the function call's R-effect would
      need to be carried in TFun, which is an effect-typing extension
      beyond L1's scope. This is the same simplification echo-types
      makes by parameterising over a thin order rather than a fibration.

    See [formal/PRESERVATION-DESIGN.md §4] for the full design
    rationale and [Counterexample.v]'s new [bad_input_untypable_l1]
    lemma for the regression. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

From Ephapax Require Import Syntax.
From Ephapax Require Typing.  (* legacy judgment, for cross-reference only *)

(** ** Helper: remove the first occurrence of [r] from [R].

    Mirrors [remove_first] in [Semantics.v]; restated here so this
    file doesn't pull in the operational semantics. The two are
    pointwise equivalent. *)

Fixpoint remove_first_L1 (r : region_name) (R : region_env) : region_env :=
  match R with
  | [] => []
  | r' :: R' => if String.eqb r r' then R' else r' :: remove_first_L1 r R'
  end.

(** ** L1 Typing Judgement

    [R_in ; G ⊢ e : T -| R_out ; G']

    The shape mirrors [has_type] from [Typing.v] but adds a sixth
    parameter [R_out] threading the region capability set through
    every rule.

    For values (T_Unit, T_Bool, T_I32, T_Loc, T_StringNew, T_Var_*,
    T_Lam): [R_out = R_in], because evaluating a value does not
    consume regions.

    For compound forms (T_Pair, T_Let, T_LetLin, T_App, T_If, T_Case,
    T_StringConcat, T_Fst, T_Snd, T_Inl, T_Inr, T_Drop, T_Copy):
    [R_in] is threaded through the sub-expressions left-to-right,
    each child's [R_out] becoming the next child's [R_in].

    For region-introduction forms (T_Region, T_Region_Active): the
    body is typed in an environment containing [r]; the outer
    [R_out] equals the body's [R_body] minus one occurrence of [r],
    reflecting S_Region_Exit's operational effect. *)

Reserved Notation "R ';' G '|=L1' e ':' T '-|' R' ';' G'"
  (at level 70, G at next level, e at next level, T at next level, R' at next level).

Inductive has_type_l1
  : region_env -> ctx -> expr -> ty -> region_env -> ctx -> Prop :=

  (** ===== Values (R and G unchanged) ===== *)

  | T_Unit_L1 : forall R G,
      R ; G |=L1 EUnit : TBase TUnit -| R ; G

  | T_Bool_L1 : forall R G b,
      R ; G |=L1 EBool b : TBase TBool -| R ; G

  | T_I32_L1 : forall R G n,
      R ; G |=L1 EI32 n : TBase TI32 -| R ; G

  (** ===== Variables ===== *)

  (** T_Var_Lin_L1 and T_Var_Unr_L1 are strengthened with a
      region-well-formedness premise: every region mentioned in the
      variable's type must be live in [R]. This closes the soundness
      gap documented in PRESERVATION-DESIGN.md §4.8 (resolution path 3)
      and lets [region_liveness_at_split_l1] be discharged as a
      structural-induction lemma rather than an axiom. *)

  | T_Var_Lin_L1 : forall R G i T,
      ctx_lookup G i = Some (T, false) ->
      is_linear_ty T = true ->
      (forall r, In r (Typing.free_regions T) -> In r R) ->
      R ; G |=L1 EVar i : T -| R ; ctx_mark_used G i

  | T_Var_Unr_L1 : forall R G i T u,
      ctx_lookup G i = Some (T, u) ->
      is_linear_ty T = false ->
      (forall r, In r (Typing.free_regions T) -> In r R) ->
      R ; G |=L1 EVar i : T -| R ; G

  (** ===== Strings ===== *)

  | T_Loc_L1 : forall R G l r,
      In r R ->
      R ; G |=L1 ELoc l r : TString r -| R ; G

  | T_StringNew_L1 : forall R G r s,
      In r R ->
      R ; G |=L1 EStringNew r s : TString r -| R ; G

  | T_StringConcat_L1 : forall R R1 R2 G G' G'' e1 e2 r,
      R  ; G  |=L1 e1 : TString r -| R1 ; G' ->
      R1 ; G' |=L1 e2 : TString r -| R2 ; G'' ->
      R  ; G  |=L1 EStringConcat e1 e2 : TString r -| R2 ; G''

  | T_StringLen_L1 : forall R R' G G' e r,
      R ; G |=L1 EBorrow e : TBorrow (TString r) -| R' ; G' ->
      R ; G |=L1 EStringLen e : TBase TI32 -| R' ; G'

  (** ===== Let Bindings ===== *)

  | T_Let_L1 : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G                  |=L1 e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1 e2 : T2 -| R2 ; (T1, true) :: G'' ->
      R  ; G                  |=L1 ELet e1 e2 : T2 -| R2 ; G''

  | T_LetLin_L1 : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      is_linear_ty T1 = true ->
      R  ; G                  |=L1 e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1 e2 : T2 -| R2 ; (T1, true) :: G'' ->
      R  ; G                  |=L1 ELetLin e1 e2 : T2 -| R2 ; G''

  (** ===== Functions =====

      T_Lam_L1: the lambda *value* is R-preserving (introducing a
      value doesn't consume regions). The body must also be R-
      preserving (body's R_in = R_out = the lambda's R) so that
      function application's R-effect is fully captured by the
      arguments. This is restrictive — it forbids functions whose
      bodies have net region effects — but it is sound and
      sufficient for the counterexample regression. Effect-typed
      lambdas are documented as future work in §4 of the design. *)

  | T_Lam_L1 : forall R G T1 T2 e,
      R ; ctx_extend G T1 |=L1 e : T2 -| R ; (T1, true) :: G ->
      R ; G               |=L1 ELam T1 e : TFun T1 T2 -| R ; G

  | T_App_L1 : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G  |=L1 e1 : TFun T1 T2 -| R1 ; G' ->
      R1 ; G' |=L1 e2 : T1          -| R2 ; G'' ->
      R  ; G  |=L1 EApp e1 e2 : T2  -| R2 ; G''

  (** ===== Products ===== *)

  | T_Pair_L1 : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G  |=L1 e1 : T1 -| R1 ; G' ->
      R1 ; G' |=L1 e2 : T2 -| R2 ; G'' ->
      R  ; G  |=L1 EPair e1 e2 : TProd T1 T2 -| R2 ; G''

  | T_Fst_L1 : forall R R' G G' e T1 T2,
      R ; G |=L1 e : TProd T1 T2 -| R' ; G' ->
      is_linear_ty T2 = false ->
      R ; G |=L1 EFst e : T1 -| R' ; G'

  | T_Snd_L1 : forall R R' G G' e T1 T2,
      R ; G |=L1 e : TProd T1 T2 -| R' ; G' ->
      is_linear_ty T1 = false ->
      R ; G |=L1 ESnd e : T2 -| R' ; G'

  (** ===== Sums ===== *)

  | T_Inl_L1 : forall R R' G G' e T1 T2,
      R ; G |=L1 e : T1 -| R' ; G' ->
      R ; G |=L1 EInl T2 e : TSum T1 T2 -| R' ; G'

  | T_Inr_L1 : forall R R' G G' e T1 T2,
      R ; G |=L1 e : T2 -| R' ; G' ->
      R ; G |=L1 EInr T1 e : TSum T1 T2 -| R' ; G'

  (** T_Case_L1: branches must agree on BOTH R_out and G_out. *)
  | T_Case_L1 : forall R R1 R_final G G' G_final e e1 e2 T1 T2 T,
      R  ; G                |=L1 e  : TSum T1 T2 -| R1 ; G' ->
      R1 ; ctx_extend G' T1 |=L1 e1 : T -| R_final ; (T1, true) :: G_final ->
      R1 ; ctx_extend G' T2 |=L1 e2 : T -| R_final ; (T2, true) :: G_final ->
      R  ; G                |=L1 ECase e e1 e2 : T -| R_final ; G_final

  (** ===== Conditionals ===== *)

  | T_If_L1 : forall R R1 R2 G G' G'' e1 e2 e3 T,
      R  ; G  |=L1 e1 : TBase TBool -| R1 ; G' ->
      R1 ; G' |=L1 e2 : T           -| R2 ; G'' ->
      R1 ; G' |=L1 e3 : T           -| R2 ; G'' ->
      R  ; G  |=L1 EIf e1 e2 e3 : T -| R2 ; G''

  (** ===== Regions =====

      T_Region_L1 (fresh introduction): r is NOT in R_in. Body typed
      in (r :: R_in). Body's R_body is whatever the body leaves
      (possibly r-internal exits). Outer R_out = remove_first r R_body
      reflects the operational S_Region_Exit popping r.

      Premise [In r R_body] ensures the operational exit can fire;
      without it, the typing would admit configurations where the
      runtime gets stuck. *)

  | T_Region_L1 : forall R R_body G G' r e T,
      ~ In r R ->
      ~ In r (Typing.free_regions T) ->
      In r R_body ->
      (r :: R) ; G |=L1 e : T -| R_body ; G' ->
      R ; G |=L1 ERegion r e : T -| remove_first_L1 r R_body ; G'

  (** T_Region_Active_L1 (re-entry of a live region): r IS in R_in.
      Body typed in R_in. Outer R_out = remove_first r R_body. *)

  | T_Region_Active_L1 : forall R R_body G G' r e T,
      In r R ->
      ~ In r (Typing.free_regions T) ->
      In r R_body ->
      R ; G |=L1 e : T -| R_body ; G' ->
      R ; G |=L1 ERegion r e : T -| remove_first_L1 r R_body ; G'

  (** ===== Borrowing ===== *)

  | T_Borrow_L1 : forall R G i T,
      ctx_lookup G i = Some (T, false) ->
      R ; G |=L1 EBorrow (EVar i) : TBorrow T -| R ; G

  | T_Borrow_Val_L1 : forall R G v T,
      is_value v ->
      R ; G |=L1 v : T -| R ; G ->
      R ; G |=L1 EBorrow v : TBorrow T -| R ; G

  (** ===== Explicit Resource Management ===== *)

  | T_Drop_L1 : forall R R' G G' e T,
      is_linear_ty T = true ->
      R ; G |=L1 e : T -| R' ; G' ->
      R ; G |=L1 EDrop e : TBase TUnit -| R' ; G'

  | T_Copy_L1 : forall R R' G G' e T,
      is_linear_ty T = false ->
      R ; G |=L1 e : T -| R' ; G' ->
      R ; G |=L1 ECopy e : TProd T T -| R' ; G'

where "R ';' G '|=L1' e ':' T '-|' R' ';' G'" := (has_type_l1 R G e T R' G').

(** ** Trivial sanity check on the new judgment.

    Every value rule preserves both R and G. This is by inspection
    of the rule shapes above, not a deep theorem. Documented here
    so future readers can re-derive the property without re-reading
    every rule. *)

Lemma value_rules_preserve_R_G_l1 :
  forall G,
    (forall R, R ; G |=L1 EUnit : TBase TUnit -| R ; G) /\
    (forall R b, R ; G |=L1 EBool b : TBase TBool -| R ; G) /\
    (forall R n, R ; G |=L1 EI32 n : TBase TI32 -| R ; G).
Proof.
  intros G. split; [|split]; intros.
  - apply T_Unit_L1.
  - apply T_Bool_L1.
  - apply T_I32_L1.
Qed.
