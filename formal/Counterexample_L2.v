(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Soundness gap (L2): preservation_l2 fails for TFunEff substituends
      inside fresh-region scopes

    The Phase D slice 4 Phase 4c β-case of preservation_l2 fails for
    programs that substitute a TFunEff value into a body containing
    [ERegion] (fresh-region) introduction.

    This file mechanises the counterexample. It mirrors the structure
    of [Counterexample.v] (which exhibits the legacy preservation's
    soundness gap) but at the L1/L2 layer with the post-redesign
    [has_type_l1] / [has_type_l2] judgments. The artifact justifies
    the **conditional** preservation_l2 closure recommended in
    [SUBST-LEMMA-GENERALIZATION-DESIGN.md] §"Phase 4c": preservation
    holds only for programs satisfying
    [regions_introduced_by(ebody) ⊆ R_in_v]; programs outside this
    class form a documented soundness-gap subclass.

    ===== Configuration =====

      T1_inner    := TFunEff TUnit TUnit [] []      (* substituee type, R_in_v = [] *)
      outer       := ELam T1_inner (ERegion r2 (EVar 0))
                                                    (* body introduces fresh r2, returns subst position *)
      v2          := ELam TUnit EUnit               (* a value of type T1_inner *)
      e_before    := EApp outer v2                  (* well-typed via T_App_L2_Eff at R = [] *)
      e_after     := ERegion r2 v2                  (* β-result: subst 0 v2 (ERegion r2 (EVar 0)) *)

    ===== Three theorems =====

    - [e_before_typed] — the input types at outer type [T1_inner]
      via T_App_L2_Eff with mode Affine.
    - [e_step]         — operational step S_App_Fun reduces e_before
      to e_after.
    - [e_after_untypable] — no L1 derivation exists for e_after at
      the same outer type. By inversion: the only ERegion-producing
      rules at non-TEcho output are T_Region_L1 and T_Region_Active_L1;
      T_Region_Active_L1 requires [In r2 []] (fails); T_Region_L1's
      body premise requires v2 typed at [r2; nil], which only
      [T_Lam_L1_*_Eff] can produce, and both rules' side condition
      [forall r, In r [r2] -> In r R_in_v = []] is contradicted by
      [In r2 [r2]].

    ===== Owner-directive compliance =====

    - Does not modify [Semantics.v] or [Counterexample.v] (the legacy
      soundness-gap artifacts).
    - Does not patch [Typing.v].
    - Does not close any residual proof-debt in [Semantics_L1.v].
    - Adds NEW infrastructure (a new file in [formal/]) orthogonal
      to legacy proof-debt, mirroring the precedent of [Counterexample.v]
      for the legacy preservation.
    - Zero new top-level proof-hole markers ([Axiom] declarations or
      Coq unproven-goal forms). *)

From Ephapax Require Import Syntax Typing TypingL1 Modality Semantics Semantics_L1 TypingL2.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Section CounterexampleL2.

  Definition r2 : region_name := "r2".

  (** Substituee type — a TFunEff lambda with empty input region env. *)
  Definition T1_inner : ty :=
    TFunEff (TBase TUnit) (TBase TUnit) [] [].

  (** Outer lambda: takes a [T1_inner]-typed argument, returns it
      inside a fresh-region scope [ERegion r2]. The bound variable
      is referenced at de Bruijn index 0 inside the region scope. *)
  Definition outer : expr :=
    ELam T1_inner (ERegion r2 (EVar 0)).

  (** Argument: a TFunEff lambda of type [T1_inner]. The body
      [EUnit] is trivially typed at any R. *)
  Definition v2 : expr :=
    ELam (TBase TUnit) EUnit.

  (** Pre-step term. *)
  Definition e_before : expr := EApp outer v2.

  (** Post-β term: [subst 0 v2 (ERegion r2 (EVar 0))]
      [= ERegion r2 (subst 0 v2 (EVar 0))]  (* ERegion isn't a binder *)
      [= ERegion r2 v2]                     (* EVar 0 substitutes to v2 *) *)
  Definition e_after : expr := ERegion r2 v2.

  (** Helper: v2 types at [T1_inner] at any R (it's a closed value
      whose formation side condition has R_in_v = [] so [R ⊆ []]
      means R = []). For the proof below we only need v2 at R = []
      and at R = [r2] — the latter is what fails. *)

  Lemma v2_typed_at_empty :
    has_type_l1 Affine [] [] v2 T1_inner [] [].
  Proof.
    unfold v2, T1_inner.
    eapply T_Lam_L1_Affine_Eff with (u := false).
    - intros r Hr; inversion Hr.
    - apply T_Unit_L1.
  Qed.

  (** Outer lambda is well-typed at [TFunEff T1_inner T1_inner [] []]. *)

  Lemma outer_typed :
    has_type_l1 Affine [] [] outer
                (TFunEff T1_inner T1_inner [] []) [] [].
  Proof.
    unfold outer.
    eapply T_Lam_L1_Affine_Eff with (u := false).
    - intros r Hr; inversion Hr.
    - eapply T_Region_L1 with (R_body := [r2]).
      + intros Hr; inversion Hr.
      + simpl. intros Hr. inversion Hr.
      + left; reflexivity.
      + eapply T_Var_Unr_L1.
        * unfold ctx_lookup; simpl. reflexivity.
        * reflexivity.
  Qed.

  (** ===== (a) e_before is well-typed via T_App_L2_Eff ===== *)

  Lemma e_before_typed :
    has_type_l2 Affine [] [] e_before T1_inner [] [].
  Proof.
    unfold e_before.
    eapply T_App_L2_Eff.
    - apply L2_lift_l1. exact outer_typed.
    - apply L2_lift_l1. exact v2_typed_at_empty.
  Qed.

  (** ===== (b) The β-step from e_before to e_after ===== *)

  Lemma e_step :
    forall mu, step (mu, [], e_before) (mu, [], e_after).
  Proof.
    intros mu. unfold e_before, e_after, outer.
    (* [subst 0 v2 (ERegion r2 (EVar 0))] reduces to [ERegion r2 v2]
       by the [subst] Fixpoint (ERegion is not a binder so no shift). *)
    change (ERegion r2 v2) with (subst 0 v2 (ERegion r2 (EVar 0))).
    apply S_App_Fun. unfold v2. apply VLam.
  Qed.

  (** ===== (c) e_after does NOT type at the same outer type =====

      No L1 derivation exists for [[] ; [] |=L1[Affine] e_after :
      T1_inner -| ?R_out; ?G_out].

      Proof by inversion on the assumed derivation. ERegion expressions
      are produced by exactly four constructors:
      - [T_Region_L1]        — output type [T] (matches T1_inner)
      - [T_Region_Active_L1] — output type [T] (matches but requires
                                [In r2 []], false)
      - [T_Region_L1_Echo]   — output type [TEcho T] (≠ T1_inner)
      - [T_Region_Active_L1_Echo] — output type [TEcho T] (≠ T1_inner)

      The two Echo cases discriminate on the output-type equation.
      The T_Region_Active_L1 case fails [In r2 []].
      The T_Region_L1 case requires v2 typed at [r2; nil]; v2 = ELam
      types only via [T_Lam_L1_*_Eff], both of whose side conditions
      [forall r, In r [r2] -> In r R_in_v = []] are contradicted by
      [In r2 [r2]]. *)

  Lemma e_after_untypable :
    forall R_out G_out,
      ~ has_type_l1 Affine [] [] e_after T1_inner R_out G_out.
  Proof.
    intros R_out G_out Ht.
    unfold e_after, v2, T1_inner in Ht.
    inversion Ht; subst.
    - (* T_Region_L1 case: body v2 typed at [r2;nil]. *)
      match goal with
      | [ Hbody : has_type_l1 _ (r2 :: _) _ (ELam _ _) _ _ _ |- _ ] =>
          rename Hbody into Hv2_inner
      end.
      inversion Hv2_inner; subst.
      (* Only T_Lam_L1_Affine_Eff survives — T_Lam_L1_Linear / _Affine
         produce TFun (discriminated), and T_Lam_L1_Linear_Eff is mode
         Linear (discriminated against Hv2_inner's Affine mode). *)
      match goal with
      | [ Hside : forall r, In r (r2 :: nil) -> In r nil |- _ ] =>
          specialize (Hside r2 (or_introl eq_refl)); inversion Hside
      end.
    - (* T_Region_Active_L1 case: requires In r2 nil, false. *)
      match goal with
      | [ Hr2_in_R : In r2 nil |- _ ] => inversion Hr2_in_R
      end.
  Qed.

  (** ===== Soundness-gap witness =====

      The three lemmas above ([e_before_typed] + [e_step] +
      [e_after_untypable]) jointly witness preservation_l2's failure
      for the TFunEff-substituee-inside-fresh-region class. No
      top-level conjunction theorem is stated because [has_type_l2]
      is Type-sorted (it is proof-relevant per L2's design) while
      [step] and [~ has_type_l1] are Prop, so a Prop-conjunction over
      the three would require either a [prod]-based product or
      [inhabited]-wrapping. Keeping them as three separate lemmas
      preserves the strongest form of each statement. *)

End CounterexampleL2.
