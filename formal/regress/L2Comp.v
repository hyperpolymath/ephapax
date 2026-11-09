(* SPDX-License-Identifier: MPL-2.0 *)
(** * L2Comp — [has_type_l2] does not compose.

    [has_type_l2] (TypingL2.v) has exactly two constructors:
    [L2_lift_l1] (any [has_type_l1] derivation) and [T_App_L2_Eff]
    (application of a [TFunEff]). There is no L2-level pair / let /
    lambda / region rule, and [has_type_l1] has no rule eliminating
    [TFunEff]. So an effect-typed application, once formed by
    [T_App_L2_Eff], cannot be placed inside any compound form.

    "Compose" here means the L1 pairing rule [T_Pair_L1], lifted to L2:
      L2 ⊢ e1 : T1 [R→R1, G→G1] and L2 ⊢ e2 : T2 [R1→R2, G1→G2]
        ⟹ L2 ⊢ EPair e1 e2 : TProd T1 T2 [R→R2, G→G2].
    We exhibit two L2-typable parts whose pair is untypable at every
    type and output, so this closure property fails. *)

From Ephapax Require Import Syntax Typing TypingL1 Semantics Semantics_L1 Modality TypingL2.
Require Import Coq.Lists.List Coq.Strings.String. Import ListNotations.
Open Scope string_scope.

Definition r : region_name := "r".

(** A lambda whose body exits the already-active region [r]: not
    R-preserving, so it is typable only at [TFunEff], never at [TFun]. *)
Definition lam : expr := ELam (TBase TUnit) (ERegion r EUnit).
Definition app : expr := EApp lam EUnit.
Definition composed : expr := EPair app EUnit.

Lemma lam_typed_eff :
  has_type_l1 Affine [r] [] lam (TFunEff (TBase TUnit) (TBase TUnit) [r] []) [r] [].
Proof.
  unfold lam. apply (T_Lam_L1_Affine_Eff [r] [] _ _ _ false [r] []).
  - auto.
  - change (@nil region_name) with (remove_first_L1 r [r]).
    apply T_Region_Active_L1; [simpl; auto | simpl; intros [] | simpl; auto | apply T_Unit_L1].
Qed.

(** Part 1: the application is L2-typable (via [T_App_L2_Eff]). *)
Definition app_typed_l2 :
  has_type_l2 Affine [r] [] app (TBase TUnit) [] [].
Proof.
  eapply T_App_L2_Eff.
  - apply L2_lift_l1. exact lam_typed_eff.
  - apply L2_lift_l1. apply T_Unit_L1.
Defined.

(** Part 2: [EUnit] is L2-typable at the output of part 1. *)
Definition unit_typed_l2 :
  has_type_l2 Affine [] [] EUnit (TBase TUnit) [] [].
Proof. apply L2_lift_l1. apply T_Unit_L1. Defined.

(** Exiting an already-active region [r] around [EUnit] removes [r]. *)
Lemma region_unit_active_out :
  forall m R G T R' G',
    In r R ->
    has_type_l1 m R G (ERegion r EUnit) T R' G' ->
    R' = remove_first_L1 r R.
Proof.
  intros m R G T R' G' Hin H.
  inversion H; subst;
  try (exfalso; match goal with Hn : ~ In r _ |- _ => apply Hn; exact Hin end);
  match goal with Hu : has_type_l1 _ _ _ EUnit _ _ _ |- _ =>
    inversion Hu; subst; reflexivity end.
Qed.

(** Key L1 fact: at [R = [r]], [lam] has no [TFun] typing, in any mode. *)
Lemma lam_not_tfun_l1 :
  forall m G T1 T2 R' G', ~ has_type_l1 m [r] G lam (TFun T1 T2) R' G'.
Proof.
  intros m G T1 T2 R' G' H. unfold lam in H.
  inversion H; subst;
  match goal with Hb : has_type_l1 _ [r] _ (ERegion r EUnit) _ [r] _ |- _ =>
    apply region_unit_active_out in Hb; [cbn in Hb; discriminate | simpl; auto] end.
Qed.

(** Hence [app] has no L1 typing at [R = [r]] (only [T_App_L1] could apply). *)
Lemma app_not_l1 :
  forall m G T R' G', ~ has_type_l1 m [r] G app T R' G'.
Proof.
  intros m G T R' G' H. unfold app in H. inversion H; subst.
  eapply lam_not_tfun_l1; eassumption.
Qed.

(** Headline 1: the composed term is untypable in L2, at every
    modality, type and output. *)
Theorem composed_untypable_l2 :
  forall m T R' G', has_type_l2 m [r] [] composed T R' G' -> False.
Proof.
  intros m T R' G' H. inversion H; subst.
  (* only L2_lift_l1 matches an EPair *)
  match goal with Hl : has_type_l1 _ _ _ composed _ _ _ |- _ =>
    unfold composed in Hl; inversion Hl; subst end.
  eapply app_not_l1; eassumption.
Qed.

(** Headline 2: the lifted pairing rule is not admissible for [has_type_l2]
    (stated as [... -> False] because [has_type_l2] lives in [Type]). *)
Theorem l2_pair_composition_fails :
  (forall m R R1 R2 G G1 G2 e1 e2 T1 T2,
       has_type_l2 m R G e1 T1 R1 G1 ->
       has_type_l2 m R1 G1 e2 T2 R2 G2 ->
       has_type_l2 m R G (EPair e1 e2) (TProd T1 T2) R2 G2) -> False.
Proof.
  intro Hcomp.
  exact (composed_untypable_l2 _ _ _ _
           (Hcomp _ _ _ _ _ _ _ _ _ _ _ app_typed_l2 unit_typed_l2)).
Qed.

(** ** Linear-mode variant (the strict ephapax-linear core).
    The parameter is a linear [TString r], consumed by [EDrop]; the
    argument is the runtime location [ELoc 0 r]. *)
Definition lam_lin : expr :=
  ELam (TString r) (EPair (EDrop (EVar 0)) (ERegion r EUnit)).
Definition app_lin : expr := EApp lam_lin (ELoc 0 r).
Definition composed_lin : expr := EPair app_lin EUnit.

Lemma lam_lin_typed_eff :
  has_type_l1 Linear [r] [] lam_lin
    (TFunEff (TString r) (TProd (TBase TUnit) (TBase TUnit)) [r] []) [r] [].
Proof.
  unfold lam_lin. apply T_Lam_L1_Linear_Eff; [auto|].
  eapply T_Pair_L1.
  - apply (T_Drop_L1 Linear _ _ _ _ _ (TString r)); [reflexivity|].
    eapply T_Var_Lin_L1; reflexivity.
  - change (@nil region_name) with (remove_first_L1 r [r]).
    apply T_Region_Active_L1; [simpl; auto | simpl; intros [] | simpl; auto | apply T_Unit_L1].
Qed.

Definition app_lin_typed_l2 :
  has_type_l2 Linear [r] [] app_lin (TProd (TBase TUnit) (TBase TUnit)) [] [].
Proof.
  eapply T_App_L2_Eff.
  - apply L2_lift_l1. exact lam_lin_typed_eff.
  - apply L2_lift_l1. apply T_Loc_L1. simpl; auto.
Defined.

Definition unit_typed_l2_lin :
  has_type_l2 Linear [] [] EUnit (TBase TUnit) [] [].
Proof. apply L2_lift_l1. apply T_Unit_L1. Defined.

Lemma drop_var_out :
  forall m R G i T R' G', has_type_l1 m R G (EDrop (EVar i)) T R' G' -> R' = R.
Proof.
  intros m R G i T R' G' H. inversion H; subst;
  match goal with Hv : has_type_l1 _ _ _ (EVar _) _ _ _ |- _ =>
    inversion Hv; subst; reflexivity end.
Qed.

Lemma lam_lin_not_tfun_l1 :
  forall m G T1 T2 R' G', ~ has_type_l1 m [r] G lam_lin (TFun T1 T2) R' G'.
Proof.
  intros m G T1 T2 R' G' H. unfold lam_lin in H.
  inversion H; subst;
  match goal with Hb : has_type_l1 _ [r] _ (EPair _ _) _ [r] _ |- _ =>
    inversion Hb; subst end;
  match goal with Hd : has_type_l1 _ [r] _ (EDrop (EVar 0)) _ ?R1 _ |- _ =>
    apply drop_var_out in Hd; subst end;
  match goal with Hg : has_type_l1 _ [r] _ (ERegion r EUnit) _ [r] _ |- _ =>
    apply region_unit_active_out in Hg; [cbn in Hg; discriminate | simpl; auto] end.
Qed.

Theorem composed_lin_untypable_l2 :
  forall m T R' G', has_type_l2 m [r] [] composed_lin T R' G' -> False.
Proof.
  intros m T R' G' H. inversion H; subst.
  match goal with Hl : has_type_l1 _ _ _ composed_lin _ _ _ |- _ =>
    unfold composed_lin in Hl; inversion Hl; subst end.
  match goal with Ha : has_type_l1 _ _ _ app_lin _ _ _ |- _ =>
    unfold app_lin in Ha; inversion Ha; subst end.
  eapply lam_lin_not_tfun_l1; eassumption.
Qed.

Theorem l2_pair_composition_fails_linear :
  (forall R R1 R2 G G1 G2 e1 e2 T1 T2,
       has_type_l2 Linear R G e1 T1 R1 G1 ->
       has_type_l2 Linear R1 G1 e2 T2 R2 G2 ->
       has_type_l2 Linear R G (EPair e1 e2) (TProd T1 T2) R2 G2) -> False.
Proof.
  intro Hcomp.
  exact (composed_lin_untypable_l2 _ _ _ _
           (Hcomp _ _ _ _ _ _ _ _ _ _ app_lin_typed_l2 unit_typed_l2_lin)).
Qed.


Print Assumptions region_unit_active_out.
Print Assumptions lam_typed_eff.
Print Assumptions app_typed_l2.
Print Assumptions unit_typed_l2.
Print Assumptions lam_not_tfun_l1.
Print Assumptions app_not_l1.
Print Assumptions composed_untypable_l2.
Print Assumptions l2_pair_composition_fails.
Print Assumptions lam_lin_typed_eff.
Print Assumptions app_lin_typed_l2.
Print Assumptions drop_var_out.
Print Assumptions lam_lin_not_tfun_l1.
Print Assumptions composed_lin_untypable_l2.
Print Assumptions l2_pair_composition_fails_linear.
