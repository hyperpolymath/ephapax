(* SPDX-License-Identifier: MPL-2.0 *)
(** * LetCheck — a COMPLETENESS gap in the current judgments.

    [ELet e1 e2] is only typable when the bound type is linear, under
    both the current L1 judgment ([has_type_l1], either modality) and
    the legacy [has_type]. Reason: [T_Let_L1] / [T_Let] demand the
    body's output context be [(T1, true) :: G''], but a non-linear
    binding's flag is never flipped to [true] ([T_Var_Unr_L1] leaves
    the context unchanged; only [T_Var_Lin_L1] marks, and it needs a
    linear type). So [let x = () in ()] — the intended [let_unit] — is
    rejected, although it is a closed, effect-free, resource-free
    program that any reasonable judgment should accept. This is a
    completeness gap, not a soundness hole. *)

From Ephapax Require Import Syntax Typing TypingL1 Semantics Semantics_L1 Modality.
Require Import Coq.Lists.List Coq.Arith.Arith. Import ListNotations.

(** Modality-polymorphic version of [Semantics_L1.unrestricted_flag_unchanged_l1]
    (which is stated for [Linear] only). *)
Lemma unr_flag_unchanged_l1_m :
  forall m R G e T R' G',
    has_type_l1 m R G e T R' G' ->
    forall j T0 u,
      is_linear_ty T0 = false ->
      ctx_lookup G j = Some (T0, u) ->
      ctx_lookup G' j = Some (T0, u).
Proof.
  intros m R G e T R' G' Htype.
  induction Htype; intros idx T0 u0 Hnlin Hlk; simpl in *;
    try exact Hlk;
    try (eapply IHHtype; eassumption);
    try (eapply IHHtype2; [exact Hnlin|]; eapply IHHtype1; eassumption).
  - (* T_Var_Lin_L1 *)
    destruct (Nat.eq_dec i idx) as [->|Hne].
    + unfold ctx_lookup in *. rewrite H in Hlk. injection Hlk as <- <-.
      rewrite Hnlin in H0. discriminate.
    + rewrite ctx_mark_used_lookup_other by exact Hne. exact Hlk.
  - (* T_Let_L1 *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in Hlk. exact Hlk.
  - (* T_LetLin_L1 *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in Hlk. exact Hlk.
  - (* T_Case_L1_Linear *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in Hlk. exact Hlk.
  - (* T_Case_L1_Affine *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in Hlk. exact Hlk.
Qed.

(** Headline (L1, any modality): a typable [ELet] has a linear bound type. *)
Theorem let_l1_forces_linear_binder :
  forall m R G e1 e2 T R' G',
    has_type_l1 m R G (ELet e1 e2) T R' G' ->
    exists T1 R1 G1, has_type_l1 m R G e1 T1 R1 G1 /\ is_linear_ty T1 = true.
Proof.
  intros m R G e1 e2 T R' G' H. inversion H; subst.
  exists T1, R1, G'0. split; [assumption|].
  destruct (is_linear_ty T1) eqn:Hl; [reflexivity|].
  match goal with Hb : has_type_l1 _ _ (ctx_extend _ T1) e2 _ _ _ |- _ =>
    pose proof (unr_flag_unchanged_l1_m _ _ _ _ _ _ _ Hb 0 T1 false Hl eq_refl) as Hc
  end.
  cbn in Hc. discriminate.
Qed.

(** [let_unit] in the current L1 judgment: untypable at every modality,
    every region env, every context, every body. *)
Definition let_unit : expr := ELet EUnit EUnit.

Theorem let_unit_untypable_l1 :
  forall m R G T R' G', ~ has_type_l1 m R G let_unit T R' G'.
Proof.
  intros m R G T R' G' H.
  destruct (let_l1_forces_linear_binder _ _ _ _ _ _ _ _ H) as (T1 & R1 & G1 & He1 & Hl).
  inversion He1; subst. discriminate.
Qed.

(** Stronger: no body makes [let _ = () in body] typable. *)
Theorem let_of_unit_untypable_l1 :
  forall m R G e2 T R' G', ~ has_type_l1 m R G (ELet EUnit e2) T R' G'.
Proof.
  intros m R G e2 T R' G' H.
  destruct (let_l1_forces_linear_binder _ _ _ _ _ _ _ _ H) as (T1 & R1 & G1 & He1 & Hl).
  inversion He1; subst. discriminate.
Qed.

(** The same gap in the legacy judgment [has_type] (Typing.v), via the
    existing Qed lemma [Semantics.flag_false_to_true_implies_linear]. *)
Theorem let_of_unit_untypable_legacy :
  forall R G e2 T G', ~ has_type R G (ELet EUnit e2) T G'.
Proof.
  intros R G e2 T G' H. inversion H; subst.
  match goal with He1 : has_type _ _ EUnit _ _ |- _ => inversion He1; subst end.
  match goal with Hb : has_type _ (ctx_extend _ _) e2 _ _ |- _ =>
    pose proof (flag_false_to_true_implies_linear _ _ _ _ _ 0 _ Hb eq_refl eq_refl) as Hc
  end.
  discriminate.
Qed.

(** Sanity (the gap is about the binder, not the body): the body alone
    and the bound expression alone are both typable everywhere. *)
Lemma let_unit_parts_typable :
  forall m R G,
    has_type_l1 m R G EUnit (TBase TUnit) R G /\
    has_type_l1 m R (ctx_extend G (TBase TUnit)) EUnit (TBase TUnit)
                R (ctx_extend G (TBase TUnit)).
Proof. intros; split; apply T_Unit_L1. Qed.

Print Assumptions unr_flag_unchanged_l1_m.
Print Assumptions let_l1_forces_linear_binder.
Print Assumptions let_unit_untypable_l1.
Print Assumptions let_of_unit_untypable_l1.
Print Assumptions let_of_unit_untypable_legacy.
Print Assumptions let_unit_parts_typable.
