(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  📌 PINNED REGRESSION WITNESS                                   ***
  ***                                                                ***
  ***  5 Qed lemmas. Authoritative source of the 2026-05-26          ***
  ***  soundness gap.                                                ***
  ***                                                                ***
  ***  This file SHOULD NOT BE WEAKENED. Any future proof work must  ***
  ***  coexist with these lemmas. The legacy judgment's falsity is   ***
  ***  load-bearing for the regression theorem; do not "fix" the     ***
  ***  legacy judgment to make these lemmas fail.                    ***
  ***                                                                ***
  ***  bad_input_untypable_l1 is also Qed under BOTH modalities,     ***
  ***  showing that the new L1 judgment closes the gap regardless of ***
  ***  Linear vs Affine.                                             ***
  ***                                                                ***
  ***  See `STATUS.adoc`, `formal/PRESERVATION-DESIGN.md §1`.        ***
  *********************************************************************

*)

(** * Soundness gap: counterexample to preservation as currently stated

    Exhibits a concrete configuration where the calculus's typing rules
    accept a well-typed input that, after a single step, becomes untypable
    at the same outer type.

    Configuration:
      e   := EPair (ERegion r' (ELoc l0 r0)) (ELoc l1 r')
             : TProd (TString r0) (TString r')   at R = [r0; r']
      e'  := EPair (ELoc l0 r0) (ELoc l1 r')
             at R = [r0]   (r' has been exited)
      Step: S_Pair_Step1 lifting S_Region_Exit on the inner ERegion r'.

    The post-step sibling ELoc l1 r' requires In r' [r0] — false.
    Hence [exists G_out, [r0]; G |- e' : TProd (TString r0) (TString r') -| G_out]
    fails. Preservation, as stated, does not hold for this input.

    Diagnoses the obstacle for preservation's 10 touches_region RIGHT
    branches: closing them requires a type-system change (Option 3 in
    PRESERVATION-HANDOFF.md), not a proof technique. *)

From Ephapax Require Import Syntax Typing Semantics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Section Counterexample.

  Definition r0 : region_name := "r0".
  Definition r1 : region_name := "r1".
  Definition l0 : loc := 0.
  Definition l1 : loc := 1.

  (* Bad input: pair of (region r1 containing a TString-r0 value) and
     (a TString-r1 location). Both children typeable at R = [r0; r1]. *)
  Definition e_bad : expr :=
    EPair (ERegion r1 (ELoc l0 r0)) (ELoc l1 r1).

  Definition T_bad : ty := TProd (TString r0) (TString r1).

  (** ===== (a) The bad input is well-typed at R = [r0; r1]. ===== *)

  Lemma bad_typable :
    has_type (r0 :: r1 :: nil) nil e_bad T_bad nil.
  Proof.
    unfold e_bad, T_bad.
    eapply T_Pair with (G' := nil).
    - (* ERegion r1 (ELoc l0 r0) : TString r0 at [r0; r1] -| []. *)
      eapply T_Region_Active.
      + (* In r1 [r0; r1]. *) right. left. reflexivity.
      + (* ~In r1 (free_regions (TString r0)) = ~In "r1" ["r0"]. *)
        simpl. intros [Heq | []].
        unfold r0, r1 in Heq. discriminate.
      + (* ELoc l0 r0 : TString r0. *)
        apply T_Loc. unfold region_active. left. reflexivity.
    - (* ELoc l1 r1 : TString r1 at [r0; r1] -| []. *)
      apply T_Loc. unfold region_active. right. left. reflexivity.
  Qed.

  (* The post-step expression: r1 has been exited; sibling still
     references r1. *)
  Definition e_bad_post : expr :=
    EPair (ELoc l0 r0) (ELoc l1 r1).

  (** ===== (b) The bad input steps to e_bad_post at R = [r0]. =====

      S_Pair_Step1 lifts an inner S_Region_Exit on the first child.
      The exit fires because:
        - ELoc l0 r0 is a value (VLoc).
        - In r1 [r0; r1].
        - expr_free_of_region r1 (ELoc l0 r0) — i.e. r0 ≠ r1. *)
  Lemma bad_step :
    forall mu,
      step (mu, r0 :: r1 :: nil, e_bad)
           (mem_free_region mu r1, r0 :: nil, e_bad_post).
  Proof.
    intros mu.
    unfold e_bad, e_bad_post.
    apply S_Pair_Step1.
    (* Inner: (mu, [r0; r1], ERegion r1 (ELoc l0 r0))
           -> (mem_free_region mu r1, remove_first r1 [r0; r1], ELoc l0 r0).
       remove_first r1 [r0; r1] = [r0] (skips r0, removes first r1). *)
    replace (r0 :: nil) with (remove_first r1 (r0 :: r1 :: nil)).
    - apply S_Region_Exit.
      + (* is_value (ELoc l0 r0). *) constructor.
      + (* In r1 [r0; r1]. *) right. left. reflexivity.
      + (* expr_free_of_region r1 (ELoc l0 r0) = (r0 <> r1). *)
        simpl. intros Heq. unfold r0, r1 in Heq. discriminate.
    - (* remove_first r1 [r0; r1] = [r0]: r0 ≠ r1 skips, then matches r1. *)
      simpl. unfold r0, r1.
      destruct (String.eqb "r1" "r0") eqn:Heq.
      + apply String.eqb_eq in Heq. discriminate.
      + destruct (String.eqb "r1" "r1") eqn:Heq2.
        * reflexivity.
        * apply String.eqb_neq in Heq2. exfalso. apply Heq2. reflexivity.
  Qed.

  (** ===== (c) e_bad_post is NOT typeable at R = [r0] : T_bad. =====

      The sibling ELoc l1 r1 requires In r1 [r0], which is false. *)
  Lemma bad_post_untypable :
    forall G G',
      ~ has_type (r0 :: nil) G e_bad_post T_bad G'.
  Proof.
    intros G G' Htype.
    unfold e_bad_post, T_bad in Htype.
    (* Invert T_Pair to expose the two children. *)
    inversion Htype; subst.
    (* The TString-r1 child: invert T_Loc, get the bad region_active premise. *)
    match goal with
    | [ H : has_type _ _ (ELoc l1 r1) (TString r1) _ |- _ ] =>
        inversion H; subst
    end.
    (* region_active [r0] r1 = In "r1" ["r0"], which is false. *)
    match goal with
    | [ H : region_active _ r1 |- _ ] =>
        unfold region_active in H; simpl in H;
        destruct H as [Heq | []];
        unfold r0, r1 in Heq; discriminate
    end.
  Qed.

  (** ===== Conclusion =====

      Preservation, as currently stated, is FALSE for input e_bad.
      [bad_typable] shows the input is well-typed; [bad_step] shows
      a single-step reduction exists; [bad_post_untypable] shows the
      result of that reduction is untypable at the same outer type.

      The 11 remaining preservation admits on the [touches_region]
      RIGHT branches share this structure. A type-system change
      (Option 3 in PRESERVATION-HANDOFF.md) is required. *)

End Counterexample.

(** * L1 regression: the redesigned typing blocks the bad input

    With the [has_type_l1] judgement from [TypingL1.v], the bad input
    [e_bad] no longer has a derivation — the L1 fix replaces the
    post-step untypability of the original counterexample with **input
    untypability**.

    Proof structure:
    - Invert [T_Pair_L1] on the assumed derivation: forces the
      second child to be typed at the first child's R-output.
    - Invert [T_Loc_L1] on the second child ([ELoc l1 r1]): gives
      [In r1 R1] as a premise.
    - Invert the typing of the first child ([ERegion r1 (ELoc l0 r0)]):
      [T_Region_L1] fails because [~ In r1 [r0; r1]] does not hold;
      [T_Region_Active_L1] forces [R1 = remove_first_L1 r1 R_body]
      where [R_body] is the body's R-output. The body is a value
      ([ELoc l0 r0]) typed under [T_Loc_L1], so [R_body = [r0; r1]]
      and hence [R1 = [r0]].
    - [In r1 [r0]] is false; contradiction. *)

From Ephapax Require Import TypingL1.

Section L1Fix.

  (** Helper: T_Loc_L1 has [R_out = R_in], [G_out = G_in]. By inversion. *)

  Lemma t_loc_l1_R_preserving :
    forall m R G l r R' G' T,
      has_type_l1 m R G (ELoc l r) T R' G' ->
      R' = R /\ G' = G.
  Proof.
    intros m R G l r R' G' T H.
    inversion H; subst; split; reflexivity.
  Qed.

  (** The L1 regression theorem.

      Generalised to [forall m : Modality, ...] per L2: the bad
      input is untypable in BOTH ephapax-linear AND ephapax-affine.
      The inversion logic is mode-polymorphic — the region-threading
      contradiction surfaces identically in both modes. *)
  Lemma bad_input_untypable_l1 :
    forall m R_out G_out,
      ~ has_type_l1 m (r0 :: r1 :: nil) nil e_bad T_bad R_out G_out.
  Proof.
    intros m R_out G_out Htype.
    unfold e_bad, T_bad in Htype.
    (* Invert T_Pair_L1; only rule matching EPair. *)
    inversion Htype; subst.
    (* Hte1 = typing of (ERegion r1 (ELoc l0 r0)); Hte2 = typing of (ELoc l1 r1). *)
    match goal with
    | [ H : has_type_l1 _ _ _ (ERegion r1 (ELoc l0 r0)) _ ?R1 _ |- _ ] =>
        rename H into Hte1; rename R1 into R1_e1
    end.
    match goal with
    | [ H : has_type_l1 _ _ _ (ELoc l1 r1) _ _ _ |- _ ] =>
        rename H into Hte2
    end.
    (* From Hte2 = T_Loc_L1: In r1 R1_e1. *)
    inversion Hte2; subst.
    match goal with
    | [ Hin : In r1 ?R |- _ ] => rename Hin into Hin_r1
    end.
    (* From Hte1 = T_Region_L1 or T_Region_Active_L1. *)
    inversion Hte1; subst.
    - (* T_Region_L1: requires ~ In r1 (r0 :: r1 :: nil), contradicted by r1 being there. *)
      match goal with
      | [ H : ~ In r1 _ |- _ ] => exfalso; apply H; right; left; reflexivity
      end.
    - (* T_Region_Active_L1: body ([ELoc l0 r0]) is a value; t_loc_l1_R_preserving
         gives body's R_out = R_in = [r0; r1].  Hence R1_e1 = remove_first_L1 r1 [r0; r1]. *)
      match goal with
      | [ Hbody : has_type_l1 _ _ _ (ELoc _ _) _ ?Rbody _ |- _ ] =>
          assert (HRb : Rbody = r0 :: r1 :: nil)
            by (eapply t_loc_l1_R_preserving; eassumption)
      end.
      subst.
      (* Compute remove_first_L1 r1 (r0::r1::nil):
         r0 ≠ r1, so skip; r1 = r1, so remove; result = [r0]. *)
      unfold r0, r1, remove_first_L1 in Hin_r1.
      simpl in Hin_r1.
      destruct (String.eqb "r1" "r0") eqn:Heq1;
        [ apply String.eqb_eq in Heq1; discriminate | ].
      destruct (String.eqb "r1" "r1") eqn:Heq2;
        [ | apply String.eqb_neq in Heq2; exfalso; apply Heq2; reflexivity ].
      simpl in Hin_r1.
      destruct Hin_r1 as [Heq_r | []].
      discriminate.
  Qed.

End L1Fix.
