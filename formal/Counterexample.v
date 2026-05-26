(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

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
