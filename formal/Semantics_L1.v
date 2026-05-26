(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Ephapax Preservation under the L1 judgment (R-threaded typing)

    This file states [preservation_l1] for the new [has_type_l1]
    judgment in [TypingL1.v]. The operational semantics [step] from
    [Semantics.v] is unchanged.

    Per PRESERVATION-DESIGN.md §4.5, preservation under L1 is:

      [step (mu, R, e) (mu', R', e')] /\
      [has_type_l1 R G e T R_final G']
      ->
      [has_type_l1 R' G e' T R_final G']

    The [R_final] and [G'] outputs are invariant under stepping —
    they describe the state after the entire expression has fully
    evaluated, which the operational step does not change.

    Current status (sequenced multi-PR closure):

    - [remove_first_eq_l1] — Qed (trivial).
    - [value_R_G_preserving_l1] — Admitted; needs induction on
      [is_value] with nested IH for EInl, EInr, EPair, EBorrow-of-
      value.
    - [region_shrink_preserves_typing_l1] — Qed via auxiliary
      [region_shrink_preserves_typing_l1_gen]; that aux has 2 admits
      (T_Region_L1 multiple-rr branch + T_Region_Active_L1 shadowed
      branch), both blocked on building L1 analogs of
      [Semantics.region_env_perm_typing] / [region_add_typing].
    - [subst_preserves_typing_l1] — Admitted; mirrors
      [Semantics.subst_preserves_typing] under the L1 judgment.
    - [preservation_l1] — Admitted; depends on the three helpers.

    Per-case proof sketches were validated experimentally during this
    file's authoring. The cases that close without any of the three
    Admitted helpers are: S_StringNew (apply T_Loc_L1), S_StringConcat
    (invert both T_Loc_L1 children, then apply T_Loc_L1), S_StringLen
    (invert the borrow, apply T_I32_L1), S_If_True / S_If_False
    (invert T_Bool_L1 on the condition, then assumption), S_Region_
    Enter (re-apply T_Region_Active_L1 with the same R_body), and
    S_Drop (apply T_Unit_L1). These can be inlined once the bullet
    structure accounts for the per-region typing cross-cases
    (ERegion inverts to both T_Region_L1 and T_Region_Active_L1,
    doubling subgoals for the three region step rules).

    Cases requiring helpers:
    - S_Region_Exit needs [region_shrink_preserves_typing_l1].
    - Congruence (S_X_Step) cases need [value_R_G_preserving_l1].
    - β-reduction (S_Let_Val, S_LetLin_Val, S_App_Fun, S_Case_Inl,
      S_Case_Inr) cases need [subst_preserves_typing_l1].

    Vacuous: S_Borrow_Step (both typing sub-cases — the inner cannot
    step under either typing rule).

    Once the three helpers are Qed, the per-case proofs are
    mechanical; the full theorem closure is sequenced as task #19's
    continuation. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

From Ephapax Require Import Syntax.
From Ephapax Require Import Typing.
From Ephapax Require Import TypingL1.
From Ephapax Require Import Semantics.

(** ** Trivial: the operational [remove_first] and the L1
    [remove_first_L1] coincide pointwise. *)

Lemma remove_first_eq_l1 :
  forall r R,
    remove_first_L1 r R = remove_first r R.
Proof.
  intros r R. induction R as [| r' R' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** ** Helper: values preserve both R and G under the L1 judgment.

    Inductive on [is_value v]. Atomic value rules (T_Unit_L1, T_Bool_L1,
    T_I32_L1, T_Loc_L1, T_StringNew_L1, T_Lam_L1) give R_out = R_in,
    G_out = G_in directly. Compound value forms (EInl, EInr, EPair,
    EBorrow of value) propagate via IH on the value-shaped sub-
    expression. Detailed proof deferred to L1 follow-up PR. *)

Lemma value_R_G_preserving_l1 :
  forall R G v T R' G',
    is_value v ->
    has_type_l1 R G v T R' G' ->
    R' = R /\ G' = G.
Proof.
  intros R G v T R' G' Hv. revert R G T R' G'.
  induction Hv; intros R0 G0 T0 R0' G0' Ht.
  - (* VUnit *) inversion Ht; subst; split; reflexivity.
  - (* VBool *) inversion Ht; subst; split; reflexivity.
  - (* VI32 *) inversion Ht; subst; split; reflexivity.
  - (* VLam *) inversion Ht; subst; split; reflexivity.
  - (* VPair v1 v2 *)
    inversion Ht; subst.
    match goal with
    | [ H1 : has_type_l1 _ _ v1 _ _ _,
        H2 : has_type_l1 _ _ v2 _ _ _ |- _ ] =>
        specialize (IHHv1 _ _ _ _ _ H1) as [HR1 HG1]; subst;
        specialize (IHHv2 _ _ _ _ _ H2) as [HR2 HG2]; subst
    end.
    split; reflexivity.
  - (* VInl T v *)
    inversion Ht; subst.
    match goal with
    | [ H : has_type_l1 _ _ v _ _ _ |- _ ] =>
        specialize (IHHv _ _ _ _ _ H) as [HR HG]; subst
    end.
    split; reflexivity.
  - (* VInr T v *)
    inversion Ht; subst.
    match goal with
    | [ H : has_type_l1 _ _ v _ _ _ |- _ ] =>
        specialize (IHHv _ _ _ _ _ H) as [HR HG]; subst
    end.
    split; reflexivity.
  - (* VLoc *) inversion Ht; subst; split; reflexivity.
  - (* VBorrow v *)
    inversion Ht; subst.
    + (* T_Borrow_L1: EBorrow (EVar i) — impossible since v is a value, not EVar *)
      inversion Hv.
    + (* T_Borrow_Val_L1 *)
      split; reflexivity.
Qed.

(** ** Helper: region-environment shrinkage for value typings.

    Mirrors [Semantics.region_shrink_preserves_typing] under the L1
    judgment. Used by the [S_Region_Exit] case of [preservation_l1].
    Detailed proof deferred to L1 follow-up PR. *)

(** Small commutation/idempotence facts about [remove_first]. *)

Lemma remove_first_comm :
  forall r1 r2 R,
    remove_first r1 (remove_first r2 R) = remove_first r2 (remove_first r1 R).
Proof.
  intros r1 r2. induction R as [| r' R' IH]; [reflexivity|].
  simpl.
  destruct (String.eqb r2 r') eqn:Heq2; destruct (String.eqb r1 r') eqn:Heq1.
  - (* r2 = r' = r1; both pop r' *)
    simpl. apply String.eqb_eq in Heq1, Heq2. subst.
    reflexivity.
  - simpl. rewrite Heq2. reflexivity.
  - simpl. rewrite Heq1. reflexivity.
  - simpl. rewrite Heq1, Heq2. f_equal. apply IH.
Qed.

(** Auxiliary general L1 region-shrinkage lemma — no [is_value] or
    [~ In r (free_regions T)] premises, mirroring the legacy
    [Semantics.region_shrink_preserves_typing]. The L1
    region-permutation infrastructure (analog of [region_env_perm_typing]
    and [region_add_typing]) is not yet built; the [T_Region_L1] and
    [T_Region_Active_L1] sub-cases need them. The two [admit]s inside
    this helper are the genuine residual blocking the [T_Lam_L1] case
    of the targeted lemma below.

    Once the L1 permutation infrastructure lands, this helper closes to
    Qed and the targeted lemma follows in one line. *)

Lemma region_shrink_preserves_typing_l1_gen :
  forall R G e T R' G',
    has_type_l1 R G e T R' G' ->
    forall r,
      expr_free_of_region r e ->
      has_type_l1 (remove_first r R) G e T (remove_first r R') G'.
Proof.
  intros R G e T R' G' Ht.
  induction Ht; intros rr Hfree; simpl in Hfree.
  - (* T_Unit_L1 *) apply T_Unit_L1.
  - (* T_Bool_L1 *) apply T_Bool_L1.
  - (* T_I32_L1 *) apply T_I32_L1.
  - (* T_Var_Lin_L1 *) eapply T_Var_Lin_L1; eauto.
  - (* T_Var_Unr_L1 *) eapply T_Var_Unr_L1; eauto.
  - (* T_Loc_L1 *)
    apply T_Loc_L1.
    apply remove_first_preserves_other; [exact Hfree | exact H].
  - (* T_StringNew_L1 *)
    apply T_StringNew_L1.
    apply remove_first_preserves_other; [exact Hfree | exact H].
  - (* T_StringConcat_L1 *)
    destruct Hfree as [Hf1 Hf2].
    eapply T_StringConcat_L1; [eapply IHHt1; auto | eapply IHHt2; auto].
  - (* T_StringLen_L1 *)
    eapply T_StringLen_L1. eapply IHHt; auto.
  - (* T_Let_L1 *)
    destruct Hfree as [Hf1 Hf2].
    eapply T_Let_L1; [eapply IHHt1; auto | eapply IHHt2; auto].
  - (* T_LetLin_L1 *)
    destruct Hfree as [Hf1 Hf2].
    eapply T_LetLin_L1; [exact H | eapply IHHt1; auto | eapply IHHt2; auto].
  - (* T_Lam_L1: body is R-preserving; IH gives shrinkage. *)
    apply T_Lam_L1. eapply IHHt; auto.
  - (* T_App_L1 *)
    destruct Hfree as [Hf1 Hf2].
    eapply T_App_L1; [eapply IHHt1; auto | eapply IHHt2; auto].
  - (* T_Pair_L1 *)
    destruct Hfree as [Hf1 Hf2].
    eapply T_Pair_L1; [eapply IHHt1; auto | eapply IHHt2; auto].
  - (* T_Fst_L1 *)
    eapply T_Fst_L1; [eapply IHHt; auto | exact H].
  - (* T_Snd_L1 *)
    eapply T_Snd_L1; [eapply IHHt; auto | exact H].
  - (* T_Inl_L1 *)
    eapply T_Inl_L1. eapply IHHt; auto.
  - (* T_Inr_L1 *)
    eapply T_Inr_L1. eapply IHHt; auto.
  - (* T_Case_L1 *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_Case_L1;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_If_L1 *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_If_L1;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_Region_L1: ERegion r e.
       Both sub-cases (rr = r shadowed, rr <> r descend) require either
       a "remove_first idempotent on absent" argument or a region-perm
       L1 helper. Documented as residual. *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed. Hfree is True (irrelevant). *)
      apply String.eqb_eq in Heq. subst r.
      rewrite (remove_first_not_in_id _ _ H).
      (* Goal: R; G |=L1 ERegion rr e : T
                -| remove_first rr (remove_first_L1 rr R_body); G' *)
      (* Case-split on whether [In rr (remove_first_L1 rr R_body)]:
         - If NO: outer [remove_first rr] is identity, and the original
           T_Region_L1 derivation suffices.
         - If YES: more r's exist; would need T_Region_L1 with the
           shrunken R_body and a body-weakening lemma. Residual. *)
      destruct (in_dec string_dec rr (remove_first_L1 rr R_body)) as [Hin | Hnotin].
      * (* Multiple rr's in R_body — needs L1 weakening to bump body
           typing from R to (rr :: R). Residual. *)
        admit.
      * (* Only one (or zero, but H1 says at least one) rr in R_body.
           Then [remove_first rr (remove_first_L1 rr R_body) =
                 remove_first_L1 rr R_body]. *)
        rewrite (remove_first_not_in_id _ _ Hnotin).
        eapply T_Region_L1; eauto.
    + (* rr <> r: descend. *)
      apply String.eqb_neq in Heq.
      assert (Hgoal_eq : remove_first rr (remove_first_L1 r R_body) =
                        remove_first_L1 r (remove_first rr R_body)).
      { rewrite (remove_first_eq_l1 r R_body).
        rewrite (remove_first_eq_l1 r (remove_first rr R_body)).
        apply remove_first_comm. }
      rewrite Hgoal_eq.
      apply (T_Region_L1 (remove_first rr R) (remove_first rr R_body) G G' r e T).
      * intro Hin. apply H. eapply remove_first_subset; exact Hin.
      * exact H0.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H1].
      * (* Body: IH at rr gives remove_first rr (r::R) ; ... |=L1 e ...
                                -| remove_first rr R_body ; ... *)
        specialize (IHHt rr Hfree).
        simpl in IHHt.
        destruct (String.eqb rr r) eqn:Heq2.
        -- exfalso. apply String.eqb_eq in Heq2. apply Heq. exact Heq2.
        -- exact IHHt.
  - (* T_Region_Active_L1: ERegion r e (r currently active). *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed; Hfree True. Need L1 region-perm to fold the
         resulting [r ∈ remove_first r R] cases. Residual. *)
      admit.
    + (* rr <> r: descend. *)
      apply String.eqb_neq in Heq.
      assert (Hgoal_eq : remove_first rr (remove_first_L1 r R_body) =
                        remove_first_L1 r (remove_first rr R_body)).
      { rewrite (remove_first_eq_l1 r R_body).
        rewrite (remove_first_eq_l1 r (remove_first rr R_body)).
        apply remove_first_comm. }
      rewrite Hgoal_eq.
      apply (T_Region_Active_L1 (remove_first rr R) (remove_first rr R_body) G G' r e T).
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H].
      * exact H0.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H1].
      * eapply IHHt. exact Hfree.
  - (* T_Borrow_L1 *)
    eapply T_Borrow_L1. exact H.
  - (* T_Borrow_Val_L1 *)
    eapply T_Borrow_Val_L1; [exact H | eapply IHHt; auto].
  - (* T_Drop_L1 *)
    eapply T_Drop_L1; [exact H | eapply IHHt; auto].
  - (* T_Copy_L1 *)
    eapply T_Copy_L1; [exact H | eapply IHHt; auto].
Admitted.

Lemma region_shrink_preserves_typing_l1 :
  forall R G v T R' G' r,
    is_value v ->
    has_type_l1 R G v T R' G' ->
    ~ In r (free_regions T) ->
    expr_free_of_region r v ->
    has_type_l1 (remove_first r R) G v T (remove_first r R') G'.
Proof.
  intros R G v T R' G' r Hv Ht HnotT Hfree.
  eapply region_shrink_preserves_typing_l1_gen; eauto.
Qed.

(** ** Helper: substitution preserves the L1 typing.

    Mirrors [Semantics.subst_preserves_typing] under the L1 judgment.
    Used by the β-reduction cases ([S_Let_Val], [S_LetLin_Val],
    [S_App_Fun], [S_Case_Inl], [S_Case_Inr]) of [preservation_l1].
    Detailed proof deferred to L1 follow-up PR. *)

Lemma subst_preserves_typing_l1 :
  forall T1 R1 G1' v R2 G2 e2 T2 R2_final G2',
    is_value v ->
    has_type_l1 R1 G1' v T1 R1 G1' ->
    has_type_l1 R2 ((T1, false) :: G2) e2 T2 R2_final ((T1, true) :: G2') ->
    has_type_l1 R2 G2 (subst 0 v e2) T2 R2_final G2'.
Admitted.

(** ** Preservation under the L1 judgment.

    The full case-by-case proof depends on the three Admitted helpers
    above. Sequenced for incremental closure across follow-up PRs (per
    task #19 in the project's task list).

    The simple cases (S_StringNew, S_StringConcat, S_StringLen,
    S_If_True, S_If_False, S_Region_Enter, S_Drop) were verified
    experimentally during this file's first-pass authoring; they close
    using only the lemmas already Qed in TypingL1.v + this file. They
    are not currently inlined into the proof body because the bullet
    structure picks up the per-step typing-rule cross-cases (e.g.
    ERegion's T_Region_L1 vs T_Region_Active_L1) which doubles the
    subgoal count over the step rule count. The clean-bullet structure
    is sequenced together with the three helpers landing. *)

Theorem preservation_l1 :
  forall mu R e mu' R' e',
    step (mu, R, e) (mu', R', e') ->
    forall G T R_final G',
      has_type_l1 R G e T R_final G' ->
      has_type_l1 R' G e' T R_final G'.
Admitted.
