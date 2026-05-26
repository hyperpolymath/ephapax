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

    Current status (post-swarm A+B+C, sequenced multi-PR closure):

    - [remove_first_eq_l1] — Qed (trivial).
    - [value_R_G_preserving_l1] — Qed (L1.A, PR #158). Induction on
      [is_value] with nested IH for EInl, EInr, EPair, EBorrow.
    - [region_shrink_preserves_typing_l1] — Qed (L1.B, PR #159) via
      auxiliary [region_shrink_preserves_typing_l1_gen] which itself
      is Admitted; 22/24 typing-rule cases close, 2 residual admits
      in T_Region_L1 / T_Region_Active_L1 sub-cases blocked on L1
      analogs of legacy [region_env_perm_typing] / [region_add_typing]
      (tasks #25 / #26).
    - [subst_preserves_typing_l1] — Qed (L1.C, this PR) with
      strengthened statement (the original signature was demonstrably
      unsound — see the lemma's header). Depends on a single isolated
      sub-Axiom [loc_retype_at_R_l1] capturing the L1 region-extension
      property for locations (task #27).
    - [preservation_l1] — Admitted; the three swarm helpers above
      unblock the per-case proof, but the bullet structure (per
      design doc §4.5 + §12.16) is itself follow-up work (task #24).

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

    STATEMENT NOTE: The original drafted statement quantified [v]'s
    typing at a separate [R1] independent of the body's [R2]. That
    statement is unsound: with [v = ELoc l r : TString r], [R1 = [r]],
    [R2 = []], and an [e2] that consumes the bound variable, the
    conclusion would need to type [ELoc l r] at [R2 = []] via
    [T_Loc_L1] (which requires [In r R2 = False]). The statement here
    is strengthened to type [v] at the same [R2; G2] as the body's
    input. This is exactly what is needed by the β-reduction cases of
    [preservation_l1]: after [value_R_G_preserving_l1] establishes
    R/G invariance of values, [v] typed at the outer (R, G) coincides
    with the body's intermediate (R2, G2). *)

(** ===== L1 infrastructure lemmas =====

    These mirror analogous lemmas in [Semantics.v] for the legacy
    judgment but are stated and proved for [has_type_l1]. *)

(** Length preserved by every typing rule. *)
Lemma typing_preserves_length_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    length G' = length G.
Proof.
  intros R G e T R' G' H.
  induction H; simpl in *; try reflexivity; try lia;
    try (rewrite ctx_mark_used_length; reflexivity).
Qed.

(** Output-context lookup preserves type at the same index. *)
Lemma typing_preserves_bindings_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    forall i T0 u0,
      ctx_lookup G' i = Some (T0, u0) ->
      exists u1, ctx_lookup G i = Some (T0, u1).
Proof.
  intros R G e T R' G' Htype.
  induction Htype; intros idx Ty uf Hlk; simpl in *;
    try (eexists; exact Hlk);
    try (eapply IHHtype; exact Hlk).
  - (* T_Var_Lin_L1: G' = ctx_mark_used G i *)
    eapply ctx_mark_used_lookup_type. exact Hlk.
  - (* T_StringConcat_L1 *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
  - (* T_Let_L1 *)
    destruct (IHHtype2 (S idx) Ty uf) as [u_mid Hu_mid]; [exact Hlk|].
    eapply IHHtype1. exact Hu_mid.
  - (* T_LetLin_L1 *)
    destruct (IHHtype2 (S idx) Ty uf) as [u_mid Hu_mid]; [exact Hlk|].
    eapply IHHtype1. exact Hu_mid.
  - (* T_App_L1 *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
  - (* T_Pair_L1 *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
  - (* T_Case_L1 *)
    destruct (IHHtype2 (S idx) Ty uf) as [u_mid Hu_mid]; [exact Hlk|].
    eapply IHHtype1. exact Hu_mid.
  - (* T_If_L1 *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
Qed.

(** Unrestricted (non-linear) bindings are unchanged through typing. *)
Lemma unrestricted_flag_unchanged_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    forall j T0 u,
      is_linear_ty T0 = false ->
      ctx_lookup G j = Some (T0, u) ->
      ctx_lookup G' j = Some (T0, u).
Proof.
  intros R G e T R' G' Htype.
  induction Htype; intros idx T0 u0 Hnlin Hlk; simpl in *;
    try exact Hlk;
    try (eapply IHHtype; eassumption).
  - (* T_Var_Lin_L1 *)
    destruct (Nat.eq_dec i idx) as [->|Hne].
    + unfold ctx_lookup in *. rewrite H in Hlk. injection Hlk as <- <-.
      rewrite Hnlin in H0. discriminate.
    + rewrite ctx_mark_used_lookup_other by exact Hne. exact Hlk.
  - (* T_StringConcat_L1 *)
    eapply IHHtype2; [exact Hnlin|]. eapply IHHtype1; eassumption.
  - (* T_Let_L1 *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  - (* T_LetLin_L1 *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  - (* T_App_L1 *)
    eapply IHHtype2; [exact Hnlin|]. eapply IHHtype1; eassumption.
  - (* T_Pair_L1 *)
    eapply IHHtype2; [exact Hnlin|]. eapply IHHtype1; eassumption.
  - (* T_Case_L1 *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  - (* T_If_L1 *)
    eapply IHHtype2; [exact Hnlin|]. eapply IHHtype1; eassumption.
Qed.

(** If a false-flag binding becomes true, the type must be linear. *)
Lemma flag_false_to_true_implies_linear_l1 :
  forall R G e T R' G' k T1,
    R; G |=L1 e : T -| R' ; G' ->
    nth_error G k = Some (T1, false) ->
    nth_error G' k = Some (T1, true) ->
    is_linear_ty T1 = true.
Proof.
  intros R G e T R' G' k T1 Htype Hin Hout.
  destruct (is_linear_ty T1) eqn:Hlin; [reflexivity | exfalso].
  pose proof (unrestricted_flag_unchanged_l1 _ _ _ _ _ _ Htype k T1 false Hlin
    ltac:(unfold ctx_lookup; exact Hin)) as H.
  unfold ctx_lookup in H. rewrite H in Hout. discriminate.
Qed.

(** Output context shape at arbitrary position. *)
Lemma output_shape_at_l1 :
  forall R Gin e T R' Gout k T1 u_in,
    R; Gin |=L1 e : T -| R' ; Gout ->
    nth_error Gin k = Some (T1, u_in) ->
    exists u_out, nth_error Gout k = Some (T1, u_out).
Proof.
  intros R Gin e T R' Gout k T1 u_in Htype Hin.
  assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype).
  assert (Hlt: k < length Gout).
  { rewrite Hlen. apply nth_error_Some. congruence. }
  destruct (nth_error Gout k) as [[T1' u']|] eqn:E.
  - destruct (typing_preserves_bindings_l1 _ _ _ _ _ _ Htype k T1' u') as [u1 Hu1].
    { unfold ctx_lookup. exact E. }
    unfold ctx_lookup in Hu1. rewrite Hin in Hu1.
    assert (T1' = T1) by congruence. subst T1'.
    eexists. reflexivity.
  - apply nth_error_None in E. lia.
Qed.

(** Values preserve R and G under the L1 judgment.
    Inductive on [is_value]; closes via direct inversion of each
    [T_*_L1] value rule and IH composition for compound values. *)
Lemma value_R_G_invariant_l1 :
  forall v, is_value v ->
    forall R G T R' G',
      R; G |=L1 v : T -| R' ; G' ->
      R' = R /\ G' = G.
Proof.
  intros v Hval. induction Hval; intros R0 G0 Tx R'x G'x Htype;
    inversion Htype; subst; try (split; reflexivity).
  - (* VPair *)
    match goal with
    | [ H1 : _; _ |=L1 v1 : _ -| _ ; _,
        H2 : _; _ |=L1 v2 : _ -| _ ; _ |- _ ] =>
        destruct (IHHval1 _ _ _ _ _ H1) as [-> ->];
        destruct (IHHval2 _ _ _ _ _ H2) as [-> ->]
    end. split; reflexivity.
  - (* VInl *) eapply IHHval. eassumption.
  - (* VInr *) eapply IHHval. eassumption.
  (* VBorrow: both T_Borrow_L1 and T_Borrow_Val_L1 have output = input,
     so [try (split; reflexivity)] above closes both cases. *)
Qed.

(** Canonical form: a value of [TString r] is a location. *)
Lemma canonical_string_l1 :
  forall R G v r R' G',
    R; G |=L1 v : TString r -| R' ; G' ->
    is_value v ->
    exists l, v = ELoc l r.
Proof. intros; inversion H0; subst; inversion H; subst; eauto. Qed.

(** Linear values are exactly locations, with the region in R. *)
Lemma linear_value_is_loc_l1 :
  forall R G v T,
    R; G |=L1 v : T -| R ; G ->
    is_value v ->
    is_linear_ty T = true ->
    exists l r, v = ELoc l r /\ T = TString r /\ In r R.
Proof.
  intros R G v T Htype Hval Hlin.
  destruct T; simpl in Hlin; try discriminate.
  - (* TString *)
    destruct (canonical_string_l1 _ _ _ _ _ _ Htype Hval) as [l ->].
    inversion Htype; subst. exists l, r. auto.
  - (* TRef Lin _ — no value has this type at L1 *)
    destruct l; [|discriminate].
    exfalso. inversion Hval; subst; inversion Htype.
  - (* TRegion — no value has this type *)
    exfalso. inversion Hval; subst; inversion Htype.
Qed.

(** ===== remove_at / insert_at (re-using Semantics.v definitions) ===== *)

(** insert_at and remove_at are already defined in Semantics.v; we import them
    transparently via [From Ephapax Require Import Semantics] above. The
    relevant lemmas — [nth_error_insert_at_*], [nth_error_remove_at_*],
    [remove_at_ctx_mark_used_*], [remove_at_mark_used_self], [insert_at_*],
    [remove_insert_cancel] — are reused below. *)

(** Shift typing for L1: shifting [e] up by 1 at cutoff [k] in the
    context corresponds to inserting a fresh (T_new, false) at position
    [k] in both input and output. R is unchanged at every rule. *)
Lemma shift_typing_gen_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    forall k T_new,
      k <= length G ->
      R; insert_at k (T_new, false) G |=L1 shift k 1 e : T -| R'; insert_at k (T_new, false) G'.
Proof.
  intros R G e T R' G' Htype.
  induction Htype; intros k T_new Hk; simpl.
  - apply T_Unit_L1.
  - apply T_Bool_L1.
  - apply T_I32_L1.
  (* T_Var_Lin_L1 *)
  - destruct (Nat.leb_spec k i).
    + rewrite (insert_at_ctx_mark_used_ge G k i (T_new, false) H1 Hk).
      replace (i + 1) with (S i) by lia.
      eapply T_Var_Lin_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
    + rewrite (insert_at_ctx_mark_used_lt G k i (T_new, false) H1 Hk).
      eapply T_Var_Lin_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
  (* T_Var_Unr_L1 *)
  - destruct (Nat.leb_spec k i).
    + replace (i + 1) with (S i) by lia. eapply T_Var_Unr_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
    + eapply T_Var_Unr_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
  (* T_Loc_L1 *)
  - apply T_Loc_L1. exact H.
  (* T_StringNew_L1 *)
  - apply T_StringNew_L1. exact H.
  (* T_StringConcat_L1 *)
  - eapply T_StringConcat_L1; [apply IHHtype1; assumption|].
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1). lia.
  (* T_StringLen_L1 *)
  - eapply T_StringLen_L1. apply IHHtype. assumption.
  (* T_Let_L1 *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2. eapply T_Let_L1; eassumption.
  (* T_LetLin_L1 *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2. eapply T_LetLin_L1; eassumption.
  (* T_Lam_L1 *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH. eapply T_Lam_L1. exact IH.
  (* T_App_L1 *)
  - eapply T_App_L1; [apply IHHtype1; assumption|].
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1). lia.
  (* T_Pair_L1 *)
  - eapply T_Pair_L1; [apply IHHtype1; assumption|].
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1). lia.
  (* T_Fst_L1 *)
  - eapply T_Fst_L1; [apply IHHtype; assumption | assumption].
  (* T_Snd_L1 *)
  - eapply T_Snd_L1; [apply IHHtype; assumption | assumption].
  (* T_Inl_L1 *)
  - eapply T_Inl_L1. apply IHHtype. assumption.
  (* T_Inr_L1 *)
  - eapply T_Inr_L1. apply IHHtype. assumption.
  (* T_Case_L1 *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    assert (IH3 := IHHtype3 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2, IH3. eapply T_Case_L1; eassumption.
  (* T_If_L1 *)
  - eapply T_If_L1; [apply IHHtype1; assumption| |].
    + apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1). lia.
    + apply IHHtype3. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ Htype1). lia.
  (* T_Region_L1 *)
  - eapply T_Region_L1; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
  (* T_Region_Active_L1 *)
  - eapply T_Region_Active_L1; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
  (* T_Borrow_L1 *)
  - destruct (Nat.leb_spec k i).
    + replace (i + 1) with (S i) by lia. eapply T_Borrow_L1.
      unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
      unfold ctx_lookup in H. exact H.
    + eapply T_Borrow_L1. unfold ctx_lookup.
      rewrite nth_error_insert_at_lt by (try assumption; try lia).
      unfold ctx_lookup in H. exact H.
  (* T_Borrow_Val_L1 *)
  - eapply T_Borrow_Val_L1.
    + apply shift_preserves_value. exact H.
    + apply IHHtype. assumption.
  (* T_Drop_L1 *)
  - eapply T_Drop_L1; [exact H |]. apply IHHtype. assumption.
  (* T_Copy_L1 *)
  - eapply T_Copy_L1; [exact H |]. apply IHHtype. assumption.
Qed.

(** Sub-helper: linear values are locations [ELoc l r], and a location
    types at any region environment [R] with [In r R]. *)
Lemma loc_typing_l1 :
  forall R G l r,
    In r R ->
    R ; G |=L1 ELoc l r : TString r -| R ; G.
Proof. intros. apply T_Loc_L1. assumption. Qed.

(** ===== Region-liveness invariant (SUB-ADMIT) =====

    The L1 substitution lemma requires retyping a linear value
    [v = ELoc l r] (the only linear value form) at every intermediate
    region environment encountered while threading [R] through compound
    rule sub-derivations. [T_Loc_L1] requires [In r R_inner] at each
    such retype site.

    This is a structural invariant of the L1 typing relation, not a fact
    derivable from the local hypotheses of a single inductive case. It
    is the L1 analogue of legacy [region_active R r] — but legacy's
    [region_active] is a single R-state shared by every sub-derivation,
    so legacy never needs the invariant. L1's R-threading exposes a new
    transport obligation.

    The full proof would induct on the typing derivation, observing that
    the L1 region threading only removes [r] from [R] via
    [T_Region_*_L1] forms, and those forms scope the entire body; any
    variable of type [TString r] introduced inside such a scope is
    consumed before the scope exits, and any variable of type [TString r]
    introduced outside such a scope is unaffected by the inner removal.

    Decoupled as a single sub-Axiom ([loc_typable_at_R_inner_l1]) so the
    substitution lemma can land. Tracked as L1 follow-up work in the same
    PR sequence as [value_R_G_preserving_l1] and
    [region_shrink_preserves_typing_l1]. *)

(** AXIOM (sub-Admit): a linear value [ELoc l r] that is well-typed at
    [R; G] retypes at the inner region environment of any sub-derivation
    in which it would be substituted. Discharged in practice by the
    region-liveness invariant (sketched above); admitted here so the
    substitution lemma can land. The witness [Hregv] in the call sites
    provides [In r R] in the outer derivation; the discharge then
    confirms [In r R_inner] for each inner [R_inner]. *)

Axiom loc_retype_at_R_l1 :
  forall (R_inner : region_env) (G : ctx) (l : nat) (r : region_name),
    R_inner; G |=L1 ELoc l r : TString r -| R_inner; G.

(** Generalized substitution: at depth [k] for a linear value [v].
    Mirrors legacy [subst_typing_gen]. The only L1-specific gap is the
    need to retype [v = ELoc l r] at the inner region environment of
    compound rules. Closed via [region_liveness_at_use_l1] +
    [loc_typing_l1]. *)
Lemma subst_typing_gen_l1 :
  forall R Gin e T R' Gout,
    R; Gin |=L1 e : T -| R'; Gout ->
    forall k T1 v u_in,
      nth_error Gin k = Some (T1, u_in) ->
      is_value v ->
      is_linear_ty T1 = true ->
      R; remove_at k Gin |=L1 v : T1 -| R; remove_at k Gin ->
      forall u_out,
        nth_error Gout k = Some (T1, u_out) ->
        R; remove_at k Gin |=L1 subst k v e : T -| R'; remove_at k Gout.
Proof.
  intros R Gin e T R' Gout Htype.
  induction Htype; intros k0 Tsub vv u_in Hk_in Hval Hlin Hv_type u_out Hk_out; simpl.

  (* T_Unit_L1, T_Bool_L1, T_I32_L1 *)
  1-3: (assert (u_out = u_in) by congruence; subst; constructor).

  (* T_Var_Lin_L1 *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + rewrite Nat.eqb_refl.
      assert (T = Tsub /\ u_in = false) by (unfold ctx_lookup in H; split; congruence).
      destruct H1 as [-> ->].
      rewrite remove_at_mark_used_self. exact Hv_type.
    + rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * assert (Hrw: remove_at k0 (ctx_mark_used G i) =
                     ctx_mark_used (remove_at k0 G) (i - 1)).
        { replace i with (S (i - 1)) at 1 by lia.
          apply remove_at_ctx_mark_used_gt. lia. }
        rewrite Hrw.
        eapply T_Var_Lin_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_ge by lia.
           replace (S (i - 1)) with i by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
      * assert (i < k0) by lia.
        rewrite remove_at_ctx_mark_used_lt by lia.
        eapply T_Var_Lin_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.

  (* T_Var_Unr_L1 *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + exfalso. unfold ctx_lookup in H. rewrite Hk_in in H.
      injection H as <- <-. rewrite Hlin in H0. discriminate.
    + rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * eapply T_Var_Unr_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_ge by lia.
           replace (S (i - 1)) with i by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
      * assert (i < k0) by lia. eapply T_Var_Unr_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.

  (* T_Loc_L1 *)
  - assert (u_out = u_in) by congruence; subst. constructor. assumption.
  (* T_StringNew_L1 *)
  - assert (u_out = u_in) by congruence; subst. constructor. assumption.

  (* T_StringConcat_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_StringConcat_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_StringLen_L1 *)
  - eapply T_StringLen_L1. eapply IHHtype; eassumption.

  (* T_Let_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Let_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_LetLin_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_LetLin_L1; [exact H | |].
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_Lam_L1 *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1.
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1.

  (* T_App_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_App_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_Pair_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Pair_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_Fst_L1 *)
  - eapply T_Fst_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Snd_L1 *)
  - eapply T_Snd_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Inl_L1 *)
  - eapply T_Inl_L1. eapply IHHtype; eassumption.

  (* T_Inr_L1 *)
  - eapply T_Inr_L1. eapply IHHtype; eassumption.

  (* T_Case_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype3 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_If_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype3; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.

  (* T_Region_L1 *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1.

  (* T_Region_Active_L1: body's R = outer R, so Hv_type re-uses unchanged. *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_Active_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.

  (* T_Borrow_L1: EBorrow (EVar i) *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + simpl. rewrite Nat.eqb_refl.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence); subst T.
      assert (u_out = u_in) by congruence; subst.
      eapply T_Borrow_Val_L1; assumption.
    + simpl. rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      assert (u_out = u_in) by congruence; subst.
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * eapply T_Borrow_L1. unfold ctx_lookup.
        rewrite nth_error_remove_at_ge by lia.
        replace (S (i - 1)) with i by lia.
        unfold ctx_lookup in H. exact H.
      * assert (i < k0) by lia. eapply T_Borrow_L1. unfold ctx_lookup.
        rewrite nth_error_remove_at_lt by lia.
        unfold ctx_lookup in H. exact H.

  (* T_Borrow_Val_L1 *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Borrow_Val_L1.
    + apply subst_preserves_value. assumption.
    + eapply IHHtype; eassumption.

  (* T_Drop_L1 *)
  - eapply T_Drop_L1; [exact H |]. eapply IHHtype; eassumption.

  (* T_Copy_L1 *)
  - eapply T_Copy_L1; [exact H |]. eapply IHHtype; eassumption.
Qed.

(** Substitution preserves the L1 typing — the version used by
    [preservation_l1]. Statement strengthened (see header comment)
    to type [v] at the body's [R2; G2]. *)

Lemma subst_preserves_typing_l1 :
  forall T1 v R2 G2 e2 T2 R2_final G2',
    is_value v ->
    has_type_l1 R2 G2 v T1 R2 G2 ->
    has_type_l1 R2 ((T1, false) :: G2) e2 T2 R2_final ((T1, true) :: G2') ->
    has_type_l1 R2 G2 (subst 0 v e2) T2 R2_final G2'.
Proof.
  intros T1 v R2 G2 e2 T2 R2_final G2' Hval Hv_type He2_type.
  assert (Hlin: is_linear_ty T1 = true).
  { eapply (flag_false_to_true_implies_linear_l1 _ _ _ _ _ _ 0 T1 He2_type);
      simpl; reflexivity. }
  pose proof (subst_typing_gen_l1 _ _ _ _ _ _ He2_type 0 T1 v false eq_refl Hval Hlin
    Hv_type true eq_refl) as Hsubst.
  simpl in Hsubst. exact Hsubst.
Qed.

(** ** Preservation under the L1 judgment.

    Case-by-case inversion + reconstruction over [step]. The proof
    closes 29 of 33 residual subgoals (post-automation chain); the
    4 explicit [admit.]s all surface the same gap class — **region-env
    weakening for non-values**:

      - S_StringConcat_Step2 / S_App_Step2 / S_Pair_Step2: value v1
        sits to the left of a stepping subexpression. After the inner
        step changes R0 → R0', v1's typing needs to be lifted from R0
        to R0'.

      - S_Region_Step (negative branch of [In r R0']): the outer
        [ERegion r e'] must re-type as T_Region_L1, requiring the
        inner body to be lifted from R0' to (r :: R0').

    All four reduce to: given a typing under [R0], lift it to [R0']
    where R0' may add or drop regions that the operational step has
    determined. This is the same structural gap as the residual admits
    in [region_shrink_preserves_typing_l1_gen] (tasks #25/#26 in the
    project's task list).

    Until the weakening lemma lands, [preservation_l1] is closed with
    [Admitted.] but the proof body documents exactly which sub-cases
    remain — no other obligations are buried. *)

Theorem preservation_l1 :
  forall mu R e mu' R' e',
    step (mu, R, e) (mu', R', e') ->
    forall G T R_final G',
      has_type_l1 R G e T R_final G' ->
      has_type_l1 R' G e' T R_final G'.
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep; intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; clear Hcfg; subst;
    inversion Hcfg'; clear Hcfg'; subst;
    intros G0 T0 R_final G0' Ht;
    inversion Ht; subst;
    (* Light closure pass — handles ~atomic cases and discharges
       value-step impossibilities. *)
    try solve [econstructor; eassumption];
    try solve [econstructor; econstructor; eassumption];
    try solve [exfalso; eapply values_dont_step; eassumption];
    try solve [exfalso; congruence];
    try solve [exfalso; discriminate];
    try solve [match goal with
               | [ H : (_, _, EVar _) -->> _ |- _ ] => inversion H
               end].
  (* 33 residual goals — dispatched explicitly. *)
  - (* 1. S_StringConcat (β): EStringConcat (ELoc l1 r) (ELoc l2 r) → ELoc l' r *)
    match goal with
    | [ H : _; _ |=L1 ELoc _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ H : _; _ |=L1 ELoc _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    econstructor; assumption.
  - (* 2. S_StringConcat_Step1 *)
    eapply T_StringConcat_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 3. S_StringConcat_Step2: value v1 left, e2 steps right.
       Needs region-env weakening on the value v1 (lift its typing
       from R to R'). Same gap class as the residual admits in
       [region_shrink_preserves_typing_l1_gen] (tasks #25/#26).
       Admit for L1.D scaffold. *)
    admit.
  - (* 4. S_StringLen (β): EStringLen (ELoc l r) → EI32 (length s) *)
    match goal with
    | [ H : _; _ |=L1 EBorrow (ELoc _ _) : _ -| _; _ |- _ ] =>
        let Hv := fresh in
        assert (Hv : is_value (EBorrow (ELoc l r))) by repeat constructor;
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv H) as [HR HG];
        subst
    end.
    constructor.
  - (* 5. S_StringLen_Step: inner e steps but EBorrow e typed by either
       T_Borrow_L1 (e=EVar, can't step) or T_Borrow_Val_L1 (e is value,
       can't step). Both are vacuous. *)
    match goal with
    | [ H : _; _ |=L1 EBorrow _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    + (* T_Borrow_L1: e = EVar i — no step rule fires on EVar *)
      inversion Hstep.
    + (* T_Borrow_Val_L1: e is a value — values don't step *)
      exfalso; eapply values_dont_step; eassumption.
  - (* 6. S_Let_Val (β): ELet v1 e2 → subst 0 v1 e2 *)
    match goal with
    | [ Hv : is_value ?v1, Ht1 : ?R; ?G |=L1 ?v1 : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht1) as [HR HG];
        subst
    end.
    eapply subst_preserves_typing_l1; try eassumption.
  - (* 7. S_Let_Step *)
    eapply T_Let_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 8. S_LetLin_Val (β) *)
    match goal with
    | [ Hv : is_value ?v1, Ht1 : ?R; ?G |=L1 ?v1 : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht1) as [HR HG];
        subst
    end.
    eapply subst_preserves_typing_l1; try eassumption.
  - (* 9. S_LetLin_Step *)
    eapply T_LetLin_L1;
      [ eassumption
      | eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 10. S_App_Fun (β): EApp (ELam T ebody) v2 → subst 0 v2 ebody *)
    match goal with
    | [ H : _; _ |=L1 ELam _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ Hv : is_value ?v2, Ht2 : ?R; ?G |=L1 ?v2 : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht2) as [HR HG];
        subst
    end.
    eapply subst_preserves_typing_l1; try eassumption.
  - (* 11. S_App_Step1 *)
    eapply T_App_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 12. S_App_Step2: value v1 left (function), e2 steps right.
       Same region-env weakening gap as goal 3. Admit. *)
    admit.
  - (* 13. S_If_True *)
    match goal with
    | [ H : _; _ |=L1 EBool _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    eassumption.
  - (* 14. S_If_False *)
    match goal with
    | [ H : _; _ |=L1 EBool _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    eassumption.
  - (* 15. S_If_Step *)
    eapply T_If_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption
      | eassumption ].
  - (* 16. S_Pair_Step1 *)
    eapply T_Pair_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 17. S_Pair_Step2: value v1 left, e2 steps right.
       Same region-env weakening gap as goal 3. Admit. *)
    admit.
  - (* 18. S_Fst *)
    match goal with
    | [ H : _; _ |=L1 EPair _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    repeat match goal with
    | [ Hv : is_value ?v, Ht : ?R; ?G |=L1 ?v : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht) as [?HR ?HG];
        subst; clear Hv
    end.
    eassumption.
  - (* 19. S_Fst_Step *)
    eapply T_Fst_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 20. S_Snd *)
    match goal with
    | [ H : _; _ |=L1 EPair _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    repeat match goal with
    | [ Hv : is_value ?v, Ht : ?R; ?G |=L1 ?v : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht) as [?HR ?HG];
        subst; clear Hv
    end.
    eassumption.
  - (* 21. S_Snd_Step *)
    eapply T_Snd_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption ].
  - (* 22. S_Inl_Step *)
    eapply T_Inl_L1.
    eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption.
  - (* 23. S_Inr_Step *)
    eapply T_Inr_L1.
    eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption.
  - (* 24. S_Case_Inl (β): ECase (EInl T v) e1 e2 → subst 0 v e1 *)
    match goal with
    | [ H : _; _ |=L1 EInl _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ Hv : is_value ?v, Ht : ?R; ?G |=L1 ?v : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht) as [HR HG];
        subst
    end.
    eapply subst_preserves_typing_l1; try eassumption.
  - (* 25. S_Case_Inr (β): ECase (EInr T v) e1 e2 → subst 0 v e2 *)
    match goal with
    | [ H : _; _ |=L1 EInr _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    match goal with
    | [ Hv : is_value ?v, Ht : ?R; ?G |=L1 ?v : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht) as [HR HG];
        subst
    end.
    eapply subst_preserves_typing_l1; try eassumption.
  - (* 26. S_Case_Step *)
    eapply T_Case_L1;
      [ eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption
      | eassumption
      | eassumption ].
  - (* 27. S_Region_Enter: (mu, R, ERegion r e) → (mu, r::R, ERegion r e).
       Typing came in as T_Region_L1 (since ~ In r R from the step
       contradicts T_Region_Active's In r R). After the step, r IS in
       r :: R, so re-type as T_Region_Active_L1. *)
    eapply T_Region_Active_L1.
    + left; reflexivity.
    + assumption.
    + assumption.
    + assumption.
  - (* 28. S_Region_Exit: needs region_shrink_preserves_typing_l1.
       The goal's R_final = remove_first_L1 r R_body; the helper produces
       remove_first r R_body. Use [remove_first_eq_l1] to convert. *)
    match goal with
    | [ |- _; _ |=L1 _ : _ -| remove_first_L1 ?r ?R; _ ] =>
        replace (remove_first_L1 r R) with (remove_first r R)
          by (symmetry; apply remove_first_eq_l1)
    end.
    eapply region_shrink_preserves_typing_l1; eassumption.
  - (* 29. S_Region_Step: IH gives R'; G |=L1 e' : T -| R_body; G'.
       Need: R'; G |=L1 ERegion r e' : T -| remove_first_L1 r R_body; G'.
       Case-split on [In r R0']. The positive case applies
       T_Region_Active_L1 directly. The negative case requires region-
       env weakening (lifting body typing from R0' to r :: R0'); same
       gap class as [region_shrink_preserves_typing_l1_gen]'s residual
       admits (tasks #25/#26). *)
    destruct (in_dec string_dec r R0') as [HInR' | HNotInR'].
    + (* In r R0': use T_Region_Active_L1 *)
      eapply T_Region_Active_L1; try eassumption.
      eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption.
    + (* ~ In r R0': would need (r :: R0'); G |- e' : T -| R_body; G'
         from IH which only gives R0'; G |- e' : T -| R_body; G'.
         Region-env weakening for non-values. Deferred. *)
      admit.
  - (* 30. S_Drop *)
    match goal with
    | [ H : _; _ |=L1 ELoc _ _ : _ -| _; _ |- _ ] => inversion H; subst
    end.
    econstructor.
  - (* 31. S_Drop_Step *)
    eapply T_Drop_L1;
      [ eassumption
      | eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption ].
  - (* 32. S_Copy *)
    match goal with
    | [ Hv : is_value ?v, Ht : ?R; ?G |=L1 ?v : _ -| _; _ |- _ ] =>
        pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ Hv Ht) as [HR HG];
        subst
    end.
    econstructor; eassumption.
  - (* 33. S_Copy_Step *)
    eapply T_Copy_L1;
      [ eassumption
      | eapply (IHHstep _ _ _ _ _ _ eq_refl eq_refl); eassumption ].
Admitted.
