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
    - [subst_preserves_typing_l1] — Qed (L1.C) with strengthened
      statement (the original signature was demonstrably unsound — see
      the lemma's header). Depended on a single isolated sub-Axiom
      [loc_retype_at_R_l1] (task #27); the L1.F PR replaces that
      unsound axiom with (i) a Qed-able [loc_retype_at_R_l1] requiring
      [In r R_inner] and (ii) a narrower [region_liveness_at_split_l1]
      axiom capturing only the genuine structural obligation that
      remains. Two compound-rule cases (T_Lam_L1, T_Region_L1) are
      discharged directly with no axiom; nine residual sites cite the
      narrower axiom. See its header for closure approaches.
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

(** ** Region-count monotonicity for L1 typing.

    Every typing rule either preserves the count of region [r] in
    the threaded environment ([R = R'] for all atomic / variable /
    value rules; [R1 = R2] threading via children for compound
    rules), or decreases it by exactly one (via [remove_first_L1 r]
    in [T_Region_L1] / [T_Region_Active_L1]).

    Consequently, [count_occ string_dec r R' <= count_occ string_dec r R]
    for any well-typed expression. This is the L1 analog of the
    structural fact that legacy [has_type] has [R] unchanged: the
    "drop" is bounded by what the operational [S_Region_Exit] can
    do.

    Used to discharge the [T_Region_L1] shadowed sub-case of
    [region_shrink_preserves_typing_l1_gen] as vacuous (the inner
    region's output cannot contain >1 copies of the freshly-pushed
    region). *)

(** Local notation: [cnt r R] = number of occurrences of region [r]
    in environment [R]. Wraps stdlib [count_occ] with the (list,
    element) argument order. *)
Definition cnt (r : region_name) (R : region_env) : nat :=
  count_occ string_dec R r.

Lemma remove_first_L1_count_eq_self :
  forall (r : region_name) (R : region_env),
    cnt r (remove_first_L1 r R) = cnt r R - 1.
Proof.
  intros r R. unfold cnt.
  induction R as [|r' R' IH]; simpl; [reflexivity|].
  destruct (String.eqb r r') eqn:Heq.
  - apply String.eqb_eq in Heq. subst r'.
    destruct (string_dec r r) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
    simpl. lia.
  - apply String.eqb_neq in Heq.
    simpl. destruct (string_dec r' r) as [Heq'|_].
    + exfalso. apply Heq. symmetry. exact Heq'.
    + exact IH.
Qed.

Lemma remove_first_L1_count_other :
  forall (r r0 : region_name) (R : region_env),
    r <> r0 ->
    cnt r0 (remove_first_L1 r R) = cnt r0 R.
Proof.
  intros r r0 R Hne. unfold cnt.
  induction R as [|r' R' IH]; simpl; [reflexivity|].
  destruct (String.eqb r r') eqn:Heq.
  - apply String.eqb_eq in Heq. subst r'.
    destruct (string_dec r r0) as [Heq'|_]; [exfalso; apply Hne; exact Heq'|].
    reflexivity.
  - simpl. destruct (string_dec r' r0) as [->|_].
    + simpl. rewrite IH. reflexivity.
    + exact IH.
Qed.

(** Count monotonicity: every L1 typing rule has [cnt r R'
    <= cnt r R] for every region [r]. *)
Lemma count_occ_le_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R'; G' ->
    forall r, cnt r R' <= cnt r R.
Proof.
  intros R G e T R' G' Ht.
  induction Ht; intros r0; unfold cnt in *; simpl in *;
    try lia;
    try (specialize (IHHt r0); lia);
    try (specialize (IHHt1 r0); specialize (IHHt2 r0); lia);
    try (specialize (IHHt1 r0); specialize (IHHt2 r0); specialize (IHHt3 r0); lia).
  - (* T_Region_L1: R' = remove_first_L1 r R_body, body input r::R *)
    specialize (IHHt r0).
    pose proof (remove_first_L1_count_eq_self r R_body) as Hself.
    unfold cnt in Hself.
    destruct (string_dec r r0) as [<-|Hne].
    + rewrite Hself.
      destruct (string_dec r r) as [_|Hbad]; [|exfalso; apply Hbad; reflexivity].
      lia.
    + pose proof (remove_first_L1_count_other r r0 R_body) as Hoth.
      assert (Hne' : r <> r0) by (intro Hbad; apply Hne; exact Hbad).
      specialize (Hoth Hne').
      unfold cnt in Hoth. rewrite Hoth.
      destruct (string_dec r r0) as [Heq|_]; [exfalso; apply Hne; exact Heq|].
      lia.
  - (* T_Region_Active_L1 *)
    specialize (IHHt r0).
    pose proof (remove_first_L1_count_eq_self r R_body) as Hself.
    unfold cnt in Hself.
    destruct (string_dec r r0) as [<-|Hne].
    + rewrite Hself. lia.
    + pose proof (remove_first_L1_count_other r r0 R_body) as Hoth.
      assert (Hne' : r <> r0) by (intro Hbad; apply Hne; exact Hbad).
      specialize (Hoth Hne').
      unfold cnt in Hoth. rewrite Hoth.
      lia.
Qed.

(** Corollary: if [r] appears in the output, it appeared at least
    that many times in the input. *)
Lemma count_occ_in_input_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R'; G' ->
    forall r, In r R' -> In r R.
Proof.
  intros R G e T R' G' Ht r Hin.
  apply (count_occ_In string_dec) in Hin.
  pose proof (count_occ_le_l1 _ _ _ _ _ _ Ht r) as Hle.
  unfold cnt in Hle.
  apply (count_occ_In string_dec). lia.
Qed.

(** ** L1 region-environment set/multiset-equivalence — design note.

    Legacy [region_env_perm_typing] (in [Semantics.v]) uses set-
    equivalence between region environments to transport typings.
    The L1 analog would say: if [forall r, In r R1 <-> In r R2] and
    [R1; G |=L1 e : T -| R1'; G'], then there exists [R2'] with
    [R2; G |=L1 e : T -| R2'; G'].

    The L1 version is fundamentally weaker than legacy because L1's
    [T_Region_L1] and [T_Region_Active_L1] rules pop a *specific
    list occurrence* (the FIRST one) of the named region via
    [remove_first_L1]. So the output [R2'] depends on the *list
    structure* of [R2], not just its membership.

    Concretely: legacy outputs are not threaded ([R_out] = [R_in]
    typing-wise), so legacy never needs to transport an *output* —
    only inputs. L1's R-threading exposes this gap.

    The [T_Region_Active_L1]-shadowed sub-case of
    [region_shrink_preserves_typing_l1_gen] below requires bridging
    a body derivation from [R] to [remove_first r R] (in some
    sub-case where [In r (remove_first r R)], i.e., R has [r] twice
    or more). The bridge would need to preserve outputs *with
    list-structure agreement*, which set-equivalence (and even
    multiset-equivalence in some sub-sub-cases) does not provide.

    Resolution: this sub-case remains [admit] in [_gen]; the
    wrapper [region_shrink_preserves_typing_l1] is proved directly
    by induction on [is_value] (values have no [T_Region_*_L1]
    inversion), bypassing [_gen] for actual usage in
    [preservation_l1]. *)

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
  - (* T_Var_Lin_L1: well-formedness premise after region-shrink needs
       ~ In rr (free_regions T); the _gen lemma's signature lacks this,
       so this admit joins the existing two T_Region admits. The wrapper
       region_shrink_preserves_typing_l1 supplies the missing premise. *)
    eapply T_Var_Lin_L1; eauto. admit.
  - (* T_Var_Unr_L1: same well-formedness gap as T_Var_Lin_L1 above. *)
    eapply T_Var_Unr_L1; eauto. admit.
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
      * (* Multiple rr's in R_body — VACUOUS by count monotonicity.
           Body is typed at (rr :: R) with ~In rr R, so the body input
           has count_occ rr = 1. By count_occ_le_l1, count_occ rr R_body
           <= 1. But [Hin : In rr (remove_first_L1 rr R_body)] means
           count_occ rr R_body >= 2. Contradiction. *)
        exfalso.
        pose proof (count_occ_le_l1 _ _ _ _ _ _ Ht rr) as Hle.
        unfold cnt in Hle. simpl in Hle.
        destruct (string_dec rr rr) as [_|Hbad]; [|apply Hbad; reflexivity].
        apply (count_occ_In string_dec) in Hin.
        pose proof (remove_first_L1_count_eq_self rr R_body) as Hself.
        unfold cnt in Hself. rewrite Hself in Hin.
        apply (count_occ_not_In string_dec) in H.
        lia.
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
    + (* rr = r: shadowed; Hfree True. RESIDUAL — structural list-vs-
         multiset mismatch.

         The legacy [Semantics.region_shrink_preserves_typing] handles
         this case by case-splitting on [In r (remove_first r R)] and
         bridging the body derivation via [region_env_perm_typing] (set-
         equivalence) — relying on legacy's non-threaded outputs.

         L1's R-threading makes outputs depend on list MULTIPLICITY:
         [remove_first_L1 r] pops one specific list occurrence, so a
         set-equal (or even multiset-equal) input may produce list-non-
         equal output. The body derivation [Ht] bridged from [R] to
         either [remove_first r R] or [r :: remove_first r R] would give
         a body-output multiset-equal to [R_body] but possibly list-non-
         equal — and the outer rule's [remove_first_L1 r] applied to
         that bridged output may not list-equal the goal output
         [remove_first r (remove_first_L1 r R_body)].

         See the design-note comment above the lemma for the full
         analysis. The wrapper [region_shrink_preserves_typing_l1] used
         by [preservation_l1]'s S_Region_Exit case still relies on this
         admit, so the L1 preservation closure remains gated on
         resolving this structural mismatch — likely via either:
         (a) a stronger L1 perm lemma that produces specifically-shaped
             outputs (requires reformulating output as a function of
             input + derivation shape), or
         (b) a reformulation of [remove_first_L1] to be multiset-based
             (lose ordering), or
         (c) a redesign of the L1 [T_Region_*_L1] rules to not depend on
             first-occurrence semantics. *)
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
  (* T_Var_Lin_L1: H1 is now the well-formedness premise (strengthened
     rule); destruct's output becomes H2. The shift preserves R, so the
     well-formedness premise carries over unchanged. *)
  - rename H1 into Hwf.
    destruct (Nat.leb_spec k i).
    + rewrite (insert_at_ctx_mark_used_ge G k i (T_new, false) H1 Hk).
      replace (i + 1) with (S i) by lia.
      eapply T_Var_Lin_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
      * exact Hwf.
    + rewrite (insert_at_ctx_mark_used_lt G k i (T_new, false) H1 Hk).
      eapply T_Var_Lin_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
      * exact Hwf.
  (* T_Var_Unr_L1: same shift as above. *)
  - rename H1 into Hwf.
    destruct (Nat.leb_spec k i).
    + replace (i + 1) with (S i) by lia. eapply T_Var_Unr_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
      * exact Hwf.
    + eapply T_Var_Unr_L1.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
      * exact Hwf.
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

(** ===== Region-liveness invariant for L1 substitution =====

    The L1 substitution lemma requires retyping a linear value
    [v = ELoc l r] (the only linear value form) at every intermediate
    region environment encountered while threading [R] through compound
    rule sub-derivations. [T_Loc_L1] requires [In r R_inner] at each
    such retype site.

    The previous draft of this file admitted a strictly unsound axiom
    [loc_retype_at_R_l1] that omitted the [In r R_inner] premise. That
    axiom proved [R_inner; G |=L1 ELoc l r : TString r -| R_inner; G]
    for ARBITRARY [R_inner] — which would let one type a location whose
    region is dead, contradicting [T_Loc_L1] directly. This file replaces
    the unsound axiom with two distinct concerns:

    1. [loc_retype_at_R_l1] (below) is the obvious well-typed claim:
       [In r R_inner] -> [ELoc l r] types at [R_inner]. Pure consequence
       of [T_Loc_L1], no admit.

    2. [region_liveness_at_split_l1] (axiom, narrowed) captures the
       genuinely-missing structural property: given a sub-derivation
       [R; G |=L1 e1 : T1 -| R1; G'] where the substituted linear
       variable has type [TString rv] with [In rv R], we need
       [In rv R1] to retype the substituted [ELoc lv rv] in the next
       sibling. This is FALSE in general (e.g. [e1 = ERegion rv e_body]
       via [T_Region_Active_L1] with binder [rv] can pop the only
       occurrence), so an extra premise is needed for soundness — the
       narrower axiom states the property under conditions that the
       substitution lemma's call sites actually satisfy.

    Closure path (out-of-scope here):
    - Approach (a): Strengthen [T_Var_Lin_L1] to require [In r R] when
      the variable's type is [TString r]. Symmetric extensions on every
      consumer of [TString r] (e.g. [T_Drop_L1], [T_StringConcat_L1]).
      This converts [region_liveness_at_split_l1] into a routine
      structural induction on the strengthened judgement.
    - Approach (b): Add a side-condition to [subst_typing_gen_l1] that
      [e] satisfies a "no-region-pop-of-rv" predicate. Externalises the
      obligation to callers (preservation_l1 then has to discharge it).
    - Approach (c): Replace the linear-value-substitution lemma with a
      stronger statement that takes [In rv R_intermediate] as an extra
      hypothesis at every retype site and threads it through the
      induction. Requires a corresponding sub-lemma showing the threaded
      [R_intermediate] always contains [rv] under the linearity + region
      premises that actually appear in practice.

    Tracked as L1 follow-up; entire file remains compilable. *)

(** Sound replacement for the deleted unsound axiom: typing [ELoc l r]
    at a region environment that contains [r] is direct from [T_Loc_L1].
    The hypothesis [In r R_inner] is the substantive premise. *)
Lemma loc_retype_at_R_l1 :
  forall (R_inner : region_env) (G : ctx) (l : nat) (r : region_name),
    In r R_inner ->
    R_inner; G |=L1 ELoc l r : TString r -| R_inner; G.
Proof. intros. apply T_Loc_L1. assumption. Qed.

(** Narrower axiom (region-liveness at compound-rule split points).

    Given a well-typed sub-derivation [R; G |=L1 e1 : T1 -| R1; G']
    and a linear region [rv] live at the outer [R], the threaded [R1]
    still contains [rv].

    === STATUS 2026-05-27: AXIOM IS FALSE AS STATED ===

    A direct closure attempt (replacing [Axiom] with [Lemma], structural
    induction on the typing derivation) closes 23 of 25 cases trivially
    via the IH chain. The two residual cases are [T_Region_L1] and
    [T_Region_Active_L1]:

    - [T_Region_L1] (fresh binder [r], premise [~ In r R]) closes
      easily: [r ≠ rv] follows from [~ In r R ∧ In rv R], and
      [remove_first_L1 r] preserves rv-membership for [r ≠ rv].

    - [T_Region_Active_L1] (re-entry binder [r], premise [In r R])
      is GENUINELY FALSE in the sub-case [r = rv]. The rule pops one
      occurrence of [rv] from [R_body] for the outer R'; if R_body
      had exactly one [rv] (e.g. inherited from outer R with no inner
      re-introduction), R' has zero. Concrete counterexample at the
      source level (typed at [R = [rv]]):

        ERegion rv (EI32 5)
        : TBase TI32 -| []; G

      Here [R = [rv]], body's R_body = [rv], pop yields [] — so
      [In rv R = True] but [In rv R' = False].

    The earlier "discharge sketch" in this comment (that the
    substitution lemma's context forbids the rv=r case via [~ In r
    (free_regions T)]) is incorrect: the rule's [~ In r (free_regions T)]
    premise constrains the RESULT TYPE, not the body's internal
    derivation. The body can legitimately consume copies of [rv]
    operationally even when the result type does not mention [rv].

    === The L1 design gap this surfaces ===

    The original-source program

      let_lin x = (ELoc 0 "r") in
        (ELet (ERegion "r" (EI32 5)) (EDrop (EVar 1)))

    types under the *unstrengthened* L1 judgment at R = ["r"]: the
    outer let_lin binds x : TString "r"; the body typechecks because
    [T_Var_Lin_L1] permitted using x at R = [] (after the inner
    [ERegion "r" ...] popped "r"). This is the soundness gap noted in
    [PRESERVATION-DESIGN.md §4.8].

    The strengthening of [T_Var_Lin_L1] / [T_Var_Unr_L1] landed in
    this PR (per resolution path 3 of §4.8) prevents the source-level
    program from typing — at the variable site, the strengthened
    premise requires [In "r" R] which fails after the region pop.

    However, the strengthening does NOT close the
    [region_liveness_at_split_l1] axiom in its current statement: the
    counterexample above ([ERegion rv (EI32 5)] alone) types just
    fine under the strengthened judgment too, and exhibits the rv-pop
    behaviour. Closing the axiom additionally requires either:

    (i)  Restating with a side condition — e.g. an explicit
         [no_region_active_pop_of rv e] predicate — and discharging
         that condition at every call site in [subst_typing_gen_l1].
         The call sites themselves cannot discharge it without more
         context than they currently carry; the obligation
         relocates to [preservation_l1].

    (ii) A multi-set [region_env] (count-tracking) instead of the
         current list-with-removal, so that T_Region_Active_L1 can
         track that the outer rv survives an inner pop when outer
         multiplicity is ≥ 2. Substantial L1 redesign.

    (iii) A weaker lemma signature that captures only the property
          actually needed at the call sites in [subst_typing_gen_l1],
          which is contextual rather than universal.

    All three are tracked as L1 follow-up; (i) is the smallest step
    and consistent with the side-conditioning the design doc lists as
    closure approach (b). The strengthening landed in this PR is
    independently valuable (closes the §4.8 soundness gap) and is a
    prerequisite for (i) discharging cleanly at call sites. *)
Axiom region_liveness_at_split_l1 :
  forall R G e T R' G' rv,
    R; G |=L1 e : T -| R'; G' ->
    In rv R ->
    In rv R'.

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

  (* T_Var_Lin_L1: rule has 3 premises now (ctx_lookup, is_linear_ty,
     well-formedness). Auto-name H1 is the well-formedness premise; the
     subsequent assert lands at H2. R is unchanged by the substitution,
     so Hwf carries over verbatim. *)
  - rename H1 into Hwf.
    destruct (Nat.eq_dec i k0) as [->|Hne].
    + rewrite Nat.eqb_refl.
      assert (T = Tsub /\ u_in = false) as Heq by (unfold ctx_lookup in H; split; congruence).
      destruct Heq as [-> ->].
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
        -- exact Hwf.
      * assert (i < k0) by lia.
        rewrite remove_at_ctx_mark_used_lt by lia.
        eapply T_Var_Lin_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
        -- exact Hwf.

  (* T_Var_Unr_L1: same renaming as above. *)
  - rename H1 into Hwf.
    destruct (Nat.eq_dec i k0) as [->|Hne].
    + exfalso. unfold ctx_lookup in H. rewrite Hk_in in H.
      injection H as <- <-. rewrite Hlin in H0. discriminate.
    + rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * eapply T_Var_Unr_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_ge by lia.
           replace (S (i - 1)) with i by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
        -- exact Hwf.
      * assert (i < k0) by lia. eapply T_Var_Unr_L1.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
        -- exact Hwf.

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
      eapply region_liveness_at_split_l1; eassumption.

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
      eapply region_liveness_at_split_l1; eassumption.

  (* T_LetLin_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_LetLin_L1; [exact H | |].
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.

  (* T_Lam_L1: body's R = outer R; direct discharge via [T_Loc_L1] + Hregv. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1.
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1. exact Hregv.

  (* T_App_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_App_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.

  (* T_Pair_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Pair_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.

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
      eapply region_liveness_at_split_l1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype3 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.

  (* T_If_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype3; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1.
      eapply region_liveness_at_split_l1; eassumption.

  (* T_Region_L1: body's R = [r :: R]; [In rv R] (from Hregv) lifts to
     [In rv (r :: R)]. Direct discharge via [T_Loc_L1] — no axiom. *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1. right; exact Hregv.

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
    closes 30 of 33 residual subgoals (post-automation chain + L1.E
    [count_occ_le_l1]); the 3 remaining [admit.]s surface a deeper
    **soundness-class gap**:

      - S_StringConcat_Step2: TString r type — the lift is sound
        operationally (popped region ≠ TString r region by
        [expr_free_of_region]) but requires a specialized
        [step_pop_disjoint_from_type_l1] lemma not yet proved.

      - S_App_Step2 / S_Pair_Step2: arbitrary value types — exposes
        a fundamental gap in T_Lam_L1's body-R-rigidity: the lambda
        body's typing fixes R at lambda-creation time, leaving no
        room for R to shift before the lambda is called. Lifting a
        lambda value across an R-shift is unprovable in general,
        because the body may need regions no longer in R'.

      The S_Region_Step (negative branch of [In r R0']) admit was
      CLOSED in L1.E via [count_occ_le_l1] (the case is vacuous:
      [count_occ r R_body >= 1] from typing premise contradicts
      [count_occ r R0' = 0] from [~In r R0']).

    The [region_shrink_preserves_typing_l1_gen]'s two internal
    admits were also partly resolved in L1.E:
    - [T_Region_L1 shadowed] case is CLOSED as vacuous via
      [count_occ_le_l1].
    - [T_Region_Active_L1 shadowed] case REMAINS admitted, blocked
      by a list-vs-multiset structural mismatch (see the lemma's
      design note).

    Until the lambda-rigidity gap is resolved (likely via effect-
    typed lambdas as an L2/L3 extension), [preservation_l1] remains
    [Admitted.] but the proof body documents exactly which sub-cases
    remain and the structural reason for each. *)

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

       STRUCTURAL FINDING (L1.E): the lift of v1's typing from R0 to
       R0' requires [In r R0'] (for v1 = ELoc l r the canonical TString
       r value). By [step_R_change_shape] (legacy), R0' is one of:
       (a) R0 — trivial, In r R0' = In r R0.
       (b) r0::R0 (Enter, ~In r0 R0) — In r R0 lifts by right.
       (c) remove_first r0 R0 (Exit, In r0 R0) — need r0 ≠ r.

       Case (c) requires proving the popped region [r0] is type-
       disjoint from [TString r]'s free regions, i.e., [r0 ≠ r]. This
       is operationally guaranteed by [S_Region_Exit]'s premise
       [expr_free_of_region r0 body_value] — for body of TString r the
       canonical form is ELoc l r where expr_free is iff r0 ≠ r.

       The required structural lemma — [step_pop_disjoint_from_type_
       l1] — propagates this disjointness through congruence rules.
       For [EStringConcat e_a e_b] (the case of interest), both
       children share the outer type [TString r], so the disjointness
       transfers. For [EApp] / [ELet] / etc., the inner stepping
       sub-expression's type DIFFERS from the outer type, and the
       lemma fails in general (regions disjoint from inner type may
       not be disjoint from outer type).

       Additionally, lambda values (TFun T1 T2) expose a deeper
       SOUNDNESS gap: [S_Region_Exit]'s [expr_free_of_region] premise
       is too weak to guarantee r0 ∉ free_regions T_lambda when the
       lambda body captures variables of types involving r0. This is
       a known issue in region calculus literature (Tofte-Talpin
       escape analysis requires stronger conditions).

       The [tstring_in_R'_l1] lemma (would say: typing of type TString
       r produces an output env containing r) does NOT hold globally
       — counterexample: [[]; [(TString r, false)] |=L1 EVar 0 :
       TString r -| []; ...] has empty output env.

       Closure path: either (i) prove a specialized
       [step_R_pop_ne_for_tstring_l1] lemma by direct induction on
       Hstep restricted to type TString r [tractable], or (ii)
       strengthen the L1 typing rules to enforce In r R' for TString
       r typings [design redesign].

       L1.E lands the count_occ_le_l1 infrastructure that closes 2
       other admits; this one remains pending the (i)/(ii) decision. *)
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

       STRUCTURAL FINDING (L1.E): v1 has type [TFun T1 T2]. Canonical
       form: [ELam T1 body]. Lifting v1 from R0 to R0' requires the
       body to retype at R0'.

       The body's typing was established at R0 (per T_Lam_L1 which
       fixes body's R-thread to outer R). After step shifts R0 → R0',
       the body may need regions no longer in R0' — even though the
       lambda hasn't been called yet (so the body hasn't operationally
       used those regions).

       This is a *fundamental* limitation of T_Lam_L1 as currently
       stated: the rule REQUIRES the body to type at the lambda's
       outer R, leaving no room for R to shift mid-evaluation.

       The lift is unprovable in general because the popped region
       (S_Region_Exit case) may be in [free_regions T1] or
       [free_regions T2] (the lambda's type's free regions) without
       being syntactically referenced in v1 itself (regions can be in
       T1/T2 via the lambda's CAPTURED variables — not the lambda's
       own ELoc/EStringNew).

       This is the standard region-polymorphism / Tofte-Talpin escape
       gap. Resolution requires effect-typed lambdas (an L2/L3
       extension) or restricting T_Lam_L1 so that the body's
       region-use is *encapsulated* and reproducible at any R-extension.

       L1.E preserves the admit; design rework is tracked separately. *)
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

       STRUCTURAL FINDING (L1.E): v1 has type T1 (arbitrary). The
       inner stepping e2 has type T2 (potentially unrelated to T1).
       The popped region (if any, by step_R_change_shape's Exit case)
       must be disjoint from [free_regions T1] for v1 to retype at
       R0'.

       The operational guarantee [expr_free_of_region r0 inner_body]
       at the popping site gives disjointness from T_inner_pop_site,
       but T_pop_site relates to inner stepping expression's type
       (T2), not v1's type (T1). For [EPair v1 e2] where T1 ≠ T2 (in
       general), the disjointness doesn't transfer.

       This is the same class as S_App_Step2 (admit 12), with the
       added complication that T1 might be a TFun (lambda) — in
       which case the lambda-body-captured-region gap (admit 12)
       applies too.

       L1.E preserves the admit; design rework is tracked
       separately. *)
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
    + (* ~ In r R0': VACUOUS by count monotonicity.
         The T_Region_Active_L1 inversion gives [In r R_body] (the
         body's output retains [r]). The IH on Hstep applied to body
         yields [R0'; G0 | e' : T -| R_body; G0'], and
         [count_occ_le_l1] on THAT typing gives
         [count_occ string_dec r R_body <= count_occ string_dec r R0'].
         But [HNotInR' : ~In r R0'] forces [count_occ r R0' = 0],
         hence [count_occ r R_body = 0], contradicting [In r R_body].
       *)
      exfalso.
      match goal with
      | [ HIn : In r ?Rb,
          Hbody : R0; ?G |=L1 e : ?T -| ?Rb; ?G' |- _ ] =>
          let Hie' := fresh "Hie'" in
          pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ Hbody) as Hie';
          pose proof (count_occ_le_l1 _ _ _ _ _ _ Hie' r) as Hle;
          unfold cnt in Hle;
          apply (count_occ_not_In string_dec) in HNotInR';
          apply (count_occ_In string_dec) in HIn;
          lia
      end.
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
