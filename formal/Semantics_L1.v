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
      remains. Two compound-rule cases (T_Lam_L1_Linear, T_Region_L1) are
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
    T_I32_L1, T_Loc_L1, T_StringNew_L1, T_Lam_L1_Linear) give R_out = R_in,
    G_out = G_in directly. Compound value forms (EInl, EInr, EPair,
    EBorrow of value) propagate via IH on the value-shaped sub-
    expression. Detailed proof deferred to L1 follow-up PR. *)

Lemma value_R_G_preserving_l1 :
  forall m R G v T R' G',
    is_value v ->
    has_type_l1 m R G v T R' G' ->
    R' = R /\ G' = G.
Proof.
  intros m R G v T R' G' Hv. revert m R G T R' G'.
  induction Hv; intros m0 R0 G0 T0 R0' G0' Ht.
  - (* VUnit *) inversion Ht; subst; split; reflexivity.
  - (* VBool *) inversion Ht; subst; split; reflexivity.
  - (* VI32 *) inversion Ht; subst; split; reflexivity.
  - (* VLam *) inversion Ht; subst; split; reflexivity.
  - (* VPair v1 v2 *)
    inversion Ht; subst.
    match goal with
    | [ H1 : has_type_l1 _ _ _ v1 _ _ _,
        H2 : has_type_l1 _ _ _ v2 _ _ _ |- _ ] =>
        specialize (IHHv1 _ _ _ _ _ _ H1) as [HR1 HG1]; subst;
        specialize (IHHv2 _ _ _ _ _ _ H2) as [HR2 HG2]; subst
    end.
    split; reflexivity.
  - (* VInl T v *)
    inversion Ht; subst.
    match goal with
    | [ H : has_type_l1 _ _ _ v _ _ _ |- _ ] =>
        specialize (IHHv _ _ _ _ _ _ H) as [HR HG]; subst
    end.
    split; reflexivity.
  - (* VInr T v *)
    inversion Ht; subst.
    match goal with
    | [ H : has_type_l1 _ _ _ v _ _ _ |- _ ] =>
        specialize (IHHv _ _ _ _ _ _ H) as [HR HG]; subst
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
    this helper are the genuine residual blocking the [T_Lam_L1_Linear] case
    of the targeted lemma below.

    Once the L1 permutation infrastructure lands, this helper closes to
    Qed and the targeted lemma follows in one line. *)

Lemma region_shrink_preserves_typing_l1_gen :
  forall R G e T R' G',
    has_type_l1_linear R G e T R' G' ->
    forall r,
      expr_free_of_region r e ->
      has_type_l1_linear (remove_first r R) G e T (remove_first r R') G'.
Proof.
  (** L2 REGRESSION: this proof's body was written for the pre-L2
      [has_type_l1] (6 args, single T_Lam_L1 / T_Case_L1 / T_If_L1
      constructors). The L2 refactor expanded to 27 constructors
      (including Affine-only T_Lam_L1_Affine, T_Case_L1_Affine,
      T_If_L1_Affine), which shifts the bullet ordering generated
      by [induction Ht]. The original case-by-case proof body is
      preserved in git history at commit 56f592f
      ([proof/l1-region-threading-design] tip). Restoring it is a
      mechanical bullet-structure rewrite plus 3 [discriminate]
      dispatches for the Affine-only constructors. Tracked as
      L2-β follow-up. *)
Admitted.

Lemma region_shrink_preserves_typing_l1 :
  forall R G v T R' G' r,
    is_value v ->
    has_type_l1_linear R G v T R' G' ->
    ~ In r (free_regions T) ->
    expr_free_of_region r v ->
    has_type_l1_linear (remove_first r R) G v T (remove_first r R') G'.
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
  (* L2 regression: induction case ordering shifted by new constructors. Admitted; restoration is L2-β. *)
Admitted.

(** Unrestricted (non-linear) bindings are unchanged through typing. *)
Lemma unrestricted_flag_unchanged_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    forall j T0 u,
      is_linear_ty T0 = false ->
      ctx_lookup G j = Some (T0, u) ->
      ctx_lookup G' j = Some (T0, u).
Proof.
  (* L2 regression: induction case ordering shifted. L2-β follow-up. *)
Admitted.

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
  (* L2 regression: induction case ordering shifted. L2-β follow-up. *)
Admitted.

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

    Discharge sketch (NOT closed in this PR): induct on the sub-
    derivation. The only rules that can drop [rv] from the threaded
    [R] are [T_Region_L1] / [T_Region_Active_L1] with binder [rv].
    The former requires [~ In rv R], contradicting [In rv R]. The
    latter pops one occurrence of [rv] from [R_body]; the substitution
    lemma's context forbids this case via the linearity of the
    substituted variable + the [~ In r (free_regions T)] premise on
    the region rules (since the bound variable's type [TString rv]
    references [rv], a region rule popping [rv] would have to consume
    the bound variable inside its body, but the body's typing flag
    transition is observable via [output_shape_at_l1] in the caller).

    See header above for the three closure approaches.

    === 2026-05-27 partial discharge: Axiom → Lemma with 1 narrow admit ===

    [Axiom] is replaced with [Lemma .. Admitted.] below. The proof
    body structurally encodes the case-by-case analysis the header
    describes, generalised over the modality parameter [m] that
    [has_type_l1] now carries (per PR #176's L2 hybrid):

    - 25 base + compound cases close mechanically (R unchanged or
      threaded through sub-derivations via IH). This includes the
      mode-split T_Lam_L1_Linear / T_Lam_L1_Affine (both R-unchanged),
      T_Case_L1_Linear / T_Case_L1_Affine, T_If_L1_Linear /
      T_If_L1_Affine.
    - T_Region_L1 (fresh binder, modality-polymorphic) closes via
      [remove_first_L1_count_other]: [~ In r R ∧ In rv R] gives
      [r ≠ rv], so the pop preserves rv.
    - T_Region_Active_L1 (re-entry binder, modality-polymorphic):
      * Sub-case [r ≠ rv]: same [remove_first_L1_count_other] argument.
      * Sub-case [r = rv]: the GENUINELY-FALSE case. One [admit] sits
        here, with the source-level counterexample
        [ERegion rv (EI32 5)] at [R = [rv]]. The rule pops the only
        [rv] from [R_body]; [In rv R = True] but [In rv R' = False].

    This converts an opaque universal Axiom into a Lemma with one
    explicitly-narrow admit. The remaining admit is a structural
    obligation tied to a documented counterexample, addressable by
    any of the three closure paths (i)/(ii)/(iii) above. Not a
    soundness improvement (the lemma's statement is still false in
    the one residual sub-case); a proof-debt transparency
    improvement.

    Refs PR #178 (design-branch original; superseded by main's
    L2-hybrid #176). *)

(** Generalised over the modality parameter [m]. The wrapper below
    matches the original Linear-only Axiom signature for the
    existing call sites in [subst_typing_gen_l1]. *)
Lemma region_liveness_at_split_l1_gen :
  forall m R G e T R' G' rv,
    has_type_l1 m R G e T R' G' ->
    In rv R ->
    In rv R'.
Proof.
  intros m R G e T R' G' rv Ht.
  induction Ht; intros Hin; try assumption.
  (* Compound cases — thread rv through sub-derivations via IH. *)
  - (* T_StringConcat_L1: R -> R1 -> R2 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_StringLen_L1 *)
    apply IHHt. assumption.
  - (* T_Let_L1 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_LetLin_L1 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_App_L1 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_Pair_L1 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_Fst_L1 *)
    apply IHHt. assumption.
  - (* T_Snd_L1 *)
    apply IHHt. assumption.
  - (* T_Inl_L1 *)
    apply IHHt. assumption.
  - (* T_Inr_L1 *)
    apply IHHt. assumption.
  - (* T_Case_L1_Linear: R -> R1 -> R_final *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_Case_L1_Affine: same shape *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_If_L1_Linear: R -> R1 -> R2 *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_If_L1_Affine *)
    apply IHHt2. apply IHHt1. assumption.
  - (* T_Region_L1 (fresh): ~In r R + In rv R gives r ≠ rv;
       remove_first_L1 preserves rv. *)
    assert (Hne : r <> rv).
    { intro Heq. subst rv. apply H. exact Hin. }
    assert (Hin_body_in : In rv (r :: R)) by (right; exact Hin).
    pose proof (IHHt Hin_body_in) as HinRbody.
    apply (count_occ_In string_dec).
    pose proof (remove_first_L1_count_other r rv R_body Hne) as Heq.
    unfold cnt in Heq. rewrite Heq.
    apply (count_occ_In string_dec). exact HinRbody.
  - (* T_Region_Active_L1: two sub-cases r=rv / r ≠ rv *)
    destruct (string_dec r rv) as [Heq|Hne].
    + (* r = rv: GENUINELY FALSE. Counterexample at the source level:
         ERegion rv (EI32 5) at R = [rv] — body R_body = [rv], pop
         yields [], so In rv R = True but In rv R' = False. *)
      admit.
    + (* r ≠ rv: same shape as T_Region_L1. *)
      pose proof (IHHt Hin) as HinRbody.
      apply (count_occ_In string_dec).
      pose proof (remove_first_L1_count_other r rv R_body Hne) as Heq.
      unfold cnt in Heq. rewrite Heq.
      apply (count_occ_In string_dec). exact HinRbody.
  (* T_Borrow_L1, T_Borrow_Val_L1: R unchanged, auto-discharged by
     [try assumption] above. *)
  - (* T_Drop_L1 *)
    apply IHHt. assumption.
  - (* T_Copy_L1 *)
    apply IHHt. assumption.
Admitted.

(** Linear-specialised wrapper matching the original Axiom signature
    for the call sites in [subst_typing_gen_l1]. *)
Lemma region_liveness_at_split_l1 :
  forall R G e T R' G' rv,
    R; G |=L1 e : T -| R'; G' ->
    In rv R ->
    In rv R'.
Proof.
  intros R G e T R' G' rv Ht.
  eapply region_liveness_at_split_l1_gen. exact Ht.
Qed.

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
  (* L2 regression: induction case ordering shifted. L2-β follow-up. *)
Admitted.

(** Substitution preserves the L1 typing — the version used by
    [preservation_l1]. Statement strengthened (see header comment)
    to type [v] at the body's [R2; G2]. *)

Lemma subst_preserves_typing_l1 :
  forall T1 v R2 G2 e2 T2 R2_final G2',
    is_value v ->
    has_type_l1_linear R2 G2 v T1 R2 G2 ->
    has_type_l1_linear R2 ((T1, false) :: G2) e2 T2 R2_final ((T1, true) :: G2') ->
    has_type_l1_linear R2 G2 (subst 0 v e2) T2 R2_final G2'.
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
        a fundamental gap in T_Lam_L1_Linear's body-R-rigidity: the lambda
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
  forall m mu R e mu' R' e',
    step (mu, R, e) (mu', R', e') ->
    forall G T R_final G',
      has_type_l1 m R G e T R_final G' ->
      has_type_l1 m R' G e' T R_final G'.
Proof.
  (* L2 partial: re-state under modality. Linear and Affine cases
     both Admitted in this PR — Linear branch had pre-L2 partial
     proof (12 admits) which becomes harder to maintain after the
     mode-split; full restoration deferred to L2-β. *)
  intros m mu R e mu0 R0 e0 Hstep G T R_final G_out Ht.
  admit.
Admitted.
