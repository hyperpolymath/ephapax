(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  ✅ ACTIVE -- L1 semantics. Modality-indexed.                   ***
  ***                                                                ***
  ***  This is the post-counterexample L1 redesign. Extend HERE.     ***
  ***                                                                ***
  ***  3 `Admitted` lemmas remain (down from 7 mid-chain, 9 pre-     ***
  ***  bullet-restoration). L2-β closures so far:                    ***
  ***    - typing_preserves_bindings_l1 (now m-polymorphic)          ***
  ***    - unrestricted_flag_unchanged_l1                            ***
  ***    - shift_typing_gen_l1 (via shift_typing_gen_l1_m + wrapper) ***
  ***    - subst_typing_gen_l1 (via subst_typing_gen_l1_m + wrapper) ***
  ***    - count_occ_le_l1 (via count_occ_le_l1_m + wrapper)         ***
  ***    - region_shrink_preserves_typing_l1_gen (via                ***
  ***      region_shrink_preserves_typing_l1_gen_m + wrapper)        ***
  ***    - typing_preserves_length_l1, output_shape_at_l1,           ***
  ***      loc_retype_at_R_l1 all generalised to m-polymorphic       ***
  ***                                                                ***
  ***  Residual admits (L2-β follow-up):                             ***
  ***    1. region_shrink_preserves_typing_l1_gen_m — list-vs-       ***
  ***       multiset structural mismatch in T_Region_Active_L1       ***
  ***       shadowed case (1 internal admit). Bullet structure       ***
  ***       restored 2026-05-27; only the structural sub-case        ***
  ***       remains.                                                 ***
  ***    2. region_liveness_at_split_l1_gen — 1 narrow admit in the  ***
  ***       T_Region_Active_L1 [r = rv] sub-case (genuinely false    ***
  ***       per documented counterexample ERegion rv (EI32 5))       ***
  ***    3. preservation_l1 — capstone; depends on closing (1)+(2)   ***
  ***       under L2 dispatch + lambda-rigidity gap resolution       ***
  ***                                                                ***
  ***  DO NOT close them by:                                         ***
  ***    - introducing new `Axiom` declarations                      ***
  ***    - ad-hoc side conditions on compound rules                  ***
  ***    - strengthened lemma signatures dodging the L2 dispatch     ***
  ***                                                                ***
  ***  Cross-layer dependencies (L1's lambda-rigidity gap closes at  ***
  ***  L2) are documented in `formal/PRESERVATION-DESIGN.md §5.1`.   ***
  ***                                                                ***
  ***  See `STATUS.adoc`, `PROOF-NEEDS.md`, and                      ***
  ***  `formal/PRESERVATION-DESIGN.md`.                              ***
  *********************************************************************

*)

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
From Ephapax Require Import Modality.
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
  - (* VEcho T v — T_Echo_L1 (slice 3a) types this at [TEcho T]
       with R_out = R and G_out = G by construction; both invariants
       hold immediately. *)
    inversion Ht; subst; split; reflexivity.
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
Lemma count_occ_le_l1_m :
  forall m R G e T R' G',
    R ; G |=L1[m] e : T -| R' ; G' ->
    forall r, cnt r R' <= cnt r R.
Proof.
  intros m R G e T R' G' Ht.
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
  - (* T_Region_L1_Echo — same remove_first_L1 shape as T_Region_L1 *)
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
  - (* T_Region_Active_L1_Echo — same shape as T_Region_Active_L1 *)
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

(** Linear specialisation — preserves the legacy call sites. *)
Lemma count_occ_le_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R'; G' ->
    forall r, cnt r R' <= cnt r R.
Proof.
  intros R G e T R' G' Ht r.
  exact (count_occ_le_l1_m Linear R G e T R' G' Ht r).
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

    Resolution: this sub-case remains an internal [admit] in
    [region_shrink_preserves_typing_l1_gen_m] (the m-polymorphic
    helper). The Linear wrapper [_gen] and the value-restricted
    wrapper [region_shrink_preserves_typing_l1] (used by
    [preservation_l1]'s S_Region_Exit case) both still depend on
    it: an earlier note here suggested the value-wrapper could
    bypass [_gen_m] by induction on [is_value], but that fails on
    [VLam] — the lambda body is a non-value whose internal
    [ERegion r' e'] subterm may shadow the outer [r], hitting the
    same structural residual. Closure options are listed in the
    case's own comment within [_gen_m]. *)

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

(** ** Modality-polymorphic generalisation.

    Mirrors the L2-β pattern used by [subst_typing_gen_l1_m] and
    [shift_typing_gen_l1_m]: the structural shrinkage lemma is
    mode-blind (region operations don't depend on the modality),
    so we prove it once at arbitrary [m] and derive the Linear
    specialisation as a wrapper.

    One genuine residual [admit] remains — the [T_Region_Active_L1]
    [rr = r] shadowed sub-case, documented as the list-vs-multiset
    bridge in PROOF-NEEDS.md §2 and in the design-note comment
    above this lemma block. The L1 region-permutation infrastructure
    (analog of [region_env_perm_typing] and [region_add_typing])
    is needed to close it; bridging options are listed in the
    case's own comment. *)
(** Migrated to [expr_strictly_free_of_region] as the precondition
    (blocker 5 reformulation, 2026-05-28). The strict predicate gives
    the body strictly MORE information than the weak one — in
    particular, the [T_Region_*_L1] cases no longer rely on a
    shadow-short-circuited [True] in the [rr = r] subcase. The
    residual [admit] at the [T_Region_Active_L1] [rr = r] sub-case
    is blocked by a list-vs-multiset structural mismatch (Phase D
    work, NOT by predicate weakness — strengthening the predicate
    does not close it). The [admit] remains; see the case's own
    comment for resolution options. *)
Lemma region_shrink_preserves_typing_l1_gen_m :
  forall m R G e T R' G',
    R ; G |=L1[m] e : T -| R' ; G' ->
    forall r,
      expr_strictly_free_of_region r e ->
      remove_first r R ; G |=L1[m] e : T -| remove_first r R' ; G'.
Proof.
  intros m R G e T R' G' Ht.
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
  - (* T_Lam_L1_Linear *)
    apply T_Lam_L1_Linear. eapply IHHt; auto.
  - (* T_Lam_L1_Affine *)
    eapply T_Lam_L1_Affine. eapply IHHt; auto.
  - (* T_Lam_L1_Linear_Eff — body's R_in is separate from outer R, but
       the side condition [forall r, In r R -> In r R_in] survives
       outer shrinkage (smaller outer R ⊆ original R ⊆ R_in). The body
       typing at R_in is unchanged. *)
    eapply T_Lam_L1_Linear_Eff; [|eassumption].
    intros r0 Hin0. apply H. eapply remove_first_subset. exact Hin0.
  - (* T_Lam_L1_Affine_Eff — same pattern. *)
    eapply T_Lam_L1_Affine_Eff; [|eassumption].
    intros r0 Hin0. apply H. eapply remove_first_subset. exact Hin0.
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
  - (* T_Case_L1_Linear *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_Case_L1_Linear;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_Case_L1_Affine *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_Case_L1_Affine;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_If_L1_Linear *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_If_L1_Linear;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_If_L1_Affine *)
    destruct Hfree as [Hf1 [Hf2 Hf3]].
    eapply T_If_L1_Affine;
      [eapply IHHt1; auto | eapply IHHt2; auto | eapply IHHt3; auto].
  - (* T_Region_L1: ERegion r e (fresh r).
       Shadowed sub-case (rr = r) closes via count-monotonicity
       vacuity; descend sub-case (rr <> r) via the
       remove_first/remove_first_L1 commutation rewrite. *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed. Hfree is True (irrelevant). *)
      apply String.eqb_eq in Heq. subst r.
      rewrite (remove_first_not_in_id _ _ H).
      destruct (in_dec string_dec rr (remove_first_L1 rr R_body)) as [Hin | Hnotin].
      * (* Multiple rr's in R_body — VACUOUS by count monotonicity.
           Body is typed at (rr :: R) with ~In rr R, so the body input
           has count_occ rr = 1. By count_occ_le_l1_m, count_occ rr R_body
           <= 1. But Hin says count_occ rr R_body >= 2. Contradiction. *)
        exfalso.
        pose proof (count_occ_le_l1_m _ _ _ _ _ _ _ Ht rr) as Hle.
        unfold cnt in Hle. simpl in Hle.
        destruct (string_dec rr rr) as [_|Hbad]; [|apply Hbad; reflexivity].
        apply (count_occ_In string_dec) in Hin.
        pose proof (remove_first_L1_count_eq_self rr R_body) as Hself.
        unfold cnt in Hself. rewrite Hself in Hin.
        apply (count_occ_not_In string_dec) in H.
        lia.
      * (* At most one rr in R_body. Then
           remove_first rr (remove_first_L1 rr R_body) =
           remove_first_L1 rr R_body. *)
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
      eapply T_Region_L1.
      * intro Hin. apply H. eapply remove_first_subset; exact Hin.
      * exact H0.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H1].
      * (* Strict-predicate migration: [Hfree] is uniformly the body's
           strict-freedom (no conditional to discharge). Still need
           [simpl in IHHt] to unfold [remove_first rr (r :: R)] into
           [r :: remove_first rr R] via the [rr <> r] guard. *)
        specialize (IHHt rr Hfree).
        simpl in IHHt.
        destruct (String.eqb rr r) eqn:Heq2.
        -- exfalso. apply String.eqb_eq in Heq2. apply Heq. exact Heq2.
        -- exact IHHt.
  - (* T_Region_Active_L1: ERegion r e (r currently active). *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed; Hfree True. RESIDUAL — structural
         list-vs-multiset mismatch documented in PROOF-NEEDS.md §2
         and in the design-note comment above this lemma block.
         Bridging requires either:
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
      eapply T_Region_Active_L1.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H].
      * exact H0.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H1].
      * eapply IHHt. exact Hfree.
  - (* T_Region_L1_Echo — structurally identical to T_Region_L1
       modulo the output-type [TEcho T] vs [T]. Both subcases close
       directly (shadowed via count-monotonicity vacuity, descend
       via remove_first/remove_first_L1 commutation). Closed in
       slice 4 to honor the "no parallel-rule admit-debt" seam-audit
       directive — the original T_Region_L1 case has zero admits,
       so its mirror has zero admits too. *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed. *)
      apply String.eqb_eq in Heq. subst r.
      rewrite (remove_first_not_in_id _ _ H).
      destruct (in_dec string_dec rr (remove_first_L1 rr R_body)) as [Hin | Hnotin].
      * (* Multiple rr's in R_body — VACUOUS by count monotonicity. *)
        exfalso.
        pose proof (count_occ_le_l1_m _ _ _ _ _ _ _ Ht rr) as Hle.
        unfold cnt in Hle. simpl in Hle.
        destruct (string_dec rr rr) as [_|Hbad]; [|apply Hbad; reflexivity].
        apply (count_occ_In string_dec) in Hin.
        pose proof (remove_first_L1_count_eq_self rr R_body) as Hself.
        unfold cnt in Hself. rewrite Hself in Hin.
        apply (count_occ_not_In string_dec) in H.
        lia.
      * (* At most one rr in R_body. *)
        rewrite (remove_first_not_in_id _ _ Hnotin).
        eapply T_Region_L1_Echo; eauto.
    + (* rr <> r: descend. *)
      apply String.eqb_neq in Heq.
      assert (Hgoal_eq : remove_first rr (remove_first_L1 r R_body) =
                        remove_first_L1 r (remove_first rr R_body)).
      { rewrite (remove_first_eq_l1 r R_body).
        rewrite (remove_first_eq_l1 r (remove_first rr R_body)).
        apply remove_first_comm. }
      rewrite Hgoal_eq.
      eapply T_Region_L1_Echo.
      * intro Hin. apply H. eapply remove_first_subset; exact Hin.
      * exact H0.
      * apply remove_first_preserves_other; [intro Hbad; apply Heq; exact Hbad | exact H1].
      * (* Strict-predicate migration: same as T_Region_L1 above —
           [simpl in IHHt] still needed to unfold [remove_first]. *)
        specialize (IHHt rr Hfree).
        simpl in IHHt.
        destruct (String.eqb rr r) eqn:Heq2.
        -- exfalso. apply String.eqb_eq in Heq2. apply Heq. exact Heq2.
        -- exact IHHt.
  - (* T_Region_Active_L1_Echo — parallels T_Region_Active_L1.
       The descend sub-case closes directly; the shadowed sub-case
       (rr = r) is the same list-vs-multiset structural residual as
       in T_Region_Active_L1 above. Per slice 4 seam audit: the
       shadowed sub-case admit is a TRUE MIRROR of the pre-existing
       L1 structural admit at line 553. The descend sub-case is
       closed Qed-style in slice 4 (not an admit). *)
    destruct (String.eqb rr r) eqn:Heq.
    + (* rr = r: shadowed — list-vs-multiset mirror of line 553.
         Resolution path is identical to its non-Echo counterpart:
         option (a) L1 perm lemma, (b) multiset reformulation, or
         (c) T_Region_*_L1 redesign. See line 542-552 design note. *)
      admit.
    + (* rr <> r: descend. *)
      apply String.eqb_neq in Heq.
      assert (Hgoal_eq : remove_first rr (remove_first_L1 r R_body) =
                        remove_first_L1 r (remove_first rr R_body)).
      { rewrite (remove_first_eq_l1 r R_body).
        rewrite (remove_first_eq_l1 r (remove_first rr R_body)).
        apply remove_first_comm. }
      rewrite Hgoal_eq.
      eapply T_Region_Active_L1_Echo.
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
  - (* T_Drop_L1_Echo — parallel rule; identical proof shape (output
       type is [TEcho T] instead of [TBase TUnit], otherwise the same). *)
    eapply T_Drop_L1_Echo; [exact H | eapply IHHt; auto].
  - (* T_Copy_L1 *)
    eapply T_Copy_L1; [exact H | eapply IHHt; auto].
  - (* T_Echo_L1 — region shrink under an echo value preserves the
     value structure (region-free witness implies a region-free echo). *)
    eapply T_Echo_L1.
    + exact H.
    + eapply IHHt; auto.
  - (* T_Observe_L1 — region shrink commutes with the witness sub-expression *)
    eapply T_Observe_L1. eapply IHHt; auto.
Admitted.

Lemma region_shrink_preserves_typing_l1_gen :
  forall R G e T R' G',
    has_type_l1_linear R G e T R' G' ->
    forall r,
      expr_strictly_free_of_region r e ->
      has_type_l1_linear (remove_first r R) G e T (remove_first r R') G'.
Proof.
  intros R G e T R' G' Ht r Hfree.
  apply (region_shrink_preserves_typing_l1_gen_m Linear); auto.
Qed.

Lemma region_shrink_preserves_typing_l1 :
  forall R G v T R' G' r,
    is_value v ->
    has_type_l1_linear R G v T R' G' ->
    ~ In r (free_regions T) ->
    expr_strictly_free_of_region r v ->
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

(** Length preserved by every typing rule.

    L2-β: generalised to modality-polymorphic [has_type_l1 m]. The
    length invariant is modality-independent (every constructor
    threads ctx length identically). Linear-specific callers
    continue to work via instantiation. *)
Lemma typing_preserves_length_l1 :
  forall m R G e T R' G',
    has_type_l1 m R G e T R' G' ->
    length G' = length G.
Proof.
  intros m R G e T R' G' H.
  induction H; simpl in *; try reflexivity; try lia;
    try (rewrite ctx_mark_used_length; reflexivity).
Qed.

(** Output-context lookup preserves type at the same index.

    L2-β restoration 2026-05-27: body ported from commit 56f592f.
    Generalised in subst_typing_gen_l1 PR to modality-polymorphic
    so sub-derivations at variable [m] from a polymorphic compound
    rule (e.g. T_App_L1) can be threaded through. The body is
    unchanged — every constructor's case discharges identically
    regardless of modality; the explicit bullets cover the seven
    compound cases that need IH composition. *)
Lemma typing_preserves_bindings_l1 :
  forall m R G e T R' G',
    has_type_l1 m R G e T R' G' ->
    forall i T0 u0,
      ctx_lookup G' i = Some (T0, u0) ->
      exists u1, ctx_lookup G i = Some (T0, u1).
Proof.
  intros m R G e T R' G' Htype.
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
  - (* T_Case_L1_Linear *)
    destruct (IHHtype2 (S idx) Ty uf) as [u_mid Hu_mid]; [exact Hlk|].
    eapply IHHtype1. exact Hu_mid.
  - (* T_Case_L1_Affine: same shape — branch 2 ignored; branch 1 carries through *)
    destruct (IHHtype2 (S idx) Ty uf) as [u_mid Hu_mid]; [exact Hlk|].
    eapply IHHtype1. exact Hu_mid.
  - (* T_If_L1_Linear *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
  - (* T_If_L1_Affine *)
    destruct (IHHtype2 _ _ _ Hlk) as [u_mid Hu_mid].
    eapply IHHtype1. exact Hu_mid.
Qed.

(** Unrestricted (non-linear) bindings are unchanged through typing.

    L2-β restoration 2026-05-27: body ported from commit 56f592f with
    new bullets for T_Case_L1_Affine + T_If_L1_Affine. T_Lam_L1_Affine
    auto-discharges through [try exact Hlk] (R/G unchanged at the
    rule's conclusion). *)
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
  - (* T_Case_L1_Linear *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  - (* T_Case_L1_Affine — same shape *)
    apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  - (* T_If_L1_Linear *)
    eapply IHHtype2; [exact Hnlin|]. eapply IHHtype1; eassumption.
  - (* T_If_L1_Affine *)
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
  forall m R Gin e T R' Gout k T1 u_in,
    has_type_l1 m R Gin e T R' Gout ->
    nth_error Gin k = Some (T1, u_in) ->
    exists u_out, nth_error Gout k = Some (T1, u_out).
Proof.
  intros m R Gin e T R' Gout k T1 u_in Htype Hin.
  assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype).
  assert (Hlt: k < length Gout).
  { rewrite Hlen. apply nth_error_Some. congruence. }
  destruct (nth_error Gout k) as [[T1' u']|] eqn:E.
  - destruct (typing_preserves_bindings_l1 _ _ _ _ _ _ _ Htype k T1' u') as [u1 Hu1].
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
    [k] in both input and output. R is unchanged at every rule.

    L2-β restoration 2026-05-27: generalised to modality-polymorphic
    [has_type_l1 m] mirroring [region_liveness_at_split_l1_gen]'s
    shape. The Linear-only wrapper [shift_typing_gen_l1] preserves
    the original signature for callers. Body ported from commit
    56f592f with new bullets for T_Lam_L1_Affine, T_Case_L1_Affine,
    T_If_L1_Affine — each Affine case mirrors its Linear counterpart
    since R and `insert_at` threading are modality-independent. *)
Lemma shift_typing_gen_l1_m :
  forall m R G e T R' G',
    has_type_l1 m R G e T R' G' ->
    forall k T_new,
      k <= length G ->
      has_type_l1 m R (insert_at k (T_new, false) G) (shift k 1 e) T R' (insert_at k (T_new, false) G').
Proof.
  intros m R G e T R' G' Htype.
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
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
  (* T_StringLen_L1 *)
  - eapply T_StringLen_L1. apply IHHtype. assumption.
  (* T_Let_L1 *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2. eapply T_Let_L1; eassumption.
  (* T_LetLin_L1 *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2. eapply T_LetLin_L1; eassumption.
  (* T_Lam_L1_Linear *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH. eapply T_Lam_L1_Linear. exact IH.
  (* T_Lam_L1_Affine *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH. eapply T_Lam_L1_Affine. exact IH.
  (* T_Lam_L1_Linear_Eff — side condition + body via IH on (S k) shift.
     The side condition is shift-invariant. *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH. eapply T_Lam_L1_Linear_Eff; [exact H | exact IH].
  (* T_Lam_L1_Affine_Eff — same. *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH. eapply T_Lam_L1_Affine_Eff; [exact H | exact IH].
  (* T_App_L1 *)
  - eapply T_App_L1; [apply IHHtype1; assumption|].
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
  (* T_Pair_L1 *)
  - eapply T_Pair_L1; [apply IHHtype1; assumption|].
    apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
  (* T_Fst_L1 *)
  - eapply T_Fst_L1; [apply IHHtype; assumption | assumption].
  (* T_Snd_L1 *)
  - eapply T_Snd_L1; [apply IHHtype; assumption | assumption].
  (* T_Inl_L1 *)
  - eapply T_Inl_L1. apply IHHtype. assumption.
  (* T_Inr_L1 *)
  - eapply T_Inr_L1. apply IHHtype. assumption.
  (* T_Case_L1_Linear *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    assert (IH3 := IHHtype3 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2, IH3. eapply T_Case_L1_Linear; eassumption.
  (* T_Case_L1_Affine *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    assert (IH3 := IHHtype3 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2, IH3. eapply T_Case_L1_Affine; eassumption.
  (* T_If_L1_Linear *)
  - eapply T_If_L1_Linear; [apply IHHtype1; assumption| |].
    + apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
    + apply IHHtype3. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
  (* T_If_L1_Affine *)
  - eapply T_If_L1_Affine; [apply IHHtype1; assumption| |].
    + apply IHHtype2. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
    + apply IHHtype3. assert (Hlen := typing_preserves_length_l1 _ _ _ _ _ _ _ Htype1). lia.
  (* T_Region_L1 *)
  - eapply T_Region_L1; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
  (* T_Region_Active_L1 *)
  - eapply T_Region_Active_L1; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
  (* T_Region_L1_Echo — parallel rule; identical shift discipline *)
  - eapply T_Region_L1_Echo; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
  (* T_Region_Active_L1_Echo — parallel rule *)
  - eapply T_Region_Active_L1_Echo; [exact H | exact H0 | exact H1 |]. apply IHHtype. assumption.
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
  (* T_Drop_L1_Echo — parallel rule *)
  - eapply T_Drop_L1_Echo; [exact H |]. apply IHHtype. assumption.
  (* T_Copy_L1 *)
  - eapply T_Copy_L1; [exact H |]. apply IHHtype. assumption.
  (* T_Echo_L1 — runtime echo value typing; shift commutes with the
     witness sub-expression. The is_value premise is preserved by
     [shift_preserves_value]. *)
  - eapply T_Echo_L1.
    + apply shift_preserves_value. exact H.
    + apply IHHtype. assumption.
  (* T_Observe_L1 — shift commutes with the witness sub-expression *)
  - eapply T_Observe_L1. apply IHHtype. assumption.
Qed.

(** Linear-specialised wrapper preserving the original lemma signature
    used by [preservation_l1] (Linear case). *)
Lemma shift_typing_gen_l1 :
  forall R G e T R' G',
    R; G |=L1 e : T -| R' ; G' ->
    forall k T_new,
      k <= length G ->
      R; insert_at k (T_new, false) G |=L1 shift k 1 e : T -| R'; insert_at k (T_new, false) G'.
Proof.
  intros R G e T R' G' Htype k T_new Hk.
  eapply shift_typing_gen_l1_m; eassumption.
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
    The hypothesis [In r R_inner] is the substantive premise.

    L2-β: generalised to modality-polymorphic; [T_Loc_L1] is itself
    m-polymorphic so the one-line proof is unchanged. The Linear
    wrapper preserves the original signature for call sites that
    still use the bare [|=L1] notation. *)
Lemma loc_retype_at_R_l1_m :
  forall (m : Modality) (R_inner : region_env) (G : ctx) (l : nat) (r : region_name),
    In r R_inner ->
    has_type_l1 m R_inner G (ELoc l r) (TString r) R_inner G.
Proof. intros. apply T_Loc_L1. assumption. Qed.

Lemma loc_retype_at_R_l1 :
  forall (R_inner : region_env) (G : ctx) (l : nat) (r : region_name),
    In r R_inner ->
    R_inner; G |=L1 ELoc l r : TString r -| R_inner; G.
Proof. intros. apply T_Loc_L1. assumption. Qed.

(** Ground non-linear retype across any [R → R'].

    For ground non-linear types ([TBase TUnit] / [TBase TBool] /
    [TBase TI32]) the typing derivation of a value is uniquely
    produced by [T_Unit_L1] / [T_Bool_L1] / [T_I32_L1], each of
    which is polymorphic in the region environment. The retype is
    therefore the trivial "invert and re-apply" pattern.

    Used by the Phase D slice 4 non-linear substitution-lemma
    generalisation: any β-reduction with [T1 ∈ {TBase TUnit,
    TBase TBool, TBase TI32}] feeds a substituend whose typing
    must be re-stated at sub-expression-internal region environments
    inside [ebody]. See [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md]
    Phase 1.

    Orthogonal to legacy [preservation] in [Semantics.v]: this lemma
    adds NEW infrastructure constrained to the post-redesign
    [has_type_l1] judgment carrying the modality parameter [m]. It
    does not extend or patch [Semantics.v]. *)
Lemma ground_nonlinear_retype_l1_m :
  forall (m m' : Modality) (R R' : region_env) (G G' : ctx) (v : expr) (T : ty),
    is_value v ->
    is_ground_nonlinear_ty T = true ->
    has_type_l1 m R G v T R G ->
    has_type_l1 m' R' G' v T R' G'.
Proof.
  intros m m' R R' G G' v T Hval Hgrd Ht.
  destruct Hval as
    [ | b | n
    | T0 e0 | v1 v2 Hv1 Hv2
    | T0 v0 Hv0 | T0 v0 Hv0
    | l r
    | v0 Hv0
    | T0 v0 Hv0 ];
    inversion Ht; subst; try discriminate Hgrd.
  - (* v = EUnit, T = TBase TUnit *) apply T_Unit_L1.
  - (* v = EBool b, T = TBase TBool *) apply T_Bool_L1.
  - (* v = EI32 n, T = TBase TI32 *) apply T_I32_L1.
Qed.

(** TFunEff lambda retype across [R → R'] under [R' ⊆ R_in].

    For values typed at [TFunEff T1 T2 R_in R_out], the lambda's body
    is typed at [R_in] (carried in the type, independent of the outer
    [R]). The outer [R] enters the typing rule only through the side
    condition [forall r, In r R -> In r R_in]. Re-typing at any [R']
    reduces to discharging the analogous side condition
    [forall r, In r R' -> In r R_in].

    Two value-shape × typing-rule cases survive [inversion]:
    [T_Lam_L1_Linear_Eff] and [T_Lam_L1_Affine_Eff]. Both produce
    [TFunEff …] in the conclusion; the legacy [T_Lam_L1_Linear] and
    [T_Lam_L1_Affine] rules produce [TFun …] and are discharged
    automatically by [inversion]'s constructor-conclusion equation.
    Non-lambda value shapes ([EUnit] / [EBool] / [EI32] / [EPair] /
    [EInl] / [EInr] / [ELoc] / [EBorrow] / [EEcho]) are typed at base /
    product / sum / borrow / region / echo types — all distinct from
    [TFunEff] — and discharge identically.

    The modality [m] is preserved across the retype: [T_Lam_L1_*_Eff]'s
    conclusion modality must match the body's typing modality, so
    unlike [ground_nonlinear_retype_l1_m] we cannot vary [m]. The
    context [G] is also preserved: the body is typed in [ctx_extend G T1]
    and varying outer [G] would require analogous machinery for context
    weakening that is out of scope here.

    Used by Phase D slice 4 Phase 3b (subst-lemma extension to TFunEff
    lambda substituends) — any β-reduction with [T1 = TFunEff …] feeds
    a lambda whose typing must be re-stated at sub-expression-internal
    region environments inside the substitution lemma's [ebody].

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 3.

    Orthogonal to legacy [preservation] in [Semantics.v]: this lemma
    adds NEW infrastructure constrained to the post-redesign
    [has_type_l1] judgment carrying the modality parameter [m]. It
    does not extend or patch [Semantics.v]. *)
Lemma tfuneff_lambda_retype_l1_m :
  forall (m : Modality) (R R' : region_env) (G : ctx)
         (v : expr) (T1 T2 : ty) (R_in R_out : region_env),
    is_value v ->
    has_type_l1 m R G v (TFunEff T1 T2 R_in R_out) R G ->
    (forall r, In r R' -> In r R_in) ->
    has_type_l1 m R' G v (TFunEff T1 T2 R_in R_out) R' G.
Proof.
  intros m R R' G v T1 T2 R_in R_out Hval Ht HR'.
  destruct Hval as
    [ | b | n
    | T0 e0 | v1 v2 Hv1 Hv2
    | T0 v0 Hv0 | T0 v0 Hv0
    | l r
    | v0 Hv0
    | T0 v0 Hv0 ];
    inversion Ht; subst.
  - (* v = ELam T0 e0, T_Lam_L1_Linear_Eff *)
    eapply T_Lam_L1_Linear_Eff; [exact HR' | eassumption].
  - (* v = ELam T0 e0, T_Lam_L1_Affine_Eff *)
    eapply T_Lam_L1_Affine_Eff; [exact HR' | eassumption].
Qed.

(** Ground non-linear values are closed terms — they contain no
    de Bruijn variables, so de Bruijn [shift] is the identity on them.

    Used by [subst_typing_gen_l1_m_ground_nonlinear] under term-binder
    cases (T_Let_L1, T_LetLin_L1, the four T_Lam_L1 lambda rules, and
    the two T_Case_L1 case rules), where the operational substitution
    introduces a [shift 0 1 vv] around the substituted value when
    descending through a binder. For ground non-linear [vv]
    (EUnit / EBool b / EI32 n) the shift is definitionally the
    identity; this lemma packages that observation so the rewrite can
    fire after canonical-form extraction.

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 2. *)
Lemma ground_nonlinear_value_shift_id_l1 :
  forall m R G v T c d,
    is_value v ->
    is_ground_nonlinear_ty T = true ->
    has_type_l1 m R G v T R G ->
    shift c d v = v.
Proof.
  intros m R G v T c d Hval Hgrd Ht.
  destruct Hval as
    [ | b | n
    | T0 e0 | v1 v2 Hv1 Hv2
    | T0 v0 Hv0 | T0 v0 Hv0
    | l r
    | v0 Hv0
    | T0 v0 Hv0 ];
    inversion Ht; subst; try discriminate Hgrd; reflexivity.
Qed.

(** TFunEff lambda retype lemma — Phase D slice 4 Phase 3 per
    [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md].

    A [TFunEff]-typed lambda value [ELam T0 e] is formed by either
    [T_Lam_L1_Linear_Eff] or [T_Lam_L1_Affine_Eff] (per
    [formal/TypingL1.v]). Both rules carry the side condition
    [forall r, In r R -> In r R_in] at the formation env [R], and
    type the body [e] at the BODY env [R_in] (which is part of the
    function type [TFunEff T1 T2 R_in R_out]).

    The body's typing is therefore INDEPENDENT of the outer formation
    env [R]. Re-applying the formation rule at any [R'] satisfying the
    rule's side condition [forall r, In r R' -> In r R_in] re-derives
    the lambda's typing at [R'] — the body typing carries over
    unchanged.

    Contrast with [ground_nonlinear_retype_l1_m] (Phase 1), which
    retypes EUnit / EBool / EI32 across ANY [R'] without a side
    condition (those values have no R-dependent body).

    Non-ELam value forms (EUnit, EBool, EI32, EPair, EInl, EInr, ELoc,
    EBorrow, EEcho) do not type at [TFunEff …] (their typing rules
    produce different type shapes). Inversion closes those cases via
    [discriminate] on the type-equation residue.

    For ELam at [TFunEff …], inversion of [Ht] yields one of four
    [T_Lam_L1_*] constructors. The two non-Eff constructors
    ([T_Lam_L1_Linear], [T_Lam_L1_Affine]) produce [TFun T1 T2]
    (no R_in / R_out fields), so the type-equation residue
    [TFun … = TFunEff …] discriminates. The two Eff constructors
    fire constructively, with re-application supplying the new R'
    and the supplied side condition [Hsub].

    Note on modality monomorphism: unlike
    [ground_nonlinear_retype_l1_m] (which is [m -> m']-polymorphic
    via the modality-independence of ground constructors), this
    lemma is [m]-monomorphic. A TFunEff lambda formed via
    [T_Lam_L1_Linear_Eff] (mode Linear) cannot be directly re-derived
    via [T_Lam_L1_Affine_Eff] (mode Affine) without lifting the body
    typing across the [Linear -> Affine] modality bridge (which is
    [linear_to_affine] in [TypingL2.v], but that operates on full
    derivations not under retype). Phase 3 does not require cross-mode
    retype — the Phase 4 [T_App_L2_Eff] β-case uses a single fixed [m]
    throughout. Cross-modality TFunEff retype, if ever needed, would
    layer [linear_to_affine] over this lemma.

    Orthogonal to legacy [preservation] in [Semantics.v]: this lemma
    adds NEW infrastructure constrained to the post-redesign
    [has_type_l1] judgment carrying the modality parameter [m]. It
    does not extend or patch [Semantics.v]. *)
Lemma tfuneff_lambda_retype_l1_m :
  forall (m : Modality) (R R' : region_env) (G : ctx) (v : expr)
         (T1 T2 : ty) (R_in R_out : region_env),
    is_value v ->
    (forall r, In r R' -> In r R_in) ->
    has_type_l1 m R G v (TFunEff T1 T2 R_in R_out) R G ->
    has_type_l1 m R' G v (TFunEff T1 T2 R_in R_out) R' G.
Proof.
  intros m R R' G v T1 T2 R_in R_out Hval Hsub Ht.
  destruct Hval as
    [ | b | n
    | T0 e0 | v1 v2 Hv1 Hv2
    | T0 v0 Hv0 | T0 v0 Hv0
    | l r
    | v0 Hv0
    | T0 v0 Hv0 ];
    inversion Ht; subst; try discriminate.
  - (* v = ELam T0 e0, T_Lam_L1_Linear_Eff *)
    eapply T_Lam_L1_Linear_Eff; [exact Hsub | eassumption].
  - (* v = ELam T0 e0, T_Lam_L1_Affine_Eff *)
    eapply T_Lam_L1_Affine_Eff; [exact Hsub | eassumption].
Qed.

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
  - (* T_Region_L1_Echo — same shape as T_Region_L1 (parallel rule;
       output type differs but the R-threading is identical). *)
    assert (Hne : r <> rv).
    { intro Heq. subst rv. apply H. exact Hin. }
    assert (Hin_body_in : In rv (r :: R)) by (right; exact Hin).
    pose proof (IHHt Hin_body_in) as HinRbody.
    apply (count_occ_In string_dec).
    pose proof (remove_first_L1_count_other r rv R_body Hne) as Heq.
    unfold cnt in Heq. rewrite Heq.
    apply (count_occ_In string_dec). exact HinRbody.
  - (* T_Region_Active_L1_Echo — same shape as T_Region_Active_L1
       including the structural admit in the [r = rv] sub-case. *)
    destruct (string_dec r rv) as [Heq|Hne].
    + admit.
    + pose proof (IHHt Hin) as HinRbody.
      apply (count_occ_In string_dec).
      pose proof (remove_first_L1_count_other r rv R_body Hne) as Heq.
      unfold cnt in Heq. rewrite Heq.
      apply (count_occ_In string_dec). exact HinRbody.
  (* T_Borrow_L1, T_Borrow_Val_L1: R unchanged, auto-discharged by
     [try assumption] above. *)
  - (* T_Drop_L1 *)
    apply IHHt. assumption.
  - (* T_Drop_L1_Echo *)
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
    compound rules. Closed via [region_liveness_at_split_l1_gen] +
    [loc_retype_at_R_l1_m].

    L2-β follow-up #2 (closed): m-polymorphic generalisation
    mirroring [shift_typing_gen_l1_m]. The substituted value's typing
    [Hv_type] stays at the bare [|=L1] (Linear) — callers always have
    a Linear v-typing — and is re-typed at the active modality [m]
    via [loc_retype_at_R_l1_m] at each compound-rule split point.
    The new mode-split constructors T_Lam_L1_Linear /
    T_Lam_L1_Affine, T_Case_L1_Linear / T_Case_L1_Affine,
    T_If_L1_Linear / T_If_L1_Affine each get their own bullet;
    Affine cases mirror Linear because the substitution threading is
    modality-independent (the Affine rules differ only in their
    permitted output flags, which are quantified inside the rule and
    transparent to the IH).

    The Linear wrapper [subst_typing_gen_l1] below preserves the
    original signature for [subst_preserves_typing_l1] and
    [preservation_l1]. *)
Lemma subst_typing_gen_l1_m :
  forall m R Gin e T R' Gout,
    has_type_l1 m R Gin e T R' Gout ->
    forall k T1 v u_in,
      nth_error Gin k = Some (T1, u_in) ->
      is_value v ->
      is_linear_ty T1 = true ->
      R; remove_at k Gin |=L1 v : T1 -| R; remove_at k Gin ->
      forall u_out,
        nth_error Gout k = Some (T1, u_out) ->
        has_type_l1 m R (remove_at k Gin) (subst k v e) T R' (remove_at k Gout).
Proof.
  intros m R Gin e T R' Gout Htype.
  induction Htype; intros k0 Tsub vv u_in Hk_in Hval Hlin Hv_type u_out Hk_out; simpl.

  (* T_Unit_L1, T_Bool_L1, T_I32_L1 *)
  1-3: (assert (u_out = u_in) by congruence; subst; constructor).

  (* T_Var_Lin_L1 *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + rewrite Nat.eqb_refl.
      assert (T = Tsub /\ u_in = false) by (unfold ctx_lookup in H; split; congruence).
      destruct H1 as [-> ->].
      rewrite remove_at_mark_used_self.
      (* Hv_type is at Linear; the current m may be anything. T_Loc_L1
         is m-polymorphic so we re-build via [linear_value_is_loc_l1]
         + [loc_retype_at_R_l1_m]. *)
      destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      apply loc_retype_at_R_l1_m. assumption.
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
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_StringConcat_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_StringLen_L1 *)
  - eapply T_StringLen_L1. eapply IHHtype; eassumption.

  (* T_Let_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Let_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_LetLin_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_LetLin_L1; [exact H | |].
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_Lam_L1_Linear: body's R = outer R; direct discharge via
     [T_Loc_L1] + Hregv. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Linear.
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. exact Hregv.

  (* T_Lam_L1_Affine: same structure; the flexible body-output flag [u]
     is the lambda's bound-variable use marker, orthogonal to the
     substituted variable's flag at outer position [k0]. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Affine.
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. exact Hregv.

  (* T_Lam_L1_Linear_Eff — body's R = R_in (separate from outer R), but
     the side condition [H : forall r, In r R -> In r R_in] gives
     In rv R_in from Hregv : In rv R. The body then types the
     substituted location at R_in. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Linear_Eff; [exact H |].
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. apply H. exact Hregv.

  (* T_Lam_L1_Affine_Eff — same. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Affine_Eff; [exact H |].
    destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. apply H. exact Hregv.

  (* T_App_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_App_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_Pair_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Pair_L1.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_Fst_L1 *)
  - eapply T_Fst_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Snd_L1 *)
  - eapply T_Snd_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Inl_L1 *)
  - eapply T_Inl_L1. eapply IHHtype; eassumption.

  (* T_Inr_L1 *)
  - eapply T_Inr_L1. eapply IHHtype; eassumption.

  (* T_Case_L1_Linear *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case_L1_Linear.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype3 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_Case_L1_Affine: same shape — per-branch [u1, u2] are the
     inner-bound variable's output flags, orthogonal to the
     substituted variable's flag. *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case_L1_Affine.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype3 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_If_L1_Linear *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1_Linear.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype3; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_If_L1_Affine: same shape; branches agree on output structure
     just as in the Linear case (the mode-split is on context
     consumption, not on conditional symmetry). *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1_Affine.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.
    + destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype3; try eassumption; try reflexivity.
      apply loc_retype_at_R_l1_m.
      eapply region_liveness_at_split_l1_gen; eassumption.

  (* T_Region_L1: body's R = [r :: R]; [In rv R] (from Hregv) lifts to
     [In rv (r :: R)]. Direct discharge via [T_Loc_L1] — no axiom. *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. right; exact Hregv.

  (* T_Region_Active_L1: body's R = outer R, so Hv_type re-uses unchanged. *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_Active_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.

  (* T_Region_L1_Echo — parallel rule; identical substitution shape *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_L1_Echo; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    apply loc_retype_at_R_l1_m. right; exact Hregv.

  (* T_Region_Active_L1_Echo — parallel rule *)
  - destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_Active_L1_Echo; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.

  (* T_Borrow_L1: EBorrow (EVar i) *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + simpl. rewrite Nat.eqb_refl.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence); subst T.
      assert (u_out = u_in) by congruence; subst.
      (* The substituted-in value is at Linear; re-construct
         [T_Borrow_Val_L1] using the polymorphic [T_Loc_L1] via
         [loc_retype_at_R_l1_m]. *)
      destruct (linear_value_is_loc_l1 _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply T_Borrow_Val_L1; [constructor|].
      apply loc_retype_at_R_l1_m. exact Hregv.
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

  (* T_Drop_L1_Echo — parallel rule *)
  - eapply T_Drop_L1_Echo; [exact H |]. eapply IHHtype; eassumption.

  (* T_Copy_L1 *)
  - eapply T_Copy_L1; [exact H |]. eapply IHHtype; eassumption.

  (* T_Echo_L1 — substitution under an echo value: the witness is a
     value, so [subst_preserves_value] preserves [is_value]. The
     witness's typing is preserved by the IH. *)
  - eapply T_Echo_L1.
    + apply subst_preserves_value. assumption.
    + eapply IHHtype; eassumption.

  (* T_Observe_L1 *)
  - eapply T_Observe_L1. eapply IHHtype; eassumption.
Qed.

(** Parallel substitution lemma for ground non-linear [T1].

    Phase D slice 4 Phase 2 per [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md].
    Mirrors [subst_typing_gen_l1_m] structurally; the case-internal
    reasoning differs in three places:

    - [T_Var_Lin_L1] with [i = k0]: the rule's [is_linear_ty T = true]
      premise contradicts [Hgrd : is_ground_nonlinear_ty Tsub = true]
      (since [is_ground_nonlinear_ty Tsub = true ->
      is_linear_ty Tsub = false] by inspection). Discharged via
      [exfalso].
    - [T_Var_Unr_L1] with [i = k0]: CONSTRUCTIVE here (the symmetric
      case in the linear lemma is the exfalso branch). The substituted
      value [vv] typed at [Linear] is lifted to the active modality [m]
      via [ground_nonlinear_retype_l1_m] (Phase 1).
    - Compound rules: [ground_nonlinear_retype_l1_m] replaces the
      [linear_value_is_loc_l1] + [loc_retype_at_R_l1_m] +
      [region_liveness_at_split_l1_gen] pipeline. The retype takes any
      [R'], so no liveness side-condition is required.

    Ships as a SIBLING lemma rather than folding case-split into the
    existing [subst_typing_gen_l1_m] to preserve the ~30 [Qed]
    downstreams. *)
Lemma subst_typing_gen_l1_m_ground_nonlinear :
  forall m R Gin e T R' Gout,
    has_type_l1 m R Gin e T R' Gout ->
    forall k T1 v u_in,
      nth_error Gin k = Some (T1, u_in) ->
      is_value v ->
      is_ground_nonlinear_ty T1 = true ->
      R; remove_at k Gin |=L1 v : T1 -| R; remove_at k Gin ->
      forall u_out,
        nth_error Gout k = Some (T1, u_out) ->
        has_type_l1 m R (remove_at k Gin) (subst k v e) T R' (remove_at k Gout).
Proof.
  intros m R Gin e T R' Gout Htype.
  induction Htype; intros k0 Tsub vv u_in Hk_in Hval Hgrd Hv_type u_out Hk_out; simpl.

  (* T_Unit_L1, T_Bool_L1, T_I32_L1 *)
  1-3: (assert (u_out = u_in) by congruence; subst; constructor).

  (* T_Var_Lin_L1 *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + (* i = k0: rule's [is_linear_ty T = true] contradicts
         [is_ground_nonlinear_ty Tsub = true] *)
      exfalso.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence). subst T.
      destruct Tsub as [b| | | | | | | | |]; try discriminate Hgrd.
      destruct b; try discriminate Hgrd; discriminate H0.
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
    + (* i = k0: CONSTRUCTIVE case for ground non-linear substitution.
         Rule output context equals input — no marking. *)
      rewrite Nat.eqb_refl.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence). subst T.
      assert (u_out = u_in) by congruence; subst u_out.
      eapply ground_nonlinear_retype_l1_m; eauto.
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
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_StringConcat_L1.
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_StringLen_L1 *)
  - eapply T_StringLen_L1. eapply IHHtype; eassumption.

  (* T_Let_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Let_L1.
    + eapply IHHtype1; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype2 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_LetLin_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_LetLin_L1; [exact H | |].
    + eapply IHHtype1; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype2 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_Lam_L1_Linear: body's R = outer R; ground value retypes trivially. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Linear.
    rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
    eapply (IHHtype (S k0) Tsub vv u_in);
      simpl; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_Lam_L1_Affine *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Affine.
    rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
    eapply (IHHtype (S k0) Tsub vv u_in);
      simpl; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_Lam_L1_Linear_Eff — body's R = R_in (independent of outer R);
     ground value retypes to ANY R, so no [R -> R_in] side-condition
     is needed. *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Linear_Eff; [exact H |].
    rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
    eapply (IHHtype (S k0) Tsub vv u_in);
      simpl; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_Lam_L1_Affine_Eff *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam_L1_Affine_Eff; [exact H |].
    rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
    eapply (IHHtype (S k0) Tsub vv u_in);
      simpl; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_App_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_App_L1.
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_Pair_L1 *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Pair_L1.
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_Fst_L1 *)
  - eapply T_Fst_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Snd_L1 *)
  - eapply T_Snd_L1; [eapply IHHtype; eassumption | assumption].

  (* T_Inl_L1 *)
  - eapply T_Inl_L1. eapply IHHtype; eassumption.

  (* T_Inr_L1 *)
  - eapply T_Inr_L1. eapply IHHtype; eassumption.

  (* T_Case_L1_Linear *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case_L1_Linear.
    + eapply IHHtype1; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype2 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype3 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_Case_L1_Affine *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case_L1_Affine.
    + eapply IHHtype1; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype2 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.
    + rewrite (ground_nonlinear_value_shift_id_l1 _ _ _ _ _ 0 1 Hval Hgrd Hv_type).
      eapply (IHHtype3 (S k0) Tsub vv u_mid);
        simpl; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eassumption.

  (* T_If_L1_Linear *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1_Linear.
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.
    + eapply IHHtype3; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_If_L1_Affine *)
  - destruct (output_shape_at_l1 _ _ _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_If_L1_Affine.
    + eapply IHHtype1; eassumption.
    + eapply IHHtype2; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.
    + eapply IHHtype3; try eassumption; try reflexivity.
      eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_Region_L1: body's R = [r :: R]; ground retypes trivially. *)
  - eapply T_Region_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_Region_Active_L1 *)
  - eapply T_Region_Active_L1; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.

  (* T_Region_L1_Echo *)
  - eapply T_Region_L1_Echo; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.
    eapply ground_nonlinear_retype_l1_m; eauto.

  (* T_Region_Active_L1_Echo *)
  - eapply T_Region_Active_L1_Echo; [exact H | exact H0 | exact H1 |].
    eapply IHHtype; try eassumption; try reflexivity.

  (* T_Borrow_L1: EBorrow (EVar i) *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + simpl. rewrite Nat.eqb_refl.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence); subst T.
      assert (u_out = u_in) by congruence; subst.
      eapply T_Borrow_Val_L1.
      * (* vv is a ground value, hence a value *) assumption.
      * eapply ground_nonlinear_retype_l1_m; eauto.
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

  (* T_Drop_L1_Echo *)
  - eapply T_Drop_L1_Echo; [exact H |]. eapply IHHtype; eassumption.

  (* T_Copy_L1 *)
  - eapply T_Copy_L1; [exact H |]. eapply IHHtype; eassumption.

  (* T_Echo_L1 *)
  - eapply T_Echo_L1.
    + apply subst_preserves_value. assumption.
    + eapply IHHtype; eassumption.

  (* T_Observe_L1 *)
  - eapply T_Observe_L1. eapply IHHtype; eassumption.
Qed.

(** Linear-specialised wrapper preserving the original signature for
    [subst_preserves_typing_l1] and [preservation_l1]. *)
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
  intros R Gin e T R' Gout Htype k T1 v u_in Hk_in Hval Hlin Hv_type u_out Hk_out.
  eapply subst_typing_gen_l1_m; eassumption.
Qed.

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

(** ** L3 preservation theorem (slice 4 of L3 wiring — capstone)

    Per-layer preservation theorem for the two L3-specific
    echo-emitting step rules [S_Region_Exit_Echo] and [S_Drop_Echo]
    (Semantics.v slice 3c) paired with their matching L3 typing
    rules [T_Region_Active_L1_Echo] / [T_Drop_L1_Echo] +
    [T_Echo_L1] for the result (TypingL1.v slices 2 / 3a / 3b).

    Stated as two per-case lemmas + an umbrella theorem
    [preservation_l3] which is their conjunction.

    Design constraint (PRESERVATION-DESIGN.md §6.3 +
    PROOF-NEEDS.md §2): the L3 step rules are universally
    quantified over the witness type [T] in the [EEcho T v]
    residue. The non-determinism is resolved at the typing-
    derivation level — each L3 typing rule pins [T] to its body
    type. The per-case lemmas state preservation for the
    matching (typing-rule, step-rule) pairs only; "cross-path"
    pairs (e.g. legacy [T_Region_Active_L1] + L3
    [S_Region_Exit_Echo]) are non-preserving by design and not
    well-typed at the umbrella's [TEcho T] output.

    Per CLAUDE.md owner directive 2026-05-27, slice 4:
      - introduces ZERO new [Admitted.] or [Axiom] declarations;
      - does NOT patch legacy [Semantics.v] preservation;
      - re-uses already-proved infrastructure
        ([value_R_G_preserving_l1] Qed,
         [region_shrink_preserves_typing_l1_gen_m] — admitted at
         the L1 layer for the T_Region_Active_L1 shadowed
         sub-case; cross-layer dependency annotated in
         PRESERVATION-DESIGN.md §5.1).

    Cross-layer accounting: the [region_shrink_preserves_typing_l1_gen_m]
    dependency is a pre-existing L1 structural admit (closes at
    L2-effect-typed-TFun per design doc §5.1). Slice 4 does NOT
    widen, duplicate, or open it — preservation_l3 is
    *conditionally* Qed under that pre-existing L1 obligation. *)

(** *** Case 1: [S_Region_Exit_Echo] paired with
    [T_Region_Active_L1_Echo].

    The typing premise extracts the body's typing
    [R; G |=L1[m] v : T -| R_body; G']; since [v] is a value,
    [value_R_G_preserving_l1] forces [R_body = R] and [G' = G].
    Region shrinkage then provides the post-step witness typing
    at [remove_first r R], and [T_Echo_L1] wraps it. *)

(** Strict-predicate migration (blocker 5, 2026-05-28): the
    region-shrinkage helper this lemma calls now requires
    [expr_strictly_free_of_region], so the corresponding premise
    here is also tightened. The legacy step rules
    [S_Region_Exit_Echo] in [Semantics.v] still emit the weak
    [expr_free_of_region]; bridging the step-rule premise to the
    L1 lemma precondition is a follow-up (legacy operational
    semantics — see PR description). *)
Lemma preservation_l3_region_active_echo :
  forall m R G r v T R_body G',
    (* T_Region_Active_L1_Echo premises *)
    In r R ->
    ~ In r (Typing.free_regions T) ->
    has_type_l1 m R G v T R_body G' ->
    (* S_Region_Exit_Echo premises (strict variant per blocker 5) *)
    is_value v ->
    expr_strictly_free_of_region r v ->
    (* Conclusion: post-step types at [TEcho T] *)
    has_type_l1 m (remove_first r R) G
      (EEcho T v) (TEcho T) (remove_first_L1 r R_body) G'.
Proof.
  intros m R G r v T R_body G' HinR HnotT Htbody Hv Hfree.
  (* Value-invariance: R_body = R and G' = G. *)
  pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hv Htbody)
    as [HR HG].
  subst R_body G'.
  (* Bridge [remove_first_L1] (typing-side) to [remove_first]
     (semantics-side) — both pointwise equal by
     [remove_first_eq_l1] (Qed). *)
  replace (remove_first_L1 r R) with (remove_first r R)
    by (symmetry; apply remove_first_eq_l1).
  (* Goal: (remove_first r R); G |- EEcho T v : TEcho T
                              -| (remove_first r R); G *)
  apply T_Echo_L1; [ exact Hv | ].
  (* Goal: (remove_first r R); G |- v : T
                              -| (remove_first r R); G
     This is exactly region shrinkage at [v] (free of [r]). *)
  apply (region_shrink_preserves_typing_l1_gen_m m _ _ _ _ _ _ Htbody _ Hfree).
Qed.

(** *** Case 2: [S_Drop_Echo] paired with [T_Drop_L1_Echo].

    The typing premise extracts
    [R; G |=L1[m] ELoc l r : T -| R'; G']. Since [ELoc l r] is
    a value (VLoc), value-invariance forces [R' = R] and
    [G' = G]. Then [T_Echo_L1] applies directly — no region
    shrinkage needed (step does not change [R]). *)

Lemma preservation_l3_drop_echo :
  forall m R G l r T R' G',
    (* T_Drop_L1_Echo premises *)
    is_linear_ty T = true ->
    has_type_l1 m R G (ELoc l r) T R' G' ->
    (* Conclusion: post-step types at [TEcho T] *)
    has_type_l1 m R G (EEcho T (ELoc l r)) (TEcho T) R' G'.
Proof.
  intros m R G l r T R' G' Hlin Htbody.
  pose proof (value_R_G_preserving_l1 _ _ _ _ _ _ _
                (VLoc l r) Htbody) as [HR HG].
  subst R' G'.
  apply T_Echo_L1; [ apply VLoc | exact Htbody ].
Qed.

(** *** Umbrella: [preservation_l3] is the conjunction of the
    two per-case lemmas above. Each conjunct corresponds to one
    (L3 typing rule, L3 step rule) matched pair. *)

Theorem preservation_l3 :
  (forall m R G r v T R_body G',
      In r R ->
      ~ In r (Typing.free_regions T) ->
      has_type_l1 m R G v T R_body G' ->
      is_value v ->
      expr_strictly_free_of_region r v ->
      has_type_l1 m (remove_first r R) G
        (EEcho T v) (TEcho T) (remove_first_L1 r R_body) G')
  /\
  (forall m R G l r T R' G',
      is_linear_ty T = true ->
      has_type_l1 m R G (ELoc l r) T R' G' ->
      has_type_l1 m R G (EEcho T (ELoc l r)) (TEcho T) R' G').
Proof.
  split.
  - exact preservation_l3_region_active_echo.
  - exact preservation_l3_drop_echo.
Qed.
