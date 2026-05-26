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
    - [region_shrink_preserves_typing_l1] — Admitted; mirrors
      [Semantics.region_shrink_preserves_typing] under the L1
      judgment.
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
Admitted.

(** ** Helper: region-environment shrinkage for value typings.

    Mirrors [Semantics.region_shrink_preserves_typing] under the L1
    judgment. Used by the [S_Region_Exit] case of [preservation_l1].
    Detailed proof deferred to L1 follow-up PR. *)

Lemma region_shrink_preserves_typing_l1 :
  forall R G v T R' G' r,
    is_value v ->
    has_type_l1 R G v T R' G' ->
    ~ In r (free_regions T) ->
    expr_free_of_region r v ->
    has_type_l1 (remove_first r R) G v T (remove_first r R') G'.
Admitted.

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
