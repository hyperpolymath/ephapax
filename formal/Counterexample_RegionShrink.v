(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  📌 PINNED REGRESSION WITNESS — region_shrink falsity          ***
  ***                                                                ***
  ***  6 Qed lemmas. Authoritative record that the NAIVE general     ***
  ***  L1 region-shrinkage statement is FALSE-as-stated.             ***
  ***                                                                ***
  ***  This file SHOULD NOT BE WEAKENED.                             ***
  *********************************************************************

  Context (2026-06-16). The former lemma

    region_shrink_preserves_typing_l1_gen_m :
      forall m R G e T R' G',
        R ; G |=L1[m] e : T -| R' ; G' ->
        forall r, expr_strictly_free_of_region r e ->
          remove_first r R ; G |=L1[m] e : T -| remove_first r R' ; G'

  was carried as an [Admitted] for the [T_Region_Active_L1] [rr = r]
  shadowed sub-case. It is not merely unproven — it is FALSE.

  Witness: [tm = ERegion "a" (ERegion "a" EUnit)] consumes TWO ambient
  copies of region ["a"] (nested [T_Region_Active_L1]), yet is
  [expr_strictly_free_of_region "a"] because that predicate descends
  through [ERegion] UNCONDITIONALLY (Syntax.v). So [tm] types at
  [["a"; "a"]] |- ... -| [[]] but does NOT type at
  [remove_first "a" ["a"; "a"] = ["a"]] — only one ambient ["a"] is
  left, and [tm] needs two. The shrunk conclusion is underivable.

  RESOLUTION (no admit, no carrier change): [Semantics_L1.v] replaces
  the false general lemma with [region_shrink_msperm], which threads a
  MULTISET-PERMUTATION hypothesis on the output env. Under that
  hypothesis the active-region case is VACUOUS (an active region
  strictly drops its r-count, so its output cannot be a multiset-perm
  of its input), and the value/neutral corollaries — which are all the
  call sites actually need — follow axiom-free. This file pins WHY the
  restriction is necessary: the unrestricted statement is refutable.

  Companion to [Counterexample.v] (legacy preservation) and
  [Counterexample_L2.v] (L2). *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From Ephapax Require Import Syntax Typing TypingL1 Semantics Modality.

Open Scope string_scope.

Definition rr : region_name := "a".
Definition R2 : region_env := rr :: rr :: nil.
Definition R1 : region_env := rr :: nil.
Definition R0 : region_env := nil.
Definition EC : ctx := nil.
Definition tm : expr := ERegion rr (ERegion rr EUnit).

(* inner region scope: R2 -> R1, closing one ambient rr *)
Lemma inner_aa :
  has_type_l1 Linear R2 EC (ERegion rr EUnit) (TBase TUnit) R1 EC.
Proof.
  change R1 with (remove_first_L1 rr R2).
  eapply T_Region_Active_L1.
  4: apply T_Unit_L1.
  - unfold R2; simpl; auto.
  - simpl; auto.
  - unfold R2; simpl; auto.
Qed.

(* whole term types at R2 -> R0, consuming BOTH ambient rr's *)
Lemma cex_types :
  has_type_l1 Linear R2 EC tm (TBase TUnit) R0 EC.
Proof.
  unfold tm.
  change R0 with (remove_first_L1 rr R1).
  eapply T_Region_Active_L1.
  4: apply inner_aa.
  - unfold R2; simpl; auto.
  - simpl; auto.
  - unfold R1; simpl; auto.
Qed.

(* ...and it is strictly free of rr (the predicate descends unconditionally) *)
Lemma cex_sfree : expr_strictly_free_of_region rr tm.
Proof. unfold tm. simpl. exact I. Qed.

(* the inner scope, at R1, is forced to output R0 *)
Lemma inner_out :
  forall m Ro G', has_type_l1 m R1 EC (ERegion rr EUnit) (TBase TUnit) Ro G' -> Ro = R0.
Proof.
  intros m Ro G' H. inversion H; subst.
  - match goal with [ HH : ~ In rr R1 |- _ ] => exfalso; apply HH; unfold R1; simpl; auto end.
  - match goal with
      [ HB : has_type_l1 _ R1 EC EUnit (TBase TUnit) _ _ |- _ ] =>
        inversion HB; subst end.
    unfold R0, R1; reflexivity.
Qed.

(* but at R1 (= remove_first rr R2) the whole term does NOT type *)
Lemma cex_not_types : ~ has_type_l1 Linear R1 EC tm (TBase TUnit) R0 EC.
Proof.
  unfold tm. intro H. inversion H; subst.
  - match goal with [ HH : ~ In rr R1 |- _ ] => apply HH; unfold R1; simpl; auto end.
  - match goal with
      [ HB : has_type_l1 _ R1 EC (ERegion rr EUnit) (TBase TUnit) ?Rb _ |- _ ] =>
        pose proof (inner_out _ _ _ HB) as Hr; subst Rb end.
    match goal with [ HI : In rr R0 |- _ ] => unfold R0 in HI; simpl in HI; exact HI end.
Qed.

(* PUNCHLINE: the naive general region_shrink statement is FALSE as stated. *)
Lemma region_shrink_is_FALSE :
  ~ (forall m R G e T R' G',
       has_type_l1 m R G e T R' G' ->
       forall r, expr_strictly_free_of_region r e ->
       has_type_l1 m (remove_first r R) G e T (remove_first r R') G').
Proof.
  intro HS.
  pose proof (HS Linear R2 EC tm (TBase TUnit) R0 EC cex_types rr cex_sfree) as Hbad.
  unfold R2, R0 in Hbad. simpl in Hbad.
  change (remove_first rr (rr :: rr :: nil)) with R1 in Hbad.
  change (remove_first rr nil) with R0 in Hbad.
  exact (cex_not_types Hbad).
Qed.
