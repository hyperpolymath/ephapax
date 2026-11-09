(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)
(** * P2 regression families from the 2026-11-04 v2 survey (F2–F6).

    Ported unchanged from
    docs/reports/2026-11-04-v2-survey/evidence/SurveyCounterexamples.v
    (which keeps F0 and F1, the statements about the retired Props).
    Every lemma is against the CURRENT judgment ([has_type_l1], [step]),
    is Qed, and must print "Closed under the global context"
    (formal/scripts/no-false-gate.sh). These are regressions, not a
    replacement soundness theorem: v2 rung P5 restates each family against
    the v2 judgment.

    ClosedCex = F2, EchoCex = F3 + F4, PairDup = F5, EchoCopy = F6. *)

From Ephapax Require Import Syntax Typing TypingL1 Semantics Semantics_L1
  Modality Counterexample Counterexample_PreservationL1 Counterexample_StepPop.
Require Import Coq.Lists.List Coq.Strings.String. Import ListNotations.
Open Scope string_scope.

(** ** F2. preservation_l1 is false with a closed context ([G = []]).
    An un-entered same-name [ERegion] exits immediately and pops the
    ambient occurrence of [rv] that the sibling [ELoc 0 rv] needs. *)
Definition rv : region_name := "rv".

Definition closed_pre : expr :=
  EStringConcat (ELoc 0 rv) (EFst (EPair (ELoc 1 rv) (ERegion rv (EI32 0)))).
Definition closed_post : expr :=
  EStringConcat (ELoc 0 rv) (EFst (EPair (ELoc 1 rv) (EI32 0))).

Lemma closed_pre_typed :
  has_type_l1 Linear [rv] [] closed_pre (TString rv) [] [].
Proof.
  unfold closed_pre.
  eapply T_StringConcat_L1.
  - apply T_Loc_L1. simpl; auto.
  - apply (T_Fst_L1 Linear [rv] [] [] [] _ (TString rv) (TBase TI32)); [| reflexivity].
    eapply T_Pair_L1.
    + apply T_Loc_L1. simpl; auto.
    + change (@nil region_name) with (remove_first_L1 rv [rv]).
      eapply T_Region_Active_L1.
      * simpl; auto.
      * simpl; intros [].
      * simpl; auto.
      * apply T_I32_L1.
Qed.

Lemma closed_step :
  step ([], [rv], closed_pre) ([], [], closed_post).
Proof.
  unfold closed_pre, closed_post.
  apply S_StringConcat_Step2; [constructor |].
  apply S_Fst_Step.
  apply S_Pair_Step2; [constructor |].
  change (@nil region_name) with (remove_first rv [rv]).
  change (@nil mem_cell) with (mem_free_region [] rv).
  apply S_Region_Exit; [constructor | simpl; auto | simpl; auto].
Qed.

Lemma closed_post_untypable :
  forall T Rf G', ~ has_type_l1 Linear [] [] closed_post T Rf G'.
Proof.
  intros T Rf G' H. unfold closed_post in H.
  inversion H; subst.
  match goal with
  | Hl : has_type_l1 _ [] [] (ELoc 0 rv) _ _ _ |- _ => inversion Hl; subst
  end.
  match goal with Hin : In _ [] |- _ => inversion Hin end.
Qed.

Theorem preservation_l1_FALSE_closed :
  ~ (forall m mu R e mu' R' e',
       step (mu, R, e) (mu', R', e') ->
       forall G T R_final G',
         has_type_l1 m R G e T R_final G' ->
         has_type_l1 m R' G e' T R_final G').
Proof.
  intro Hp.
  eapply closed_post_untypable.
  eapply (Hp Linear [] [rv] closed_pre [] [] closed_post closed_step);
    exact closed_pre_typed.
Qed.

(** ** F3. preservation_l1 is false for a reason unrelated to regions:
    [S_Drop] and [S_Drop_Echo] both fire on the same term, so [step]
    is nondeterministic, and the echo path leaves a [T_Drop_L1]
    derivation untypable. *)
Lemma drop_typed :
  has_type_l1 Linear [rv] [] (EDrop (ELoc 0 rv)) (TBase TUnit) [rv] [].
Proof. apply (T_Drop_L1 Linear [rv] [rv] [] [] (ELoc 0 rv) (TString rv)); [reflexivity | apply T_Loc_L1; simpl; auto]. Qed.

Lemma drop_echo_step :
  step ([], [rv], EDrop (ELoc 0 rv)) ([], [rv], EEcho (TString rv) (ELoc 0 rv)).
Proof.
  change (@nil mem_cell) with (mem_write [] 0 CFree) at 2.
  apply S_Drop_Echo.
Qed.

Lemma echo_not_unit :
  forall R G Rf G' T, ~ has_type_l1 Linear R G (EEcho T (ELoc 0 rv)) (TBase TUnit) Rf G'.
Proof. intros R G Rf G' T H. inversion H. Qed.

Theorem preservation_l1_FALSE_echo_crosspath :
  ~ (forall m mu R e mu' R' e',
       step (mu, R, e) (mu', R', e') ->
       forall G T R_final G',
         has_type_l1 m R G e T R_final G' ->
         has_type_l1 m R' G e' T R_final G').
Proof.
  intro Hp.
  eapply echo_not_unit.
  eapply (Hp Linear [] [rv] _ [] [rv] _ drop_echo_step); exact drop_typed.
Qed.

(** ** F4. progress fails: [EObserve] has a typing rule but no step rule. *)
Lemma observe_typed :
  has_type_l1 Linear [] [] (EObserve (EEcho (TBase TUnit) EUnit)) (TBase TUnit) [] [].
Proof. apply (T_Observe_L1 Linear [] [] [] [] _ (TBase TUnit)). apply T_Echo_L1; [constructor | apply T_Unit_L1]. Qed.

Lemma observe_not_value : ~ is_value (EObserve (EEcho (TBase TUnit) EUnit)).
Proof. intro H; inversion H. Qed.

Lemma observe_stuck :
  forall mu c', ~ step (mu, [], EObserve (EEcho (TBase TUnit) EUnit)) c'.
Proof. intros mu c' H. inversion H. Qed.

(** ** F5. Compound linearity hole: a pair variable whose first
    component is a linear [TString] is treated as unrestricted
    ([is_linear_ty (TProd _ _) = false]), so Linear mode duplicates
    the string. *)
Lemma pair_dup_linear_string : forall r,
  has_type_l1 Linear [r] [(TProd (TString r) (TBase TI32), false)]
    (EPair (EFst (EVar 0)) (EFst (EVar 0)))
    (TProd (TString r) (TString r)) [r] [(TProd (TString r) (TBase TI32), false)].
Proof.
  intros r. eapply T_Pair_L1;
  (eapply T_Fst_L1; [eapply T_Var_Unr_L1; reflexivity | reflexivity]).
Qed.

(** ** F6. A drop-echo residue of a linear String can be copied in
    Linear mode ([is_linear_ty (TEcho _) = false]). *)
Lemma echo_copyable_linear_mode :
  forall l r R G, In r R ->
  has_type_l1 Linear R G (ECopy (EEcho (TString r) (ELoc l r)))
              (TProd (TEcho (TString r)) (TEcho (TString r))) R G.
Proof.
  intros l r R G Hin. apply T_Copy_L1; [reflexivity|].
  apply T_Echo_L1; [constructor | now apply T_Loc_L1].
Qed.

