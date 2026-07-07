(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Counterexample — [preservation_l1] is FALSE as stated.

    (Experiment 3b of the choreographic series — the completion of
    [Counterexample_StepPop.v]. Regression witness in the tradition of
    [Counterexample.v], which did the same for the LEGACY preservation.)

    The Admitted capstone [preservation_l1] ([Semantics_L1.v]) claims:

      step (mu,R,e) (mu',R',e') ->
      has_type_l1 m R G e T R_final G' ->
      has_type_l1 m R' G e' T R_final G'.

    This file exhibits a configuration that types (in BOTH modalities),
    steps, and whose post-state is UNTYPABLE at the same indices — [Qed],
    zero axioms. Together with [Counterexample_StepPop.v]: BOTH remaining
    L1 Admitted markers were hiding falsehoods, not unfinished proofs.

    ** The witness (value-anchored — closes the StepPop file's open door)

      e = EStringConcat (ELoc 0 rv)
            (ESnd (EPair (ERegion rv (EI32 0)) (EVar 0)))
      R = [rv]        G = [(TString rv, false)]       T = TString rv

    - The LEFT operand is an [ELoc] VALUE. Its one typing rule
      [T_Loc_L1] demands [In rv R] — satisfied pre-step ([R = [rv]]).
    - The RIGHT operand evaluates [ERegion rv (EI32 0)] under
      [ESnd (EPair _ (EVar 0))]; the pair's second component supplies
      the [TString rv] the concat needs, typed by [T_Var_Lin_L1] at the
      already-popped env (no [In rv R] premise).
    - Stepping: [S_StringConcat_Step2] -> [S_Snd_Step] -> [S_Pair_Step1]
      -> [S_Region_Exit] pops the ONLY [rv]: [R' = []].
    - Post-state: the anchor [ELoc 0 rv] must retype at [R' = []], and
      [T_Loc_L1] demands [In rv []] — no derivation exists
      ([wit2_post_untypable], by double inversion).

    [Counterexample_StepPop.v] suggested a value-anchored RESTRICTION of
    step_pop "may be provable" because its refuting sibling was a
    variable. This witness closes that door: the dangling dependence
    here IS a value ([ELoc]), living one congruence away from the popped
    region. The hole is not variable-typing alone; it is that the
    snapshot judgment lets ONE operand's evaluation consume an ambient
    region a SIBLING's value-typing depends on — region-liveness-
    through-reduction, the one invariant behind all four historical L1
    admit faces (per the 2026-06 audit), now [Qed]-fatal to the capstone
    as stated.

    ** What this forces (experiment 3 verdict, completed)

    The L1 redesign closed the LEGACY counterexample ([Counterexample.v]
    still proves [bad_input_untypable_l1]: that configuration is
    REJECTED at typing). This file shows the post-L2-hybrid judgment
    still admits a configuration in the same semantic class through a
    different door. Preservation for L1 is NOT provable by more lemmas;
    it requires the judgment to carry the missing temporal invariant:

      - either typing-level: region-liveness / trace-coherence as a
        judgment input (the choreographic-foundational route — now
        provably MANDATORY, not merely preferred), per
        [L1ChoreoExperiment2.v]'s model + [L1-ELIMINATOR-FORK.md] §3-§7;
      - or rule-level: strengthen the leaves ([T_Var_*_L1], and the
        interplay of [T_Loc_L1] with sibling threading) so the witness
        is rejected at typing, and re-derive — the A'/path-3 family,
        whose earlier failure analyses should be revisited IN LIGHT OF
        this witness (the failure probes predate it).

    Direction choice is the owner's (PRESERVATION-DESIGN.md is the
    canonical place for the decision record). Fences respected: this
    file only ADDS a witness; [Semantics_L1.v] is untouched and its
    Admitted markers stand until the reformulation is ratified. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.

From Ephapax Require Import Syntax.
From Ephapax Require Import Modality.
From Ephapax Require Import Typing.
From Ephapax Require Import TypingL1.
From Ephapax Require Import Semantics.
From Ephapax Require Import Semantics_L1.

Definition rv : region_name := "rv".
Definition anchor : expr := ELoc 0 rv.
Definition popper : expr := ESnd (EPair (ERegion rv (EI32 0)) (EVar 0)).
Definition wit2 : expr := EStringConcat anchor popper.
Definition wit2_G : ctx := [(TString rv, false)].

(** Pre-state types — in BOTH modalities: both operands [TString rv],
    region env threading [rv] -> []. *)
Lemma wit2_types : forall m,
  has_type_l1 m [rv] wit2_G wit2 (TString rv) [] (ctx_mark_used wit2_G 0).
Proof.
  intro m.
  unfold wit2, anchor, popper.
  eapply T_StringConcat_L1 with (R1 := [rv]).
  - apply T_Loc_L1. simpl; auto.
  - eapply T_Snd_L1 with (T1 := TBase TI32).
    + eapply T_Pair_L1 with (R1 := remove_first_L1 rv [rv]).
      * eapply T_Region_Active_L1.
        -- simpl; auto.
        -- simpl. intro Hin. exact Hin.
        -- simpl; auto.
        -- apply T_I32_L1.
      * simpl. eapply T_Var_Lin_L1; reflexivity.
    + reflexivity.
Qed.

(** The step: concat's Step2 congruence -> snd congruence -> pair
    congruence -> region exit. [R] goes [[rv]] -> [[]]. *)
Lemma wit2_steps : forall mu,
  step (mu, [rv], wit2)
       (mem_free_region mu rv, [],
        EStringConcat anchor (ESnd (EPair (EI32 0) (EVar 0)))).
Proof.
  intro mu.
  unfold wit2, anchor, popper.
  replace ([] : region_env) with (remove_first rv [rv]).
  2: { simpl. destruct (string_dec rv rv); [reflexivity | congruence]. }
  apply S_StringConcat_Step2; [constructor|].
  apply S_Snd_Step.
  apply S_Pair_Step1.
  apply S_Region_Exit.
  - constructor.
  - simpl. left. reflexivity.
  - simpl. exact I.
Qed.

(** Post-state is UNTYPABLE at the same indices: the anchor [ELoc]'s
    only rule demands [In rv []]. *)
Lemma wit2_post_untypable :
  ~ has_type_l1 Linear [] wit2_G
      (EStringConcat anchor (ESnd (EPair (EI32 0) (EVar 0))))
      (TString rv) [] (ctx_mark_used wit2_G 0).
Proof.
  intro H.
  inversion H; subst.
  match goal with
  | Ha : has_type_l1 _ [] _ anchor _ _ _ |- _ =>
      inversion Ha; subst
  end.
  match goal with
  | Hin : In rv [] |- _ => exact Hin
  end.
Qed.

(** ** THE REFUTATION *)
Theorem preservation_l1_FALSE :
  ~ (forall m mu R e mu' R' e',
       step (mu, R, e) (mu', R', e') ->
       forall G T R_final G',
         has_type_l1 m R G e T R_final G' ->
         has_type_l1 m R' G e' T R_final G').
Proof.
  intro H.
  apply wit2_post_untypable.
  eapply (H Linear [] [rv] wit2).
  - apply wit2_steps.
  - apply wit2_types.
Qed.

Print Assumptions preservation_l1_FALSE.
