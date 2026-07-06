(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Counterexample — [step_pop_disjoint_from_type_l1] is FALSE as stated.

    (Experiment 3 of the choreographic series; regression witness in the
    tradition of [Counterexample.v] / [Counterexample_RegionShrink.v].)

    The Admitted lemma [step_pop_disjoint_from_type_l1]
    ([Semantics_L1.v]) claims:

      step (mu,R,e) (mu',R',e') ->
      has_type_l1 m R G e T R_final G' ->
      In r (free_regions T) -> In r R -> In r R'.

    This file exhibits a configuration that satisfies every premise and
    falsifies the conclusion, [Qed], zero axioms. The Admitted marker was
    therefore hiding a FALSEHOOD, not an unfinished proof — the same
    class as the removed [region_liveness_at_split_l1] (2026-06-26).
    No proof effort can close the lemma as stated; the honest move is
    reformulation (see "What this forces", below).

    ** The witness

      e  = EPair (ERegion rv (EI32 5)) (EVar 0)
      R  = [rv]              G = [(TString rv, false)]
      T  = TProd (TBase TI32) (TString rv)

    Typing ([wit_types]): the active-region rule types e1 and pops the
    ambient [rv] ([remove_first_L1 rv [rv] = []]); [T_Var_Lin_L1] then
    types [EVar 0 : TString rv] at the EMPTY region env — it has no
    [In rv R] premise. The pair's type carries [rv] via its second
    component, so [In rv (free_regions T)] holds.

    Stepping ([wit_steps]): [EI32 5] is a value, so [S_Region_Exit]
    fires under the [S_Pair_Step1] congruence, giving [R' = []].
    Conclusion demanded: [In rv []] — False.

    ** Relation to the choreographic trace model (experiment 2)

    [L1ChoreoExperiment2.v]'s congruence dichotomy proves the "third
    situation" — the stepping sibling net-closes the outer [rv] while the
    surviving sibling still USES it — is never trace-COHERENT
    ([sibling_use_keeps_region_live]). The witness is EXACTLY that third
    situation, and it TYPES. Hence ([typed_but_incoherent], below):

      has_type_l1 does NOT imply trace coherence.

    So experiment 2's wiring lemma ([wiring_obligation]) is unprovable
    for any trace extraction faithful enough to record the sibling's
    rv-dependence as a [Use]: the coherence the model needs is not a
    CONSEQUENCE of the current judgment — it is a MISSING PREMISE of it.

    ** What this forces (the experiment-3 verdict)

    The four-layer architecture's standing rule says: when a closure
    needs a side condition the judgment cannot supply, the architecture
    is asking for a NEW INVARIANT, not a cleverer lemma. This witness is
    that signal, now [Qed]-forced:

      - [step_pop_disjoint_from_type_l1] must be REFORMULATED with a
        liveness/coherence premise (or restricted to consumers that
        anchor the region operationally — its only caller,
        S_StringConcat_Step2, retypes an [ELoc _ r] VALUE whose
        [T_Loc_L1] typing already carried [In r R]; note the witness's
        dangling sibling is a VARIABLE, which no [S_*_Step2] case ever
        needs to retype at R', suggesting the value-anchored restriction
        may be provable);
      - the choreographic route's job description changes from "derive
        coherence from typing" (impossible — this file) to "make
        coherence a judgment-level input" — the foundational thesis,
        now with a machine-checked forcing argument.

    Owner escalation, not patching: this file only ADDS a regression
    witness. [Semantics_L1.v] is untouched; its Admitted markers stand
    until the owner ratifies a reformulation. *)

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
From Ephapax Require Import L1ChoreoExperiment2.

Definition rv : region_name := "rv".
Definition wit_e1 : expr := ERegion rv (EI32 5).
Definition wit_e2 : expr := EVar 0.
Definition wit : expr := EPair wit_e1 wit_e2.
Definition wit_G : ctx := [(TString rv, false)].
Definition wit_T : ty := TProd (TBase TI32) (TString rv).

(** The witness types under [has_type_l1] — in BOTH modalities — with
    [R = [rv]], landing at the empty region env. *)
Lemma wit_types : forall m,
  has_type_l1 m [rv] wit_G wit wit_T [] (ctx_mark_used wit_G 0).
Proof.
  intro m.
  unfold wit, wit_e1, wit_e2, wit_T.
  eapply T_Pair_L1 with (R1 := remove_first_L1 rv [rv]).
  - (* e1 = ERegion rv (EI32 5) : TBase TI32 — active-region rule,
       consumes the ambient rv. *)
    eapply T_Region_Active_L1.
    + simpl; auto.
    + simpl. intro Hin. exact Hin.
    + simpl; auto.
    + apply T_I32_L1.
  - (* e2 = EVar 0 : TString rv — at the ALREADY-EMPTY region env.
       T_Var_Lin_L1 has no In rv R premise; this is the door. *)
    simpl.
    eapply T_Var_Lin_L1.
    + reflexivity.
    + reflexivity.
Qed.

(** The witness steps: the inner region exits under the pair congruence,
    popping the only [rv]. *)
Lemma wit_steps : forall mu,
  step (mu, [rv], wit) (mem_free_region mu rv, [], EPair (EI32 5) wit_e2).
Proof.
  intro mu.
  unfold wit, wit_e1.
  replace ([] : region_env) with (remove_first rv [rv]).
  2: { simpl. destruct (string_dec rv rv); [reflexivity | congruence]. }
  apply S_Pair_Step1.
  apply S_Region_Exit.
  - constructor.
  - simpl. left. reflexivity.
  - simpl. exact I.
Qed.

(** [rv] is free in the result type (via the surviving sibling). *)
Lemma wit_free : In rv (Typing.free_regions wit_T).
Proof. simpl. auto. Qed.

(** ** THE REFUTATION *)
Theorem step_pop_disjoint_from_type_l1_FALSE :
  ~ (forall mu R e mu' R' e' m G T R_final G',
       step (mu, R, e) (mu', R', e') ->
       has_type_l1 m R G e T R_final G' ->
       forall r, In r (Typing.free_regions T) -> In r R -> In r R').
Proof.
  intro H.
  assert (Hin : In rv ([] : region_env)).
  { eapply (H [] [rv] wit (mem_free_region [] rv) [] (EPair (EI32 5) wit_e2)
             Linear wit_G wit_T [] (ctx_mark_used wit_G 0)).
    - apply wit_steps.
    - apply wit_types.
    - apply wit_free.
    - simpl; auto. }
  simpl in Hin. exact Hin.
Qed.

(** ** Tie-in to experiment 2's trace model

    The witness's faithful single-region trace is [Close; Use] from
    initial balance [cnt rv [rv] = 1]: e1's evaluation closes the
    ambient [rv]; the surviving sibling's rv-dependence is the [Use],
    ordered after it. That trace is INCOHERENT — so the configuration
    the type system just accepted is exactly one the trace model
    (correctly) rejects. Typing does not imply coherence; coherence is
    the missing invariant. *)
Example typed_but_incoherent :
  ~ valid 1 (Close :: Use :: []).
Proof.
  simpl. intros [_ [Huse _]]. inversion Huse.
Qed.

Print Assumptions step_pop_disjoint_from_type_l1_FALSE.
Print Assumptions typed_but_incoherent.
