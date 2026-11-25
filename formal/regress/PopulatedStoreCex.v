(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)
(** * M0 / P2: ClosedCex with a populated store.

    The pinned ClosedCex in SurveyFamilies uses an empty store. This
    independent extension uses two allocated, distinct locations in the
    live region. The same reduction frees both cells and leaves both
    references in the residual expression. It is a regression against the
    current L1 judgment and legacy step, not a v2 soundness claim.

    The initial memory reads are valid; we do not claim a source-to-runtime
    reachability theorem or a general configuration well-formedness
    judgment for this historical calculus. *)

From Ephapax Require Import Syntax Typing TypingL1 Semantics Modality.
From Ephapax.regress Require Import SurveyFamilies.
Require Import Coq.Lists.List Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition populated_pre_store : mem :=
  [CString SurveyFamilies.rv "left"; CString SurveyFamilies.rv "right"].

Definition populated_post_store : mem := [CFree; CFree].

Lemma populated_reads_before :
  mem_read populated_pre_store 0 = Some (CString SurveyFamilies.rv "left") /\
  mem_read populated_pre_store 1 = Some (CString SurveyFamilies.rv "right").
Proof. split; reflexivity. Qed.

Lemma populated_step :
  step (populated_pre_store, [SurveyFamilies.rv], SurveyFamilies.closed_pre)
       (populated_post_store, [], SurveyFamilies.closed_post).
Proof.
  unfold SurveyFamilies.closed_pre, SurveyFamilies.closed_post.
  apply S_StringConcat_Step2; [constructor |].
  apply S_Fst_Step.
  apply S_Pair_Step2; [constructor |].
  change (@nil region_name) with
    (remove_first SurveyFamilies.rv [SurveyFamilies.rv]).
  change populated_post_store with
    (mem_free_region populated_pre_store SurveyFamilies.rv).
  apply S_Region_Exit; [constructor | simpl; auto | simpl; auto].
Qed.

Lemma populated_reads_after :
  mem_read populated_post_store 0 = Some CFree /\
  mem_read populated_post_store 1 = Some CFree.
Proof. split; reflexivity. Qed.

(** The exact regression obligation: live, readable cells initially;
    a typed closed-context input; one step that invalidates both cells;
    and no L1 post-typing at any result type or output indices. *)
Theorem populated_store_counterexample :
  (mem_read populated_pre_store 0 = Some (CString SurveyFamilies.rv "left") /\
   mem_read populated_pre_store 1 = Some (CString SurveyFamilies.rv "right")) /\
  has_type_l1 Linear [SurveyFamilies.rv] [] SurveyFamilies.closed_pre
              (TString SurveyFamilies.rv) [] [] /\
  step (populated_pre_store, [SurveyFamilies.rv], SurveyFamilies.closed_pre)
       (populated_post_store, [], SurveyFamilies.closed_post) /\
  (mem_read populated_post_store 0 = Some CFree /\
   mem_read populated_post_store 1 = Some CFree) /\
  (forall T Rf G', ~ has_type_l1 Linear [] [] SurveyFamilies.closed_post T Rf G').
Proof.
  exact (conj populated_reads_before
         (conj SurveyFamilies.closed_pre_typed
         (conj populated_step
         (conj populated_reads_after SurveyFamilies.closed_post_untypable)))).
Qed.
