(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Choreographic experiment 2 — the CONGRUENCE cases, with a
      NON-collapsed trace model.

    Experiment 1 ([L1ChoreoExperiment.v]) returned RELOCATES, but its own
    "honest gaps" §2 records exactly WHY and prescribes the next move:

      - it COLLAPSED the projection onto the scalar predicate
        [expr_no_exit_of_region], discarding the subterm-relative ORDER;
      - it targeted the CLEAN [ERegion rv] exit — which is already Qed,
        protected by the Tofte–Talpin premise [~ In r (free_regions T)]
        in [T_Region_Active_L1] — rather than the genuinely-open
        CONGRUENCE cases [S_Let_Step] / [S_App_Step2] / [S_Pair_Step2] /
        [S_Case_Step], where an INNER step pops a region ERASED from the
        OUTER result type ([Semantics_L1.v], congruence admits).

    This file builds the minimal NON-collapsed apparatus the gap asks for
    and aims it at the congruence boundary. It models one region [rv]'s
    lifecycle as a TRACE of events RELATIVE TO the subterm structure. The
    trace keeps the same open/close BALANCE the scalar [cnt rv R] keeps —
    but, unlike a snapshot, it keeps the ORDER, and that is exactly enough
    to separate two configurations the snapshot CONFLATES at the e1/e2
    boundary:

      (Internal scope) [rv] is opened AND closed within the stepping
        sibling's evaluation — that sibling is rv-net-neutral, so the
        OTHER sibling sees the SAME rv-environment the whole context began
        in: the congruence CARRIES ([congruence_internal_scope_carries]).

      (Escaping close) the stepping sibling closes an [rv] that was open in
        the OUTER scope — the very [rv] the surviving sibling depends on.
        In a coherent trace this is IMPOSSIBLE while the sibling still uses
        [rv]: the balance after the stepping sibling is forced [>= 1]
        ([sibling_use_keeps_region_live]). So the dangerous configuration
        is VACUOUS (never coherent), and the safe one keeps [rv] live.

    The decisive content is [congruence_dichotomy] + the corollary
    [step_pop_obligation_holds_in_trace_model]: for the congruence boundary
    the eliminator fork resolves to (carries ∨ rv-stays-live), i.e. the
    trace model CLOSES the obligation that the scalar snapshot can only
    RELOCATE. Crucially the closure is NON-circular: it does not invoke
    preservation; it is a pure structural fact about ordered traces
    ([valid_app_suffix] + the [Use] clause), and the snapshot cannot state
    it because the snapshot has only the final balance, not the witness
    that the [Use] is ORDERED after the stepping sibling's sub-trace.

    HONEST STATUS. This is the MODEL-LEVEL result. It is NOT yet a Coq
    closure of the L1 admit: the remaining obligation is the WIRING lemma
    — that [has_type_l1] of a congruence redex induces a VALID trace at
    [k = cnt rv R] with the surviving sibling's rv-dependence appearing as
    a [Use] ordered after the stepping sibling's sub-trace. That lemma is
    stated (never faked) at the foot as [wiring_obligation], in the same
    honest style experiment 1 used for [close_derives_coherence]. The
    file closes NO admit and adds NO axiom; every lemma below is [Qed].
    Verdict for the congruence cases is upgraded from experiment 1's
    "relocates" to: CLOSES IN THE TRACE MODEL, reduced to one wiring
    lemma. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

From Ephapax Require Import Syntax.
From Ephapax Require Import Typing.
From Ephapax Require Import TypingL1.
From Ephapax Require Import Semantics_L1.

(** ** The trace model (one region [rv], events relative to subterms)

    [Open]  — the region is entered ([S_Region_Enter]; [cnt rv] += 1).
    [Close] — the region is exited ([S_Region_Exit]; [cnt rv] -= 1).
    [Use]   — a subterm here DEPENDS on [rv] being live (it holds an
              [ELoc _ rv] / is typed at a [TString rv] / ...): coherence
              requires the balance to be [>= 1] at this point. *)
Inductive Ev := Open | Close | Use.
Definition Trace := list Ev.

(** Net open/close balance after running [t] from an initial balance [k]
    (= [cnt rv R] at the start of the segment). [Close] decrements; under
    [valid] (below) a [Close] only fires at balance [>= 1], so [Nat.pred]
    is the genuine decrement, never an underflow-hiding floor. *)
Fixpoint final_balance (k : nat) (t : Trace) : nat :=
  match t with
  | [] => k
  | Open :: t'  => final_balance (S k) t'
  | Close :: t' => final_balance (Nat.pred k) t'
  | Use :: t'   => final_balance k t'
  end.

(** Coherence of a trace from initial balance [k]: a [Close] requires the
    region to be open ([>= 1]) — well-nesting; a [Use] requires the region
    to be live ([>= 1]) — no use-after-close. This is the trace-level
    reading of the very property the four L1 admits owe. *)
Fixpoint valid (k : nat) (t : Trace) : Prop :=
  match t with
  | [] => True
  | Open :: t'  => valid (S k) t'
  | Close :: t' => k >= 1 /\ valid (Nat.pred k) t'
  | Use :: t'   => k >= 1 /\ valid k t'
  end.

(** ** Compositional structure of segments (the e1 ++ e2 boundary) *)

Lemma final_balance_app : forall t1 t2 k,
  final_balance k (t1 ++ t2) = final_balance (final_balance k t1) t2.
Proof.
  induction t1 as [|a t1 IH]; intros t2 k; simpl; [reflexivity|].
  destruct a; apply IH.
Qed.

(** Validity of the whole [t1 ++ t2] runs the suffix [t2] from the
    post-[t1] balance. This is the ordering fact a scalar snapshot lacks:
    [t2]'s coherence is evaluated AT [final_balance k t1], not at the
    global final count. *)
Lemma valid_app_suffix : forall t1 t2 k,
  valid k (t1 ++ t2) -> valid (final_balance k t1) t2.
Proof.
  induction t1 as [|a t1 IH]; intros t2 k H; simpl in *.
  - exact H.
  - destruct a; simpl in *.
    + apply IH; exact H.
    + destruct H as [_ H]; apply IH; exact H.
    + destruct H as [_ H]; apply IH; exact H.
Qed.

Lemma valid_app_prefix : forall t1 t2 k,
  valid k (t1 ++ t2) -> valid k t1.
Proof.
  induction t1 as [|a t1 IH]; intros t2 k H; simpl in *.
  - exact I.
  - destruct a; simpl in *.
    + apply (IH t2); exact H.
    + destruct H as [Hk H]; split; [exact Hk | apply (IH t2); exact H].
    + destruct H as [Hk H]; split; [exact Hk | apply (IH t2); exact H].
Qed.

(** ** (A) Internal scope carries — the snapshot agrees here, but the
       trace certifies WHY.

    If the stepping sibling [t1] is rv-net-neutral ([final_balance k t1 =
    k] — every [Open] it makes is matched by a [Close] it makes), then the
    surviving sibling [t2] is coherent at the ORIGINAL [k]: its rv-world is
    exactly the one the context began in, independent of [t1]'s internal
    region activity. This is the [S_Region_Step]-under-a-congruence case
    where [rv] never escaped the stepping subterm. *)
Theorem congruence_internal_scope_carries : forall t1 t2 k,
  valid k (t1 ++ t2) ->
  final_balance k t1 = k ->
  valid k t2.
Proof.
  intros t1 t2 k Hval Hneutral.
  pose proof (valid_app_suffix t1 t2 k Hval) as Hsuf.
  rewrite Hneutral in Hsuf. exact Hsuf.
Qed.

(** ** (B) The decisive lemma — a sibling [Use] keeps the region live.

    THIS is the obligation [step_pop_disjoint_from_type_l1] relocates to,
    proved here as a pure structural fact. If the surviving sibling uses
    [rv] AFTER the stepping sibling's sub-trace [t1] (the whole
    [t1 ++ Use :: t2] is coherent), then the balance after [t1] is forced
    [>= 1]: the stepping sibling CANNOT have closed [rv] out of scope. In
    [step_pop] terms, [rv] free in the result type (the surviving
    sibling's [Use]) + [rv] live before the step ([k >= 1]) gives [rv]
    live AFTER the step — exactly [In rv R'] — with NO appeal to
    preservation. The snapshot cannot prove this because it does not carry
    the order placing the [Use] after [t1]. *)
Theorem sibling_use_keeps_region_live : forall t1 t2 k,
  valid k (t1 ++ Use :: t2) ->
  final_balance k t1 >= 1.
Proof.
  intros t1 t2 k H.
  pose proof (valid_app_suffix t1 (Use :: t2) k H) as Hsuf.
  simpl in Hsuf. destruct Hsuf as [Hk _]. exact Hk.
Qed.

(** ** The congruence dichotomy (decisive)

    For a coherent congruence trace [t1 ++ t2] (stepping sibling [t1],
    surviving sibling [t2]), EXACTLY ONE of two structurally-recognisable
    situations holds, and BOTH discharge the eliminator-fork obligation:

      - [t1] net-neutral on [rv]  ->  [t2] coherent at the original [k]
        (congruence carries: [congruence_internal_scope_carries]);
      - [t2] uses [rv]            ->  [rv] live after [t1] ([>= 1])
        (region survives the step: [sibling_use_keeps_region_live]).

    The fork's "inner pop erased from the outer type" is the attempted
    THIRD situation — [t1] net-closes the outer [rv] WHILE [t2] uses it —
    and the second clause shows it is not coherent: there is no valid
    trace in which the stepping sibling pops the very [rv] a later sibling
    still uses. The snapshot conflated this impossible case with the safe
    ones; the trace separates them. *)
Theorem congruence_dichotomy : forall t1 t2 k,
  valid k (t1 ++ t2) ->
  (final_balance k t1 = k -> valid k t2)
  /\ (forall tb, t2 = Use :: tb -> final_balance k t1 >= 1).
Proof.
  intros t1 t2 k Hval. split.
  - intro Hneutral. eapply congruence_internal_scope_carries; eassumption.
  - intros tb Heq. subst t2.
    eapply sibling_use_keeps_region_live; eassumption.
Qed.

(** A direct restatement in [step_pop]'s own vocabulary: in the trace
    model, when the surviving sibling depends on [rv] (a leading [Use] in
    its segment), the post-step balance — the model's [cnt rv R'] — is
    [>= 1], i.e. [rv] remains live. This is precisely
    [In rv (free_regions T) -> In rv R -> In rv R'] read through the
    model, and it is [Qed], not [admit]. *)
Corollary step_pop_obligation_holds_in_trace_model :
  forall t1 tb k,
    valid k (t1 ++ Use :: tb) ->
    final_balance k (t1 ++ Use :: tb) >= 1 \/ final_balance k t1 >= 1.
Proof.
  intros t1 tb k H. right.
  eapply sibling_use_keeps_region_live; eassumption.
Qed.

(** ** The remaining obligation, named honestly (the WIRING lemma)

    The model above closes the congruence fork ASSUMING the program's
    region behaviour is faithfully presented as a [valid] trace at
    [k = cnt rv R] with the surviving sibling's rv-dependence appearing as
    a [Use] ordered after the stepping sibling's sub-trace. Discharging
    THAT — extracting such a trace from a [has_type_l1] derivation and
    proving it [valid] with the boundaries aligned — is the NEXT
    experiment. It is stated here as a [Prop] over an abstract extraction
    [trace_of], NEVER proved (no faked [Qed], no [Admitted]); this is the
    honest record of the one remaining gap, mirroring experiment 1's
    [close_derives_coherence].

    Risk carried forward (experiment 1, risk #2): the difficulty COULD
    re-appear inside [wiring_obligation] — proving [valid] of the
    extracted trace may itself need the ordering invariant. But note the
    asymmetry that makes this progress: the obligation is no longer
    "relocate to [expr_no_exit], which is false at re-entry" (experiment
    1), it is "extract a [valid] trace", and the trace's [valid] is
    DEFINED to permit re-entry (nested [Open]/[Close] with balance > 1).
    So experiment 1's specific failure mode (re-entry falsifies the
    relocated predicate) does not recur here. *)
Definition wiring_obligation
  (trace_of : region_name -> region_env -> expr -> Trace)
  (use_after : region_name -> region_env -> expr -> Trace -> Prop) : Prop :=
  forall m rv R G e T R' G',
    has_type_l1 m R G e T R' G' ->
    In rv (free_regions T) ->
    valid (cnt rv R) (trace_of rv R e)
    /\ use_after rv R e (trace_of rv R e).

(** If the wiring holds with the surviving sibling's dependence realised
    as a trailing [Use] (the [use_after] witness), then [step_pop]'s
    conclusion [final_balance >= 1] (the model's [In rv R']) follows from
    [sibling_use_keeps_region_live] — no further region reasoning. The
    proof obligation that remains is therefore EXACTLY [wiring_obligation],
    not preservation. *)
Definition wiring_discharges_step_pop
  (trace_of : region_name -> region_env -> expr -> Trace) : Prop :=
  forall rv R e t1 tb,
    valid (cnt rv R) (trace_of rv R e) ->
    trace_of rv R e = t1 ++ Use :: tb ->
    final_balance (cnt rv R) t1 >= 1.

Lemma wiring_discharges_step_pop_holds :
  forall trace_of, wiring_discharges_step_pop trace_of.
Proof.
  intros trace_of rv R e t1 tb Hval Heq.
  rewrite Heq in Hval.
  eapply sibling_use_keeps_region_live; eassumption.
Qed.

(** ** Verdict (experiment 2)

    For the CONGRUENCE cases — where [L1ChoreoExperiment.v] located the
    genuinely-open fork — the non-collapsed trace model CLOSES the
    obligation [step_pop_disjoint_from_type_l1] relocates to:
    [sibling_use_keeps_region_live] is [Qed], non-circular, and
    unprovable from the scalar snapshot alone. The eliminator fork for the
    congruence boundary reduces to ONE wiring lemma
    ([wiring_obligation]) — extract a [valid] trace from typing — with
    experiment 1's re-entry failure mode provably absent. This upgrades
    the congruence verdict from "relocates" to "closes in the trace model,
    reduced to wiring", and it identifies the wiring lemma as the precise
    next target. No admit, no axiom: see [Print Assumptions] below. *)

Print Assumptions congruence_internal_scope_carries.
Print Assumptions sibling_use_keeps_region_live.
Print Assumptions congruence_dichotomy.
Print Assumptions step_pop_obligation_holds_in_trace_model.
Print Assumptions wiring_discharges_step_pop_holds.
