(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Deciding experiment: does subject reduction carry region-liveness
      through a region exit, or does it RELOCATE the obligation into a
      projection-coherence side condition?

    This is the minimal, machine-checked record of the experiment the
    eliminator-fork analysis flags as "cheap, do first"
    ([formal/L1-ELIMINATOR-FORK.md] §5/§6): model the lifecycle of one
    region [rv] as a two-segment choreography

        Gx ::= open[rv] . use[rv](j) . close[rv] . end

    and ask whether subject reduction at the [close[rv]] boundary
    DEFINITIONALLY discharges "rv live throughout the open segment", or
    whether coherence of the post-close projection becomes a fresh
    hypothesis.

    ====================================================================
    VERDICT (workflow wf_300a9737, 3-lens adversarial verify, 2026-06-16):
        RELOCATES — it does not carry coherently.
    ====================================================================

    The verdict was SHARPENED by adversarial verification into a stronger,
    more useful negative result. Two corrections to the naive framing,
    both encoded as Qed lemmas below:

    (1) [EDrop (EVar j)] is the WRONG PROBE. It reduces by [S_Drop], which
        writes the cell to [CFree] and leaves the region environment [R]
        UNCHANGED ([Semantics.v] S_Drop; [T_Drop_L1] passes [R] through).
        It NEVER fires [S_Region_Exit]. So it crosses no boundary at all,
        and is carried unconditionally — see [edrop_evar_carries_liveness].
        The [S_Region_Exit] / [close[rv]] boundary exists ONLY when an
        [ERegion rv (...)] frame wraps the term; the choreographic
        [close] action projects onto the [ERegion] frame, not onto [EDrop].

    (2) The relocated coherence side condition is, definitionally, exactly
        [expr_no_exit_of_region] ([coherence_is_no_exit], reflexivity) —
        and at the GENUINE boundary term [ERegion rv e] it is provably
        FALSE ([region_frame_breaks_no_exit]). So the relocation does not
        CLOSE the obligation; it surfaces it where it is genuinely
        unsatisfiable unless the language forbids inner re-entry. That is
        made precise — and fully proved — by
        [close_derives_coherence_needs_no_inner_exit]: the apparatus-level
        proposition [close_derives_coherence] would force that NO program
        with an inner same-region re-frame ever types with [rv] live.

    Consequence for the four open L1 admits (4 faces of ONE invariant,
    per the call-site audit at [Semantics_L1.v:2032-2052]): the
    choreographic reframe CONVERTS the four faces into one global-type
    coherence obligation (= [expr_no_exit_of_region] made foundational).
    That is genuine consolidation (4 -> 1, the right shape) but NOT
    closure (1 is not 0). Per the verifier consistency lens this is
    consistent with — and confirms — "four faces of ONE invariant".

    WHERE THE REAL FORK ACTUALLY LIVES (verifier soundness lens): NOT in
    the clean [ERegion rv] region-exit case (that case is already Qed at
    [Semantics_L1.v:3462-3493], protected by the Tofte-Talpin premise
    [~ In r (free_regions T)] in [T_Region_Active_L1]). The genuinely
    admitted hard cases are the CONGRUENCE rules [S_Let_Step] /
    [S_App_Step2] / [S_Pair_Step2] / [S_Case_Step]
    ([Semantics_L1.v:3271-3284]), where an INNER step pops a region that
    is ERASED from the OUTER result type. The corrected next experiment
    must target those, not the clean exit. See [honest gaps] at the foot.

    This file closes NO admit and adds NO axiom. It imports the existing
    Qed lemma [region_liveness_no_exit_l1_gen] and reasons only about the
    [expr_no_exit_of_region] predicate. [Print Assumptions] is clean for
    every lemma below. The legacy admits are untouched (still 4 in
    [Semantics_L1.v], 1 in [Semantics.v]). *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.

From Ephapax Require Import Syntax.
From Ephapax Require Import TypingL1.
From Ephapax Require Import Semantics_L1.

(** ** Segment skeleton (thin model)

    The two time segments of [rv]'s lifecycle. We model only what the
    experiment needs: the projection target of a sub-term is the segment
    it lives in. [Seg1_open_use] is the half-open interval during which
    [rv] is open and used; [Seg2_closed] is after the [close[rv]] event.
    No global-type / coherence judgement is built here (that is the next
    experiment, see foot) — the projection is collapsed to the existing
    scalar predicate, which is exactly the point being tested. *)
Inductive ChoreoSeg := Seg1_open_use | Seg2_closed.

Definition in_open_interval (s : ChoreoSeg) : Prop :=
  match s with Seg1_open_use => True | Seg2_closed => False end.

(** ** (1) [EDrop (EVar j)] is the wrong probe.

    Its no-exit predicate computes to [True] (the [EDrop] clause recurses
    into the [EVar] leaf, which is [True]); so the EXISTING true lemma
    carries liveness with no side condition and no admit. The term never
    crosses a region exit. *)
Lemma edrop_evar_no_exit :
  forall (rv : region_name) j, expr_no_exit_of_region rv (EDrop (EVar j)).
Proof. intros rv j. simpl. exact I. Qed.

Lemma edrop_evar_carries_liveness :
  forall m R G j rv T R' G',
    has_type_l1 m R G (EDrop (EVar j)) T R' G' ->
    In rv R -> In rv R'.
Proof.
  intros m R G j rv T R' G' Ht Hin.
  eapply region_liveness_no_exit_l1_gen.
  - exact Ht.
  - apply edrop_evar_no_exit.
  - exact Hin.
Qed.

(** ** (2) The relocated coherence side condition.

    The projection-coherence condition the [close[rv]] step would have to
    discharge is, definitionally, the honest no-exit predicate. We DEFINE
    it that way and PROVE the identity by reflexivity — no weaker
    condition is smuggled. *)
Definition projection_coherent_after_close (rv : region_name) (residual : expr) : Prop :=
  expr_no_exit_of_region rv residual.

Lemma coherence_is_no_exit :
  forall rv e, projection_coherent_after_close rv e <-> expr_no_exit_of_region rv e.
Proof. intros rv e. unfold projection_coherent_after_close. split; intro H; exact H. Qed.

(** The ONLY term that actually crosses the [close[rv]] / [S_Region_Exit]
    boundary is an [ERegion rv (...)] frame, and on that term the relocated
    coherence condition is provably FALSE ([rv <> rv] is unsatisfiable).
    So the relocation does not close the obligation — it surfaces it where
    it is false. This is the vacuity the buildability lens flagged, here
    made an explicit, sharp Qed. *)
Lemma region_frame_breaks_no_exit :
  forall rv e, ~ expr_no_exit_of_region rv (ERegion rv e).
Proof. intros rv e [Hne _]. apply Hne. reflexivity. Qed.

(** ** (3) The apparatus-level obligation, named honestly.

    [close_derives_coherence] is the proposition that the choreographic
    [close[rv]] step DERIVES projection coherence rather than ASSUMING it.
    If it held definitionally, the verdict would upgrade to "carries
    coherently". It is left as a bare [Definition] (a [Prop]), NEVER
    proved — this is the honest record of the open obligation, not a faked
    [Qed] and not an [Admitted]. *)
Definition close_derives_coherence : Prop :=
  forall m R G rv e T R' G',
    has_type_l1 m R G (ERegion rv e) T R' G' ->
    In rv R ->
    projection_coherent_after_close rv e.

(** And here is the fully-proved reason it does not hold for the real
    language: [close_derives_coherence] is INCOMPATIBLE with the existence
    of any inner same-region re-frame [ERegion rv (ERegion rv e0)] that
    types with [rv] live. I.e. relocation does not close the fork; it
    demands a language restriction (no inner re-entry of a live region) —
    which is exactly [expr_no_exit_of_region] promoted to a global
    invariant. Proved with no axiom, no concrete typing witness required. *)
Lemma close_derives_coherence_needs_no_inner_exit :
  close_derives_coherence ->
  forall m R G rv e0 T R' G',
    has_type_l1 m R G (ERegion rv (ERegion rv e0)) T R' G' ->
    In rv R ->
    False.
Proof.
  intros Hcdc m R G rv e0 T R' G' Ht Hin.
  pose proof (Hcdc m R G rv (ERegion rv e0) T R' G' Ht Hin) as Hcoh.
  unfold projection_coherent_after_close in Hcoh.
  exact (region_frame_breaks_no_exit rv e0 Hcoh).
Qed.

(** ** Honest gaps (NOT settled by this experiment)

    1. [close_derives_coherence] is left UNPROVED (and is false in general,
       per the lemma above). A "carries coherently" verdict is therefore
       unavailable for the full language.

    2. No global-type apparatus is built: no [has_type_global], no
       projection function [Gx |> e], no [coherent(Gx)] judgement and no
       [close]-reduction [Gx --close--> Gx']. The segment/projection here
       is the thin [ChoreoSeg] / [in_open_interval] skeleton plus the
       reused scalar predicate. Building that apparatus is the NEXT
       experiment, and it must be aimed at the CONGRUENCE cases
       ([S_Let_Step] / [S_App_Step2] / [S_Pair_Step2] / [S_Case_Step],
       [Semantics_L1.v:3271-3284], inner pop erased from outer type) —
       NOT the clean [ERegion rv] exit, which is already Qed.
       STARTED in [L1ChoreoExperiment2.v]: the non-collapsed trace model
       aimed at the congruence boundary CLOSES the relocated obligation
       in-model ([sibling_use_keeps_region_live], Qed, axiom-free) and
       reduces the fork to one wiring lemma. See [L1-ELIMINATOR-FORK.md] §9.

    3. The tropical/Lean side has the monotonicity backbone
       ([matStar_mono], [id_le_star], [parametric_resource_transport]) but
       NO choreography, NO time segments, NO grade vector, NO reduction
       relation and NO liveness theorem. The graded unification is
       motivated, not mechanised.

    4. This must NOT gate the clean-win deterministic carrier refactor for
       admits 1/2 ([formal/L1-REGION-REFOUNDATION-PLAN.md]); that route is
       independent of this choreographic research on admits 3/4. *)
