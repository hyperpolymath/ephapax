(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Ephapax L2 — Modality-parameterised typing judgment (skeleton)

    Layer 2 of the four-layer preservation redesign
    ([PRESERVATION-DESIGN.md] §5). The L2 judgment

      [R ; G  ⊢_ℓ  e : T  -|  R' ; G']

    extends [has_type_l1] (the R-threaded judgment from [TypingL1.v])
    with a modality parameter [ℓ ∈ {Linear, Affine}]. Most typing
    rules are modality-polymorphic (rule shape identical in both
    modes); the mode-specific rules are [T_Lam], [T_Drop], and the
    branch-meet of [T_Case] / [T_If].

    ===== Scope of this skeleton =====

    Per design-doc §5 and the same "first slice" framing used for
    L3 (#166), this PR ships:

    - The [has_type_l2] inductive shape — with [L2_lift_l1] (lifts
      any L1 derivation into the L2 judgment at either mode) and
      [T_App_L2_Eff] (effect-typed application; the elimination form
      of [TFunEff] lambdas, moved out of L1 per option 5a / Phase D
      slice 3 / [PHASE-D-REDESIGN.md] slice 3 sub-sub-addendum). The
      L2_lift_l1 case is sound: per §5's preservation table,
      "[Affine derivations are L1-safe by weakening]" and Linear
      derivations are precisely the strict L1 derivations.

    - [weaken_modality] — the headline §5 lemma, Qed. In this
      skeleton the proof is a single induction; future PRs will add
      mode-specific constructors and the proof body will gain mode-
      switch cases. The Linear→Affine arrow exists as a real proof
      term from day one.

    What is NOT in this skeleton (forward-looking, separate PRs):

    - Mode-specific [T_Lam_Linear_L2] / [T_Lam_Affine_L2]
      constructors. Per §5 table, Linear's [T_Lam] requires
      [(T1, true) :: G] on body output (the bound linear variable
      MUST be consumed); Affine's [T_Lam] permits
      [(T1, true_or_unused) :: G]. The L2 Phase 2 PR adds both as
      distinct constructors and re-proves [weaken_modality] with the
      added mode switch.

    - Mode-specific [T_Drop_Linear_L2] / [T_Drop_Affine_L2]. Linear's
      [T_Drop] discharges an obligation to consume; Affine's permits
      implicit drop with an [LEcho Affine] residue produced (cross-
      layer with L3 — see [Echo.v]'s [no_section_collapse_to_residue]
      for why the residue is structurally well-defined).

    - Mode-specific branch-meet for [T_Case_Linear_L2] / [T_If_*]:
      Linear requires both branches to agree on [(R', G')] exactly;
      Affine permits a thin-poset meet on outputs.

    - Top-level closure constraint: Linear requires [G = G' = []];
      Affine requires [G = []] but [G'] may carry unused linear
      bindings.

    - The no-leak / no-duplicate / resource-exact / garbage-residue-
      inhabited proof obligations (§5 table). Each is a separate
      lemma stated against [has_type_l2 Linear] or [has_type_l2
      Affine].

    Cross-layer dependencies that block ulterior work:

    - L1's lambda-rigidity gap (§4.8 of PRESERVATION-DESIGN.md +
      Semantics_L1.v's preservation_l1 admits) is resolved at the L2
      level by introducing effect-typed [TFun] in mode-specific
      [T_Lam_*_L2]. L2 Phase 2 + L3 Phase 3 jointly close the L1
      gap. *)

Require Import Coq.Lists.List.
Import ListNotations.

From Ephapax Require Import Syntax Typing TypingL1 Modality Semantics Semantics_L1.

(** ===== The L2 judgment (skeleton) =====

    A single constructor that lifts any L1 derivation into either
    mode. Future PRs add mode-specific rules. *)

(** After L2.A (TypingL1 itself takes Modality), has_type_l2 is a
    thin wrapper that just re-indexes the L1 modality at the L2
    level. This keeps the L2 layer's distinct identity for future
    L3 (echo) and L4 (dyadic) extensions while delegating all rule
    semantics to has_type_l1. *)

Inductive has_type_l2
  : Modality ->
    region_env -> ctx -> expr -> ty -> region_env -> ctx -> Type :=
  | L2_lift_l1 :
      forall m R G e T R' G',
        TypingL1.has_type_l1 m R G e T R' G' ->
        has_type_l2 m R G e T R' G'
  (** [T_App_L2_Eff] — effect-typed application (Phase D slice 3,
      option 5a). The elimination form for [TFunEff] lambdas. Lives
      at L2 because effect-typed application is an effect-semantic
      operation (consuming [R_in / R_out] annotations meaningfully)
      and the canonical home for it is the typing-layer judgment per
      [PRESERVATION-DESIGN.md] §5.1.

      Threading: [e1] produces an effect-typed lambda value at
      ([R → R1]). [e2] evaluates the argument, threading
      [R1 → R_in] (the lambda's declared input env). The body runs
      [R_in → R_out] per the type, so the whole [EApp] consumes
      [R → R_out].

      Side condition: none at elimination. The intro side condition
      [(forall r, In r R -> In r R_in)] (T_Lam_L1_*_Eff slice 2)
      already ensures formation-time region availability; at the
      call site [e2] supplies [R_in] explicitly via its output env. *)
  | T_App_L2_Eff :
      forall m R R1 G G' G'' e1 e2 T1 T2 R_in R_out,
        has_type_l2 m R  G  e1 (TFunEff T1 T2 R_in R_out) R1   G' ->
        has_type_l2 m R1 G' e2 T1                         R_in G'' ->
        has_type_l2 m R  G  (EApp e1 e2) T2               R_out G''.

(** Notation following the Agda upstream [_;_⊢_ℓ_:_-|_;_]. *)

Reserved Notation "R ';' G '|=L2(' m ')' e ':' T '-|' R' ';' G'"
  (at level 70, G at next level, e at next level, T at next level, R' at next level).

Notation "R ';' G '|=L2(' m ')' e ':' T '-|' R' ';' G'" :=
  (has_type_l2 m R G e T R' G').

(** Convenience wrappers: an L1 derivation immediately gives an L2
    derivation at either mode. These are the entry points the L1
    consumers should use to upgrade to L2 framing. *)

Definition lift_l1_to_linear
  {R G e T R' G'}
  (H : TypingL1.has_type_l1 Linear R G e T R' G') :
  has_type_l2 Linear R G e T R' G' :=
  L2_lift_l1 Linear R G e T R' G' H.

Definition lift_l1_to_affine
  {R G e T R' G'}
  (H : TypingL1.has_type_l1 Affine R G e T R' G') :
  has_type_l2 Affine R G e T R' G' :=
  L2_lift_l1 Affine R G e T R' G' H.

(** Partial projection: extract the underlying L1 derivation from
    an L2 one when (and only when) the L2 derivation is a lift.

    Post-slice-3 (option 5a), [has_type_l2] also carries
    [T_App_L2_Eff], which has no L1 counterpart — effect-typed
    application is L2-only by design. The projection is therefore
    [option]-valued: [Some H1] for [L2_lift_l1] cases, [None] for
    the [T_App_L2_Eff] case.

    Callers that previously assumed totality (e.g. the old
    [weaken_modality] proof) must instead do structural induction
    on the L2 derivation; see [weaken_modality] below for the
    updated pattern. *)

Definition project_l2_to_l1
  {m R G e T R' G'}
  (H : has_type_l2 m R G e T R' G') :
  option (TypingL1.has_type_l1 m R G e T R' G') :=
  match H with
  | L2_lift_l1 _ _ _ _ _ _ _ H1 => Some H1
  | T_App_L2_Eff _ _ _ _ _ _ _ _ _ _ _ _ _ _ => None
  end.

(** ===== Headline §5 lemma: Linear ⇒ Affine weakening =====

    Every Linear derivation is an Affine derivation. Mirrors
    [EchoLinear.agda]'s [weaken : LEcho linear → LEcho affine] but
    at the typing-derivation layer rather than the echo layer.

    Proof: induction on the L2 derivation. In this skeleton there is
    one constructor case; future mode-specific constructors will
    introduce mode-switch cases. *)

(** Post-slice-3 (option 5a), the proof is by structural induction
    on the L2 derivation. The [L2_lift_l1] case lifts via
    [linear_to_affine]; the [T_App_L2_Eff] case weakens the two
    sub-derivations recursively and reconstructs by [T_App_L2_Eff]
    at [Affine]. *)

Theorem weaken_modality :
  forall {R G e T R' G'},
    has_type_l2 Linear R G e T R' G' ->
    has_type_l2 Affine R G e T R' G'.
Proof.
  intros R G e T R' G' H.
  remember Linear as m eqn:Hm.
  induction H as
    [ m' R0 G0 e0 T0 R0' G0' H1
    | m' R0 R1 G0 G0' G0'' e1 e2 T1 T2 R_in R_out He1 IHe1 He2 IHe2 ];
    subst m'.
  - apply lift_l1_to_affine.
    apply TypingL1.linear_to_affine.
    exact H1.
  - eapply T_App_L2_Eff.
    + apply IHe1; reflexivity.
    + apply IHe2; reflexivity.
Qed.

(** Idempotence at [Affine]: an Affine derivation re-weakened to
    Affine is the same derivation. Trivial in this skeleton; lets
    callers chain mode-weakenings without case analysis. *)

Theorem weaken_modality_affine_id :
  forall {R G e T R' G'} (H : has_type_l2 Affine R G e T R' G'),
    has_type_l2 Affine R G e T R' G'.
Proof. intros; exact H. Qed.

(** General modality weakening: dispatch on a [modality_le] proof.
    For any [m1 ⊑ m2], a derivation at [m1] gives one at [m2]. *)

Definition weaken_modality_le
  {m1 m2 : Modality} (p : modality_le m1 m2)
  {R G e T R' G'}
  (H : has_type_l2 m1 R G e T R' G') :
  has_type_l2 m2 R G e T R' G' :=
  match p in modality_le mA mB
    return has_type_l2 mA R G e T R' G' ->
           has_type_l2 mB R G e T R' G'
  with
  | Linear_le_Linear => fun h => h
  | Linear_le_Affine => fun h => weaken_modality h
  | Affine_le_Affine => fun h => h
  end H.

(** Composition law: two successive modality-weakenings agree with
    a single weakening along the composed ordering. Mirrors
    [Echo.degrade_mode_comp] one layer up.

    Trivial in this skeleton; future mode-specific rules will make
    this a real composition theorem (the Linear → Affine arrow
    becomes interesting once the modes differ on rule premises). *)

Lemma weaken_modality_le_id_linear :
  forall {R G e T R' G'} (H : has_type_l2 Linear R G e T R' G'),
    weaken_modality_le Linear_le_Linear H = H.
Proof. reflexivity. Qed.

Lemma weaken_modality_le_id_affine :
  forall {R G e T R' G'} (H : has_type_l2 Affine R G e T R' G'),
    weaken_modality_le Affine_le_Affine H = H.
Proof. reflexivity. Qed.

Lemma weaken_modality_le_strict_is_weaken_modality :
  forall {R G e T R' G'} (H : has_type_l2 Linear R G e T R' G'),
    weaken_modality_le Linear_le_Affine H = weaken_modality H.
Proof. reflexivity. Qed.

(** ===== Preservation at L2 (Phase D slice 4 — partial landing) =====

    The full statement we want:

      [Theorem preservation_l2 :
         forall m mu R e mu' R' e',
           step (mu, R, e) (mu', R', e') ->
           forall G T R_final G',
             has_type_l2 m R G e T R_final G' ->
             has_type_l2 m R' G e' T R_final G'.]

    Structural induction on the L2 derivation has two cases:

    - [L2_lift_l1] case: defer to [Semantics_L1.preservation_l1].
      Honest carry-forward of slice 4b legacy debt — [preservation_l1]
      is itself [Admitted] (lambda-rigidity gap for legacy [TFun]
      lambdas, [Semantics_L1.v:1708-1713]). This case introduces no
      new admit; it transparently surfaces the existing L1 admit
      through [Print Assumptions].

    - [T_App_L2_Eff] case: case-analysis on [step]:
      * [S_App_Step1] (e1 reduces): close via IH on e1's L2
        sub-derivation; reconstruct via [T_App_L2_Eff].
      * [S_App_Step2] (e2 reduces): close via IH on e2's L2
        sub-derivation; reconstruct via [T_App_L2_Eff].
      * [S_App_Fun] (β-reduction): the load-bearing case. After
        inverting [has_type_l2 m R G (ELam T1 ebody)
        (TFunEff T1 T2 R_in R_out) R1 G'] through [L2_lift_l1] and
        [T_Lam_L1_*_Eff], and after applying [value_R_G_preserving_l1]
        to v2 to force [R_in = R] (and [G'' = G]), the residual
        obligation is L1-substitution at index 0:

          [has_type_l1 m R G (subst 0 v2 ebody) T2 R_out G]

        from the body typing [has_type_l1 m R (T1, false)::G ebody
        T2 R_out (T1, true)::G] and the argument typing
        [has_type_l1 m R G v2 T1 R G].

        This is exactly the signature of [subst_typing_gen_l1_m]
        ([Semantics_L1.v:1358]) — EXCEPT that lemma carries an
        [is_linear_ty T1 = true] precondition that does not hold in
        general (the lambda parameter type [T1] can be [TUnit],
        [TBool], [TI32], etc. for which [is_linear_ty] returns
        [false]).

        Per CLAUDE.md owner directive 2026-05-27 §"DO escalate
        before patching", the proper response is to surface this
        as a layer-design item, not to bolt on an ad-hoc fix.

    ===== What this slice ships =====

    [preservation_l2_via_l1] — the L2_lift_l1 case in standalone
    form. Provable from [preservation_l1] without touching the
    T_App_L2_Eff case. This is the largest fragment of
    preservation_l2 that lands cleanly under the current
    substitution-lemma generality.

    ===== Next-slice infrastructure required =====

    To close the full [preservation_l2] over [has_type_l2]:

    1. **Generalize [subst_typing_gen_l1_m]** (or provide a sibling
       lemma) to handle non-linear [T1] — substitution for
       non-linear parameter types in the lambda-binding position.
       Sits in [Semantics_L1.v] but is NEW infrastructure, not
       legacy patching.

    2. **Inversion principles for [has_type_l2] on [EApp]**: a
       lemma stating that any [has_type_l2] derivation of
       [EApp e1 e2] at type [T2] decomposes into the [T_App_L2_Eff]
       premises (or [L2_lift_l1] wrapping [T_App_L1] for the
       [TFun] path). Coq's [inversion] tactic should produce this
       directly; if it gets stuck on dependent-typing constraints,
       a manual inversion lemma helps.

    3. **Inversion on [T_Lam_L1_*_Eff]** to extract the body
       typing at [R_in]. Mechanical via [inversion] on the L1
       derivation.

    Once (1) lands, (2) and (3) compose into the full
    [preservation_l2] proof body. *)

Theorem preservation_l2_via_l1 :
  forall m mu R e mu' R' e',
    step (mu, R, e) (mu', R', e') ->
    forall G T R_final G',
      TypingL1.has_type_l1 m R G e T R_final G' ->
      has_type_l2 m R' G e' T R_final G'.
Proof.
  intros m mu R e mu' R' e' Hstep G T R_final G' Ht.
  apply L2_lift_l1.
  eapply Semantics_L1.preservation_l1; eassumption.
Qed.

(** Corollary: the L2_lift_l1 case of [preservation_l2] over the
    full [has_type_l2] judgment is direct from
    [preservation_l2_via_l1] by destructuring the lift. *)

Corollary preservation_l2_lift_case :
  forall m mu R e mu' R' e',
    step (mu, R, e) (mu', R', e') ->
    forall G T R_final G' (H1 : TypingL1.has_type_l1 m R G e T R_final G'),
      has_type_l2 m R' G e' T R_final G'.
Proof.
  intros m mu R e mu' R' e' Hstep G T R_final G' H1.
  eapply preservation_l2_via_l1; eassumption.
Qed.

(** ===== Phase D slice 4 Phase 4a — β-case closure for linear T1 =====

    The [T_App_L2_Eff] β-case (S_App_Fun step) closes for linear [T1]
    via the existing m-indexed substitution lemma
    [subst_typing_gen_l1_m]. This slice ships pure new infrastructure
    orthogonal to the legacy admits; it does not patch [Semantics.v],
    [Typing.v], [Counterexample.v], or close any residual
    [Semantics_L1.v] marker.

    Structure:

    - [preservation_l2_app_eff_beta_linear_l1] — the L1-level kernel.
      Takes the inverted T_App_L2_Eff premises (a lambda formed at
      [TFunEff] + a value argument typed at [T1]) and produces the
      post-β L1 typing of [subst 0 v2 ebody]. Two structural reductions
      inside: inversion on the lambda derivation forces [T_Lam_L1_*_Eff]
      (the only formation rules producing [TFunEff] types), exposing
      the body typing at [R_in]; [value_R_G_preserving_l1] on the
      argument forces [R_in = R1 = R] and [G'' = G' = G], collapsing
      the threaded environments to a uniform [R / G] triple. Then
      [subst_typing_gen_l1_m] at [k = 0] fires with [is_linear_ty T1].

    - [preservation_l2_app_eff_beta_linear] — the L2 wrapper. Inverts
      both [has_type_l2] hypotheses through [L2_lift_l1] (the
      [T_App_L2_Eff] cases discriminate: the lambda's head is [ELam]
      not [EApp], and the argument is a value so it cannot be [EApp]),
      then defers to the L1 kernel and re-lifts via [L2_lift_l1].

    Phase 4 follow-ons (not in this PR):
    - 4b: ground-non-linear [T1] via Phase 2's
      [subst_typing_gen_l1_m_ground_nonlinear].
    - 4c: [TFunEff] non-linear [T1] — blocked on Phase 3b
      (issue #225, the substitution-lemma extension for [TFunEff]
      lambdas as substituends).
    - 4d: compound non-linear (EPair / EInl / EInr / EEcho) deferred
      to Phase 5.

    These three helpers compose with [preservation_l2_via_l1] (the
    L2_lift_l1 case) toward eventual closure of [preservation_l2]
    over the full [has_type_l2] judgment. *)

(** Auxiliary: m-polymorphic retype for linear values. Linear values
    at L1 are exactly locations (per [Semantics_L1.linear_value_is_loc_l1]),
    and [T_Loc_L1] is m-polymorphic; the value retypes at any [m']
    without further structure. Local to this file because the only
    consumer is the Affine branch of
    [preservation_l2_app_eff_beta_linear_l1] (the subst lemma's
    [|=L1] premise is Linear-mode-only). *)

Lemma linear_value_retype_l1_m :
  forall m m' R G v T,
    TypingL1.has_type_l1 m R G v T R G ->
    is_value v ->
    is_linear_ty T = true ->
    TypingL1.has_type_l1 m' R G v T R G.
Proof.
  intros m m' R G v T Htype Hval Hlin.
  destruct Hval as
    [ | b | n
    | T0 e0 | v1 v2 Hv1 Hv2
    | T0 v0 Hv0 | T0 v0 Hv0
    | l r
    | v0 Hv0
    | T0 v0 Hv0 ];
    inversion Htype; subst; try discriminate Hlin.
  apply T_Loc_L1; assumption.
Qed.

Lemma preservation_l2_app_eff_beta_linear_l1 :
  forall m R R1 G G' G'' v2 T1 T2 R_in R_out ebody,
    is_value v2 ->
    is_linear_ty T1 = true ->
    TypingL1.has_type_l1 m R  G  (ELam T1 ebody)
                                 (TFunEff T1 T2 R_in R_out) R1 G' ->
    TypingL1.has_type_l1 m R1 G' v2 T1 R_in G'' ->
    TypingL1.has_type_l1 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 T1 T2 R_in R_out ebody Hval Hlin Hlam Harg.
  inversion Hlam; subst.
  - (* T_Lam_L1_Linear_Eff: body at R_in / (T1,false)::G'' → R_out / (T1,true)::G''
       (R and G eliminated by inversion equalities; R_in and G'' remain. Use
       raw cons (not [ctx_extend]) in the [with] clause so unification of
       [remove_at 0 Gin = G''] does not stall on δ-unfolding.) *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m with
      (k := 0) (u_in := false)
      (Gin := (T1, false) :: G'')
      (Gout := (T1, true) :: G'').
    + (* body typing: H10 has [ctx_extend G'' T1] which is δ-equal to [(T1,false)::G''] *)
      unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hlin.
    + exact Harg.
    + reflexivity.
  - (* T_Lam_L1_Affine_Eff: body output is [(T1, u) :: G''] for some [u]
       introduced by inversion. The subst lemma's [|=L1] premise is
       Linear-mode-only, so Harg (Affine-typed) is re-derived at Linear
       via [linear_value_retype_l1_m]. *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m with
      (k := 0) (u_in := false)
      (Gin := (T1, false) :: G'')
      (Gout := (T1, _) :: G'').
    + unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hlin.
    + apply (linear_value_retype_l1_m Affine Linear); assumption.
    + reflexivity.
Qed.

Lemma preservation_l2_app_eff_beta_linear :
  forall m R R1 G G' G'' v2 T1 T2 R_in R_out ebody,
    is_value v2 ->
    is_linear_ty T1 = true ->
    has_type_l2 m R  G  (ELam T1 ebody)
                        (TFunEff T1 T2 R_in R_out) R1 G' ->
    has_type_l2 m R1 G' v2 T1 R_in G'' ->
    has_type_l2 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 T1 T2 R_in R_out ebody Hval Hlin Hlam Harg.
  (* Lambda inversion: [T_App_L2_Eff]'s expression is [EApp _ _],
     not [ELam _ _], so it discriminates; only [L2_lift_l1] remains. *)
  inversion Hlam as [m0 R0 G0 e0 T0 R0' G0' Hlam_l1 | ]; subst.
  (* Argument inversion: [v2] is a value, so the [T_App_L2_Eff] case
     would force [v2 = EApp _ _], contradicting [Hval]. *)
  inversion Harg as [m0' R0'' G0'' e0' T0' R0''' G0''' Harg_l1 | ]; subst.
  - apply L2_lift_l1.
    eapply preservation_l2_app_eff_beta_linear_l1; eassumption.
  - (* T_App_L2_Eff case for Harg forces v2 = EApp _ _ but Hval : is_value v2.
       [exfalso] switches to Prop so the Prop-elim of Hval (is_value : ... -> Prop)
       into the Type-sorted has_type_l2 goal is allowed. *)
    exfalso. inversion Hval.
Qed.

(** Phase D slice 4 Phase 4b — preservation_l2 β-case closure for
    ground-non-linear T1.

    Mirrors [preservation_l2_app_eff_beta_linear] (PR #228) but uses
    Phase 2's [Semantics_L1.subst_typing_gen_l1_m_ground_nonlinear]
    for the L1 substitution step. Covers T1 ∈ { TBase TUnit,
    TBase TBool, TBase TI32 } — ground values whose typing is
    R-irrelevant and modality-polymorphic, so they bridge across the
    Linear-only [|=L1] premise of the Phase 2 lemma via
    [ground_nonlinear_retype_l1_m] (Phase 1).

    Combined with PR #228's [preservation_l2_app_eff_beta_linear],
    this closes the [T_App_L2_Eff] β-case for T1 ∈ { linear,
    ground-non-linear }. Phase 4c (TFunEff T1) and Phase 4d
    (compound non-linear) remain open — see issue #225 / Phase 5
    respectively.

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 4,
    [PRESERVATION-DESIGN.md §5.1]. *)

Lemma preservation_l2_app_eff_beta_ground_nonlinear_l1 :
  forall m R R1 G G' G'' v2 T1 T2 R_in R_out ebody,
    is_value v2 ->
    is_ground_nonlinear_ty T1 = true ->
    TypingL1.has_type_l1 m R  G  (ELam T1 ebody)
                                 (TFunEff T1 T2 R_in R_out) R1 G' ->
    TypingL1.has_type_l1 m R1 G' v2 T1 R_in G'' ->
    TypingL1.has_type_l1 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 T1 T2 R_in R_out ebody Hval Hgrd Hlam Harg.
  inversion Hlam; subst.
  - (* T_Lam_L1_Linear_Eff: m = Linear; body at R_in / (T1,false)::G'' →
       R_out / (T1,true)::G''. Harg : has_type_l1 Linear R G v2 T1 R G
       (after value_R_G_preserving_l1). Matches Phase 2's [|=L1]
       premise directly. *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m_ground_nonlinear with
      (k := 0) (u_in := false)
      (Gin := (T1, false) :: G'')
      (Gout := (T1, true) :: G'').
    + unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hgrd.
    + exact Harg.
    + reflexivity.
  - (* T_Lam_L1_Affine_Eff: m = Affine; bridge Harg (Affine) to Linear
       via [ground_nonlinear_retype_l1_m] (cross-modality at same R). *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m_ground_nonlinear with
      (k := 0) (u_in := false)
      (Gin := (T1, false) :: G'')
      (Gout := (T1, _) :: G'').
    + unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hgrd.
    + eapply ground_nonlinear_retype_l1_m;
        [exact Hval | exact Hgrd | exact Harg].
    + reflexivity.
Qed.

Lemma preservation_l2_app_eff_beta_ground_nonlinear :
  forall m R R1 G G' G'' v2 T1 T2 R_in R_out ebody,
    is_value v2 ->
    is_ground_nonlinear_ty T1 = true ->
    has_type_l2 m R  G  (ELam T1 ebody)
                        (TFunEff T1 T2 R_in R_out) R1 G' ->
    has_type_l2 m R1 G' v2 T1 R_in G'' ->
    has_type_l2 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 T1 T2 R_in R_out ebody Hval Hgrd Hlam Harg.
  (* Lambda inversion: only [L2_lift_l1] survives ([T_App_L2_Eff]'s
     expression is [EApp _ _], not [ELam _ _]). *)
  inversion Hlam as [m0 R0 G0 e0 T0 R0' G0' Hlam_l1 | ]; subst.
  (* Argument inversion: [v2] is a value, so the [T_App_L2_Eff] case
     would force [v2 = EApp _ _], contradicting [Hval]. *)
  inversion Harg as [m0' R0'' G0'' e0' T0' R0''' G0''' Harg_l1 | ]; subst.
  - apply L2_lift_l1.
    eapply preservation_l2_app_eff_beta_ground_nonlinear_l1; eassumption.
  - exfalso. inversion Hval.
Qed.

(** ===== Phase D slice 4 Phase 4c (Stage 1b) — β-case closure for
    closed TFunEff substituents in leaf-only bodies ====================

    Mirrors [preservation_l2_app_eff_beta_linear] (Phase 4a, PR #228)
    and [preservation_l2_app_eff_beta_ground_nonlinear] (Phase 4b)
    but uses [Semantics_L1.subst_typing_gen_l1_m_tfuneff] (Phase 3b
    Stage 1b) for the L1 substitution step. Covers T1 = TFunEff Ta Tb
    R_in_v R_out_v — TFunEff-typed function arguments.

    Two-condition statement (per ephapax issue #239's owner-approved
    Stage 1 framing + Stage 1b's path-(i) closure precondition):

    - [tfuneff_lambda_free ebody = true] (P1): the OUTER lambda's body
      [ebody] is leaf-only with respect to TFunEff-typed lambdas.
      Stage 3 (#241) relaxes via CPS once [declared_lambda_r_ins ⊆
      R_in_v] becomes derivable from typing.

    - [(forall r, In r (regions_introduced_by ebody) -> In r R_in_v)]
      (P2): every region introduced syntactically in [ebody] is
      contained in the substituent's declared input env.
      [Counterexample_L2.v] (PR #234) mechanises the soundness gap
      this precondition rules out (fresh-region introduction
      under a stale lambda capture).

    - [expr_closed_below 0 v2 = true] (P3): the substituent is
      closed. Stage 4 (#242) replaces with a typing-derived
      closure invariant.

    The mechanised soundness-gap witnesses for the conditional form
    live in [Counterexample_L2.v] (fresh-region gap, the
    counterexample to dropping P2) and [Counterexample_L2_nested.v]
    (nested-lambda gap, the counterexample to dropping P1). The two
    files together justify why Stage 1 ships the two-condition (plus
    P3 closure) statement rather than an unconditional version —
    Stage 4 (#242) achieves the unconditional form once the L4
    annotation extension (#240) and CPS argument (#241) land.

    Combined with PRs #228 (Phase 4a, linear T1) and #233 (Phase 4b,
    ground-non-linear T1), this closes the [T_App_L2_Eff] β-case for
    T1 ∈ {linear, ground-non-linear, TFunEff}. Phase 4d (compound
    non-linear EPair / EInl / EInr / EEcho) remains open (Phase 5).

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 3b
    Stage 1b, [PRESERVATION-DESIGN.md §5.1], ephapax issue #249,
    ephapax issue #239 (parent Stage 1), [Counterexample_L2.v] +
    [Counterexample_L2_nested.v] (mechanised soundness-gap witnesses). *)

Lemma preservation_l2_app_eff_beta_tfuneff_l1 :
  forall m R R1 G G' G'' v2 Ta Tb R_in_v R_out_v T2 R_in R_out ebody,
    is_value v2 ->
    tfuneff_lambda_free ebody = true ->
    (forall r, In r (regions_introduced_by ebody) -> In r R_in_v) ->
    expr_closed_below 0 v2 = true ->
    TypingL1.has_type_l1 m R  G  (ELam (TFunEff Ta Tb R_in_v R_out_v) ebody)
                                 (TFunEff (TFunEff Ta Tb R_in_v R_out_v) T2 R_in R_out) R1 G' ->
    TypingL1.has_type_l1 m R1 G' v2 (TFunEff Ta Tb R_in_v R_out_v) R_in G'' ->
    TypingL1.has_type_l1 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 Ta Tb R_in_v R_out_v T2 R_in R_out ebody
         Hval Hflam Hreg Hclos Hlam Harg.
  inversion Hlam; subst.
  - (* T_Lam_L1_Linear_Eff: body at R_in / (Tfun, false)::G''
       → R_out / (Tfun, true)::G''. Use value_R_G_preserving on Harg
       to collapse R_in = R1 = R and G'' = G' = G. *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m_tfuneff with
      (k := 0) (u_in := false)
      (Gin := (TFunEff Ta Tb R_in_v R_out_v, false) :: G'')
      (Gout := (TFunEff Ta Tb R_in_v R_out_v, true) :: G'').
    + unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hflam.
    + exact Hreg.
    + exact Hclos.
    + exact Harg.
    + reflexivity.
  - (* T_Lam_L1_Affine_Eff: body output is [(Tfun, u) :: G''] for some [u]. *)
    destruct (value_R_G_preserving_l1 _ _ _ _ _ _ _ Hval Harg) as [<- <-].
    eapply subst_typing_gen_l1_m_tfuneff with
      (k := 0) (u_in := false)
      (Gin := (TFunEff Ta Tb R_in_v R_out_v, false) :: G'')
      (Gout := (TFunEff Ta Tb R_in_v R_out_v, _) :: G'').
    + unfold ctx_extend in *. eassumption.
    + reflexivity.
    + exact Hval.
    + exact Hflam.
    + exact Hreg.
    + exact Hclos.
    + exact Harg.
    + reflexivity.
Qed.

(** L2-judgment wrapper for [preservation_l2_app_eff_beta_tfuneff_l1].

    Inverts both [has_type_l2] hypotheses through [L2_lift_l1] (the
    [T_App_L2_Eff] cases discriminate: the lambda's head is [ELam]
    not [EApp], and the argument is a value so it cannot be [EApp]),
    then defers to the L1 kernel and re-lifts via [L2_lift_l1]. *)
Lemma preservation_l2_app_eff_beta_tfuneff :
  forall m R R1 G G' G'' v2 Ta Tb R_in_v R_out_v T2 R_in R_out ebody,
    is_value v2 ->
    tfuneff_lambda_free ebody = true ->
    (forall r, In r (regions_introduced_by ebody) -> In r R_in_v) ->
    expr_closed_below 0 v2 = true ->
    has_type_l2 m R  G  (ELam (TFunEff Ta Tb R_in_v R_out_v) ebody)
                        (TFunEff (TFunEff Ta Tb R_in_v R_out_v) T2 R_in R_out) R1 G' ->
    has_type_l2 m R1 G' v2 (TFunEff Ta Tb R_in_v R_out_v) R_in G'' ->
    has_type_l2 m R  G  (subst 0 v2 ebody) T2 R_out G''.
Proof.
  intros m R R1 G G' G'' v2 Ta Tb R_in_v R_out_v T2 R_in R_out ebody
         Hval Hflam Hreg Hclos Hlam Harg.
  inversion Hlam as [m0 R0 G0 e0 T0 R0' G0' Hlam_l1 | ]; subst.
  inversion Harg as [m0' R0'' G0'' e0' T0' R0''' G0''' Harg_l1 | ]; subst.
  - apply L2_lift_l1.
    eapply preservation_l2_app_eff_beta_tfuneff_l1; eassumption.
  - exfalso. inversion Hval.
Qed.

(* ============================================================
   Print Assumptions audit — L2 lift honest-ness seal
   ============================================================

   Closes proof-debt P10/P32 (per the PROOF-NEEDS.md inventory):
   formally certify which axioms / Admitted lemmas surface through
   each L2 β-case and the lift theorem. Without this audit, the
   "L2 lift is honest" claim in PROOF-NEEDS.md §1 ("conditional on
   preservation_l1") is unverified — `Print Assumptions` is the
   build oracle for that claim.

   Expected (per the design):

   - [preservation_l2_via_l1]  surfaces [preservation_l1] only.
     This is the canonical L1-conditional lift; no other axioms.

   - [preservation_l2_app_eff_beta_linear]  surfaces structural
     L1 admits via [subst_typing_gen_l1_m] +
     [region_shrink_preserves_typing_l1_gen_m].

   - [preservation_l2_app_eff_beta_ground_nonlinear]  surfaces
     [ground_nonlinear_retype_l1_m] + structural L1 admits.

   - [preservation_l2_app_eff_beta_tfuneff]  surfaces Phase 3b
     Stage 1b machinery + the three side conditions (P1 leaf-only,
     P2 regions ⊆ R_in_v, P3 closed-below-0) + structural L1
     admits.

   - [weaken_modality]  zero axioms.

   - [linear_to_affine] (TypingL1.v)  zero axioms.

   Verifying these mechanically means a future Qed silently
   accruing an undocumented Axiom (the historical anti-pattern
   that produced the legacy [region_liveness_at_split_l1] axiom)
   would be caught at the next [Print Assumptions] re-run.

   Build-oracle conformance: `just -f formal/Justfile all` prints
   these blocks at compile time; CI (coq-build.yml) preserves
   them in the artefacts. *)

Print Assumptions weaken_modality.
Print Assumptions preservation_l2_via_l1.
Print Assumptions linear_value_retype_l1_m.
Print Assumptions preservation_l2_app_eff_beta_linear.
Print Assumptions preservation_l2_app_eff_beta_ground_nonlinear.
Print Assumptions preservation_l2_app_eff_beta_tfuneff.
