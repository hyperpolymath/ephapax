(* SPDX-License-Identifier: PMPL-1.0-or-later *)
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

From Ephapax Require Import Syntax Typing TypingL1 Modality.

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
