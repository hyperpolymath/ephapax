(* SPDX-License-Identifier: MPL-2.0 *)
(* Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Soundness gap (L2): preservation_l2 fails for nested-TFunEff
      substituends — the gap Phase 3b Stage 1's [tfuneff_lambda_free]
      precondition correctly EXCLUDES.

    Sibling artifact to [Counterexample_L2.v]. That earlier file
    witnessed the soundness gap for TFunEff substituends crossing
    a fresh-region scope ([ERegion]). This file witnesses a
    DIFFERENT gap class: TFunEff substituends placed inside an
    inner [TFunEff] lambda whose declared [R_in_inner] is too
    small to accommodate the substituent's required formation env.

    The two together justify the **two**-condition statement of
    Phase 3b Stage 1's [preservation_l2_app_eff_beta_tfuneff_l1]:

      (P1)  [tfuneff_lambda_free ebody = true]
            — rules out THIS counterexample's class (inner lambda)
      (P2)  [regions_introduced_by ebody ⊆ R_in_v]
            — rules out [Counterexample_L2.v]'s class (fresh region)

    Stage 2 (#240) lifts (P1) by carrying [R_in / R_out] on [ELam].
    Stage 3 (#241) replaces (P1) with a CPS-style proof that closes
    the inner-lambda case via a relaxed [declared_lambda_r_ins ⊆ R_in_v]
    obligation. Stage 4 (#242) reaches an unconditional preservation_l2.

    ===== Configuration =====

      T_v        := TFunEff TUnit TUnit [] []      (* substituent type, R_in_v = [] *)
      v          := ELam TUnit EUnit               (* value of type T_v *)
      inner_body := ELam TUnit (EVar 1)            (* inner lambda; body refs outer var *)
      T_inner    := TFunEff TUnit T_v [r2] [r2]    (* inner lambda's annotated type *)
      outer      := ELam T_v inner_body            (* outer lambda; param of type T_v *)
      T_outer    := TFunEff T_v T_inner [] []      (* outer type *)
      e_before   := EApp outer v                   (* well-typed via T_App_L2_Eff at R = [] *)
      e_after    := ELam TUnit v                   (* β-result: subst 0 v inner_body *)

    ===== Why this configuration witnesses the gap =====

    Pre-β [outer] is well-typed because the inner lambda's body
    [EVar 1] references the outer variable (de-Bruijn index 1
    skipping the inner binder) at type [T_v]. Per [T_Var_Unr_L1]
    on a non-linear type ([is_linear_ty T_v = false]), the reference
    types at any region env; in particular at [R_in_inner = [r2]].
    Side condition [R_in_outer ⊆ R_in_inner] passes vacuously when
    [R_in_outer = []].

    Post-β substitutes [v] for the outer variable. The inner lambda
    body becomes [shift 0 1 v = v] (closed value). So
    [e_after = ELam TUnit v]. For [e_after] to type at [T_inner],
    [v] would need to retype at [R = [r2]] via [T_Lam_L1_*_Eff],
    which requires [[r2] ⊆ R_in_v = []]. This fails on [r2 ∈ [r2]]
    vs. [r2 ∉ []].

    The structural mechanism: [tfuneff_lambda_retype_l1_m]
    (Semantics_L1.v:1257) carries the obligation [R' ⊆ R_in_v];
    inside a nested [TFunEff] lambda the [R'] is the INNER
    [R_in_inner], not the OUTER formation env — and inner [R_in]
    annotations are invisible to Phase 3b Stage 1's syntactic
    [regions_introduced_by] over-approximation. Stage 1 therefore
    refuses ebody-with-inner-lambdas via [tfuneff_lambda_free].

    ===== Three theorems =====

    - [e_before_typed]   — outer at [T_outer] via T_Lam_L1_Affine_Eff
                           cascaded with inner; full e_before via T_App_L2_Eff.
    - [e_step]           — operational [S_App_Fun] β-reduction.
    - [e_after_untypable] — no L1 derivation exists for e_after at
                            T_inner. Inversion forces [T_Lam_L1_*_Eff]
                            (only formation rule producing TFunEff);
                            both modes' side condition
                            [forall r, In r [r2] -> In r []] is
                            contradicted by [In r2 [r2]].

    ===== Owner-directive compliance =====

    - Does not modify [Semantics.v] or [Counterexample.v] (legacy
      soundness-gap artifacts).
    - Does not patch [Typing.v].
    - Does not close any residual [Semantics_L1.v] admit.
    - Adds NEW infrastructure (a new file in [formal/]) orthogonal
      to legacy admits, mirroring the precedent of [Counterexample.v]
      for the legacy preservation and [Counterexample_L2.v] for the
      fresh-region soundness-gap class.
    - No new [Axiom] or [Admitted] markers. *)

From Ephapax Require Import Syntax Typing TypingL1 Modality Semantics Semantics_L1 TypingL2.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Section CounterexampleL2Nested.

  Definition r2 : region_name := "r2".

  (** Substituent type — a TFunEff lambda with empty input region env. *)
  Definition T_v : ty :=
    TFunEff (TBase TUnit) (TBase TUnit) [] [].

  (** Substituent value — a closed [TUnit -> TUnit] lambda. *)
  Definition v : expr :=
    ELam (TBase TUnit) EUnit.

  (** Inner lambda type — annotated with [R_in = R_out = [r2]]. *)
  Definition T_inner : ty :=
    TFunEff (TBase TUnit) T_v [r2] [r2].

  (** Inner lambda body — references the outer-bound variable via
      [EVar 1] (de Bruijn index 1 skips the inner [ELam] binder). *)
  Definition inner_body : expr :=
    ELam (TBase TUnit) (EVar 1).

  (** Outer lambda — parameter of type [T_v], body is [inner_body]. *)
  Definition outer : expr :=
    ELam T_v inner_body.

  (** Outer lambda's type. *)
  Definition T_outer : ty :=
    TFunEff T_v T_inner [] [].

  Definition e_before : expr := EApp outer v.

  (** Post-β term: [subst 0 v (ELam TUnit (EVar 1))]
      = [ELam TUnit (subst 1 (shift 0 1 v) (EVar 1))]
      = [ELam TUnit (shift 0 1 v)]   (* EVar 1 substitutes to shift 0 1 v *)
      = [ELam TUnit v]                 (* v is a closed value, shift is identity on its body *) *)
  Definition e_after : expr := ELam (TBase TUnit) v.

  (** Helper: [v] types at [T_v] at any sufficiently small R. *)

  Lemma v_typed_at_empty :
    has_type_l1 Affine [] [] v T_v [] [].
  Proof.
    unfold v, T_v.
    eapply T_Lam_L1_Affine_Eff with (u := false).
    - intros r Hr; inversion Hr.
    - apply T_Unit_L1.
  Qed.

  (** Outer lambda is well-typed at [T_outer]. *)

  Lemma outer_typed :
    has_type_l1 Affine [] [] outer T_outer [] [].
  Proof.
    unfold outer, T_outer, T_inner, inner_body.
    eapply T_Lam_L1_Affine_Eff with (u := false).
    - intros r Hr; inversion Hr.
    - (* Inner lambda formation at outer body context.
         Outer body context: [ctx_extend [] T_v = (T_v, false) :: []].
         Inner lambda forms at TFunEff (TBase TUnit) T_v [r2] [r2]. *)
      eapply T_Lam_L1_Affine_Eff with (u := false).
      + intros r Hr; inversion Hr.
      + (* Body of inner: [EVar 1] at R = [r2], context =
           ctx_extend ((T_v, false) :: []) (TBase TUnit)
           = ((TBase TUnit, false) :: (T_v, false) :: []).
           [EVar 1] looks up [T_v] at index 1; output type [T_v]. *)
        eapply T_Var_Unr_L1.
        * unfold ctx_lookup. simpl. reflexivity.
        * reflexivity.
  Qed.

  (** ===== (a) e_before is well-typed via T_App_L2_Eff ===== *)

  Lemma e_before_typed :
    has_type_l2 Affine [] [] e_before T_inner [] [].
  Proof.
    unfold e_before.
    eapply T_App_L2_Eff.
    - apply L2_lift_l1. exact outer_typed.
    - apply L2_lift_l1. exact v_typed_at_empty.
  Qed.

  (** ===== (b) The β-step from e_before to e_after =====

      [subst 0 v (ELam TUnit (EVar 1))]
        = [ELam TUnit (subst 1 (shift 0 1 v) (EVar 1))]   (* binder descent *)
        = [ELam TUnit (shift 0 1 v)]                       (* EVar 1 substitutes *)

      We need [shift 0 1 v = v]. Since [v = ELam TUnit EUnit] and
      [shift c d (ELam T0 e0) = ELam T0 (shift (S c) 1 e0)], we get
      [shift 0 1 (ELam TUnit EUnit) = ELam TUnit (shift 1 1 EUnit) =
       ELam TUnit EUnit = v]. *)

  Lemma e_step :
    forall mu, step (mu, [], e_before) (mu, [], e_after).
  Proof.
    intros mu. unfold e_before, e_after, outer, inner_body.
    change (ELam (TBase TUnit) v)
      with (subst 0 v (ELam (TBase TUnit) (EVar 1))).
    apply S_App_Fun. unfold v. apply VLam.
  Qed.

  (** ===== (c) e_after does NOT type at T_inner =====

      No L1 derivation exists for [[] ; [] |=L1[Affine] e_after :
      T_inner -| ?R_out; ?G_out].

      Proof by inversion: e_after = ELam (TBase TUnit) v is an [ELam]
      whose annotated TFunEff type carries [R_in = [r2]]. Only
      [T_Lam_L1_Linear_Eff] and [T_Lam_L1_Affine_Eff] produce
      TFunEff types ([T_Lam_L1_Linear] and [T_Lam_L1_Affine] produce
      [TFun], discriminated). Both _Eff rules form the body of e_after
      ([v]) at [R = R_in = [r2]] and require [v] to type at
      [TFunEff (TBase TUnit) (TBase TUnit) [] []]; the body
      [v = ELam (TBase TUnit) EUnit] re-enters [T_Lam_L1_*_Eff],
      whose side condition [forall r, In r [r2] -> In r []] is
      contradicted by [In r2 [r2]]. *)

  Lemma e_after_untypable :
    forall R_out G_out,
      ~ has_type_l1 Affine [] [] e_after T_inner R_out G_out.
  Proof.
    intros R_out G_out Ht.
    unfold e_after, T_inner, v in Ht.
    inversion Ht; subst.
    (* Only T_Lam_L1_Affine_Eff survives (mode matches, output type
       structure matches). The body [ELam (TBase TUnit) EUnit] at
       [R = [r2]] must produce a TFunEff. *)
    match goal with
    | [ Hbody : has_type_l1 _ (r2 :: nil) _
                  (ELam (TBase TUnit) EUnit) _ _ _ |- _ ] =>
        rename Hbody into Hv_inner
    end.
    inversion Hv_inner; subst.
    (* Only T_Lam_L1_Affine_Eff survives — T_Lam_L1_Affine produces
       TFun (discriminated against output type
       TFunEff (TBase TUnit) (TBase TUnit) [] []). *)
    match goal with
    | [ Hside : forall r, In r (r2 :: nil) -> In r nil |- _ ] =>
        specialize (Hside r2 (or_introl eq_refl)); inversion Hside
    end.
  Qed.

  (** ===== Soundness-gap witness =====

      The three lemmas above ([e_before_typed] + [e_step] +
      [e_after_untypable]) jointly witness preservation_l2's failure
      for the nested-TFunEff substituent class. No top-level
      conjunction theorem is stated for the same Type/Prop-sort reason
      documented in [Counterexample_L2.v]. *)

End CounterexampleL2Nested.
