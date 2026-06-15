(* SPDX-License-Identifier: PMPL-1.0-or-later *)
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Ephapax Typing Rules — L1 redesign (region capability threading)

    This file contains the **new** typing judgment as specified in
    [formal/PRESERVATION-DESIGN.md §4]. It coexists with the legacy
    [Typing.v] (`has_type`) so that the migration is incremental: old
    lemmas in [Semantics.v] continue to compile against the legacy
    judgment, and [Counterexample.v] gains a new lemma proving the
    L1 fix blocks the bad input.

    The judgment shape is:

      [R_in ; G ⊢ e : T -| R_out ; G']

    where [R_in] is the live-region capability set at the start of
    evaluating [e] and [R_out] is the live-region capability set
    after [e] has reduced to a value. Compound rules thread R
    left-to-right through sub-expressions, mirroring the existing
    G-threading. Region introduction / re-entry rules expose the
    capability shift caused by S_Region_Exit.

    Known limitation (documented for future work):
    - T_Lam_L1 requires the lambda body to be **R-preserving** (body's
      R_in = R_out). Without this, the function call's R-effect would
      need to be carried in TFun, which is an effect-typing extension
      beyond L1's scope. This is the same simplification echo-types
      makes by parameterising over a thin order rather than a fibration.

    See [formal/PRESERVATION-DESIGN.md §4] for the full design
    rationale and [Counterexample.v]'s new [bad_input_untypable_l1]
    lemma for the regression. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

From Ephapax Require Import Syntax.
From Ephapax Require Typing.  (* legacy judgment, for cross-reference only *)

(** ** Helper: remove the first occurrence of [r] from [R].

    Mirrors [remove_first] in [Semantics.v]; restated here so this
    file doesn't pull in the operational semantics. The two are
    pointwise equivalent. *)

Fixpoint remove_first_L1 (r : region_name) (R : region_env) : region_env :=
  match R with
  | [] => []
  | r' :: R' => if String.eqb r r' then R' else r' :: remove_first_L1 r R'
  end.

(** ** L2 Mode scaffolding — the Linear/Affine thin poset.

    See [formal/PRESERVATION-DESIGN.md §5]. The two ephapax sublanguages
    (ephapax-linear, ephapax-affine) share syntax and operational
    semantics; they differ only in which typing derivations the L1
    judgment admits. We encode this by adding a modality parameter
    [m : modality] to [has_type_l1] below.

    The poset structure mirrors
    [echo-types/proofs/agda/EchoLinear.agda:30-101]: two modes
    [Linear] and [Affine] with [Linear <= Affine] (Linear is the
    stricter mode; every Linear derivation is also Affine). The
    order is propositional — each ordered pair has at most one
    proof — which makes the [linear_to_affine] weakening
    deterministic.

    Disambiguation: this is the [L2 modality] of the four-layer
    redesign, internal to ephapax. It is NOT the AffineScript
    language (separate project; shares only the typed-wasm target).
    See [feedback_affinescript_ephapax_siblings_not_impl_proof]. *)

Inductive modality : Type :=
  | Linear : modality
  | Affine : modality.

Inductive le_mod : modality -> modality -> Prop :=
  | le_LL : le_mod Linear Linear
  | le_LA : le_mod Linear Affine
  | le_AA : le_mod Affine Affine.

Definition join_mod (m1 m2 : modality) : modality :=
  match m1 with
  | Linear => m2
  | Affine => Affine
  end.

Lemma le_mod_refl : forall m, le_mod m m.
Proof. destruct m; constructor. Qed.

Lemma le_mod_trans :
  forall m1 m2 m3, le_mod m1 m2 -> le_mod m2 m3 -> le_mod m1 m3.
Proof.
  intros m1 m2 m3 H12 H23.
  destruct H12; destruct H23; constructor.
Qed.

(** Propositionality of [le_mod]: each ordered pair has a unique
    proof. Mirrors [EchoLinear.agda:123] [<=m-prop]. Modality is
    a decidable type with no equality cases, so [dependent
    destruction] suffices. *)
Require Import Coq.Program.Equality.

Lemma le_mod_prop :
  forall m1 m2 (p1 p2 : le_mod m1 m2), p1 = p2.
Proof.
  intros m1 m2 p1 p2.
  dependent destruction p1; dependent destruction p2; reflexivity.
Qed.

Lemma le_mod_join_left : forall m1 m2, le_mod m1 (join_mod m1 m2).
Proof. destruct m1; destruct m2; simpl; constructor. Qed.

Lemma le_mod_join_right : forall m1 m2, le_mod m2 (join_mod m1 m2).
Proof. destruct m1; destruct m2; simpl; constructor. Qed.

Lemma le_mod_join_univ :
  forall m1 m2 m3,
    le_mod m1 m3 -> le_mod m2 m3 -> le_mod (join_mod m1 m2) m3.
Proof.
  intros m1 m2 m3 H1 H2.
  destruct m1; destruct m2; simpl; assumption.
Qed.

(** ** L1 Typing Judgement

    [R_in ; G ⊢ e : T -| R_out ; G']

    The shape mirrors [has_type] from [Typing.v] but adds a sixth
    parameter [R_out] threading the region capability set through
    every rule.

    For values (T_Unit, T_Bool, T_I32, T_Loc, T_StringNew, T_Var_*,
    T_Lam): [R_out = R_in], because evaluating a value does not
    consume regions.

    For compound forms (T_Pair, T_Let, T_LetLin, T_App, T_If, T_Case,
    T_StringConcat, T_Fst, T_Snd, T_Inl, T_Inr, T_Drop, T_Copy):
    [R_in] is threaded through the sub-expressions left-to-right,
    each child's [R_out] becoming the next child's [R_in].

    For region-introduction forms (T_Region, T_Region_Active): the
    body is typed in an environment containing [r]; the outer
    [R_out] equals the body's [R_body] minus one occurrence of [r],
    reflecting S_Region_Exit's operational effect. *)

Reserved Notation "R ';' G '|=L1[' m ']' e ':' T '-|' R' ';' G'"
  (at level 70, m at next level, G at next level, e at next level, T at next level, R' at next level).

Inductive has_type_l1
  : modality -> region_env -> ctx -> expr -> ty -> region_env -> ctx -> Prop :=

  (** ===== Values (R and G unchanged) — modality-polymorphic ===== *)

  | T_Unit_L1 : forall m R G,
      R ; G |=L1[m] EUnit : TBase TUnit -| R ; G

  | T_Bool_L1 : forall m R G b,
      R ; G |=L1[m] EBool b : TBase TBool -| R ; G

  | T_I32_L1 : forall m R G n,
      R ; G |=L1[m] EI32 n : TBase TI32 -| R ; G

  (** ===== Variables ===== *)

  | T_Var_Lin_L1 : forall m R G i T,
      ctx_lookup G i = Some (T, false) ->
      is_linear_ty T = true ->
      R ; G |=L1[m] EVar i : T -| R ; ctx_mark_used G i

  | T_Var_Unr_L1 : forall m R G i T u,
      ctx_lookup G i = Some (T, u) ->
      is_linear_ty T = false ->
      R ; G |=L1[m] EVar i : T -| R ; G

  (** ===== Strings ===== *)

  | T_Loc_L1 : forall m R G l r,
      In r R ->
      R ; G |=L1[m] ELoc l r : TString r -| R ; G

  | T_StringNew_L1 : forall m R G r s,
      In r R ->
      R ; G |=L1[m] EStringNew r s : TString r -| R ; G

  | T_StringConcat_L1 : forall m R R1 R2 G G' G'' e1 e2 r,
      R  ; G  |=L1[m] e1 : TString r -| R1 ; G' ->
      R1 ; G' |=L1[m] e2 : TString r -| R2 ; G'' ->
      R  ; G  |=L1[m] EStringConcat e1 e2 : TString r -| R2 ; G''

  | T_StringLen_L1 : forall m R R' G G' e r,
      R ; G |=L1[m] EBorrow e : TBorrow (TString r) -| R' ; G' ->
      R ; G |=L1[m] EStringLen e : TBase TI32 -| R' ; G'

  (** ===== Let Bindings ===== *)

  (** ===== Let Bindings — MODE-SPLIT =====

      Mirrors the T_Lam / T_Case split (PRESERVATION-DESIGN.md §5).
      Linear: the let-bound variable must be consumed — body output
      head flag forced to [true]. Affine: the body may leave it unused
      ([u : bool] free), which is the affine "implicit drop" of an
      unused binding at the point it goes out of scope. This replaces
      the earlier free-floating [T_Forget_Affine_L1] structural rule,
      which was length-non-preserving (it prepended an extra binding
      to the output context, falsifying [typing_preserves_length_l1]
      and [value_R_G_preserving_l1]). Modelling implicit-drop here, at
      the binder, keeps every rule length-preserving. *)

  | T_Let_L1_Linear : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G                  |=L1[Linear] e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1[Linear] e2 : T2 -| R2 ; (T1, true) :: G'' ->
      R  ; G                  |=L1[Linear] ELet e1 e2 : T2 -| R2 ; G''

  | T_Let_L1_Affine : forall R R1 R2 G G' G'' e1 e2 T1 T2 u,
      R  ; G                  |=L1[Affine] e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1[Affine] e2 : T2 -| R2 ; (T1, u) :: G'' ->
      R  ; G                  |=L1[Affine] ELet e1 e2 : T2 -| R2 ; G''

  | T_LetLin_L1_Linear : forall R R1 R2 G G' G'' e1 e2 T1 T2,
      is_linear_ty T1 = true ->
      R  ; G                  |=L1[Linear] e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1[Linear] e2 : T2 -| R2 ; (T1, true) :: G'' ->
      R  ; G                  |=L1[Linear] ELetLin e1 e2 : T2 -| R2 ; G''

  | T_LetLin_L1_Affine : forall R R1 R2 G G' G'' e1 e2 T1 T2 u,
      is_linear_ty T1 = true ->
      R  ; G                  |=L1[Affine] e1 : T1 -| R1 ; G' ->
      R1 ; ctx_extend G' T1   |=L1[Affine] e2 : T2 -| R2 ; (T1, u) :: G'' ->
      R  ; G                  |=L1[Affine] ELetLin e1 e2 : T2 -| R2 ; G''

  (** ===== Functions — MODE-SPLIT =====

      T_Lam_L1_Linear: the body must end with the bound variable
      unused, i.e. body output ctx = [(T1, true) :: G]. This
      enforces ephapax-linear's "no implicit drop" discipline.

      T_Lam_L1_Affine: the body may end with the bound variable
      either used or unused; output ctx = [(T1, u) :: G] for any
      [u : bool]. This admits ephapax-affine's relaxed binding
      semantics. *)

  | T_Lam_L1_Linear : forall R G T1 T2 e,
      R ; ctx_extend G T1 |=L1[Linear] e : T2 -| R ; (T1, true) :: G ->
      R ; G               |=L1[Linear] ELam T1 e : TFun T1 T2 -| R ; G

  | T_Lam_L1_Affine : forall R G T1 T2 e u,
      R ; ctx_extend G T1 |=L1[Affine] e : T2 -| R ; (T1, u) :: G ->
      R ; G               |=L1[Affine] ELam T1 e : TFun T1 T2 -| R ; G

  | T_App_L1 : forall m R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G  |=L1[m] e1 : TFun T1 T2 -| R1 ; G' ->
      R1 ; G' |=L1[m] e2 : T1          -| R2 ; G'' ->
      R  ; G  |=L1[m] EApp e1 e2 : T2  -| R2 ; G''

  (** ===== Products ===== *)

  | T_Pair_L1 : forall m R R1 R2 G G' G'' e1 e2 T1 T2,
      R  ; G  |=L1[m] e1 : T1 -| R1 ; G' ->
      R1 ; G' |=L1[m] e2 : T2 -| R2 ; G'' ->
      R  ; G  |=L1[m] EPair e1 e2 : TProd T1 T2 -| R2 ; G''

  | T_Fst_L1 : forall m R R' G G' e T1 T2,
      R ; G |=L1[m] e : TProd T1 T2 -| R' ; G' ->
      is_linear_ty T2 = false ->
      R ; G |=L1[m] EFst e : T1 -| R' ; G'

  | T_Snd_L1 : forall m R R' G G' e T1 T2,
      R ; G |=L1[m] e : TProd T1 T2 -| R' ; G' ->
      is_linear_ty T1 = false ->
      R ; G |=L1[m] ESnd e : T2 -| R' ; G'

  (** ===== Sums ===== *)

  | T_Inl_L1 : forall m R R' G G' e T1 T2,
      R ; G |=L1[m] e : T1 -| R' ; G' ->
      R ; G |=L1[m] EInl T2 e : TSum T1 T2 -| R' ; G'

  | T_Inr_L1 : forall m R R' G G' e T1 T2,
      R ; G |=L1[m] e : T2 -| R' ; G' ->
      R ; G |=L1[m] EInr T1 e : TSum T1 T2 -| R' ; G'

  (** T_Case — MODE-SPLIT:
      Linear: both branches must agree on (R_out, G_out) exactly.
      Affine: branches may end with the bound binding in different
        usage states; we use the same shape but allow per-branch
        [u_i : bool] for the bound flag. (Full meet-on-outputs
        deferred to L2-β.) *)

  | T_Case_L1_Linear : forall R R1 R_final G G' G_final e e1 e2 T1 T2 T,
      R  ; G                |=L1[Linear] e  : TSum T1 T2 -| R1 ; G' ->
      R1 ; ctx_extend G' T1 |=L1[Linear] e1 : T -| R_final ; (T1, true) :: G_final ->
      R1 ; ctx_extend G' T2 |=L1[Linear] e2 : T -| R_final ; (T2, true) :: G_final ->
      R  ; G                |=L1[Linear] ECase e e1 e2 : T -| R_final ; G_final

  | T_Case_L1_Affine : forall R R1 R_final G G' G_final e e1 e2 T1 T2 T u1 u2,
      R  ; G                |=L1[Affine] e  : TSum T1 T2 -| R1 ; G' ->
      R1 ; ctx_extend G' T1 |=L1[Affine] e1 : T -| R_final ; (T1, u1) :: G_final ->
      R1 ; ctx_extend G' T2 |=L1[Affine] e2 : T -| R_final ; (T2, u2) :: G_final ->
      R  ; G                |=L1[Affine] ECase e e1 e2 : T -| R_final ; G_final

  (** ===== Conditionals — MODE-SPLIT =====
      Same rationale as T_Case: Linear requires branch agreement;
      Affine relaxes (currently still requires (R_out, G_out) match
      on this Bool-conditional since there is no binder to disagree
      about; left as a separate constructor for symmetry and to
      allow future per-branch G' relaxation). *)

  | T_If_L1_Linear : forall R R1 R2 G G' G'' e1 e2 e3 T,
      R  ; G  |=L1[Linear] e1 : TBase TBool -| R1 ; G' ->
      R1 ; G' |=L1[Linear] e2 : T           -| R2 ; G'' ->
      R1 ; G' |=L1[Linear] e3 : T           -| R2 ; G'' ->
      R  ; G  |=L1[Linear] EIf e1 e2 e3 : T -| R2 ; G''

  | T_If_L1_Affine : forall R R1 R2 G G' G'' e1 e2 e3 T,
      R  ; G  |=L1[Affine] e1 : TBase TBool -| R1 ; G' ->
      R1 ; G' |=L1[Affine] e2 : T           -| R2 ; G'' ->
      R1 ; G' |=L1[Affine] e3 : T           -| R2 ; G'' ->
      R  ; G  |=L1[Affine] EIf e1 e2 e3 : T -| R2 ; G''

  (** ===== Regions ===== *)

  | T_Region_L1 : forall m R R_body G G' r e T,
      ~ In r R ->
      ~ In r (Typing.free_regions T) ->
      In r R_body ->
      (r :: R) ; G |=L1[m] e : T -| R_body ; G' ->
      R ; G |=L1[m] ERegion r e : T -| remove_first_L1 r R_body ; G'

  | T_Region_Active_L1 : forall m R R_body G G' r e T,
      In r R ->
      ~ In r (Typing.free_regions T) ->
      In r R_body ->
      R ; G |=L1[m] e : T -| R_body ; G' ->
      R ; G |=L1[m] ERegion r e : T -| remove_first_L1 r R_body ; G'

  (** ===== Borrowing ===== *)

  | T_Borrow_L1 : forall m R G i T,
      ctx_lookup G i = Some (T, false) ->
      R ; G |=L1[m] EBorrow (EVar i) : TBorrow T -| R ; G

  | T_Borrow_Val_L1 : forall m R G v T,
      is_value v ->
      R ; G |=L1[m] v : T -| R ; G ->
      R ; G |=L1[m] EBorrow v : TBorrow T -| R ; G

  (** ===== Explicit Resource Management =====

      T_Drop_L1: modality-polymorphic. In Linear mode this is the
      sole way to discharge an unused linear binding; in Affine
      mode it remains available (explicit drop), and the implicit-
      drop semantics is provided by T_Forget_Affine_L1 below.

      L3 echo residue: the output [TBase TUnit] here is a residue
      placeholder. Full residue mechanisation deferred to L3
      (PRESERVATION-DESIGN.md §6). *)

  | T_Drop_L1 : forall m R R' G G' e T,
      is_linear_ty T = true ->
      R ; G |=L1[m] e : T -| R' ; G' ->
      R ; G |=L1[m] EDrop e : TBase TUnit -| R' ; G'

  | T_Copy_L1 : forall m R R' G G' e T,
      is_linear_ty T = false ->
      R ; G |=L1[m] e : T -| R' ; G' ->
      R ; G |=L1[m] ECopy e : TProd T T -| R' ; G'

  (** ===== Affine implicit-drop =====

      The affine "implicit drop" of an unused binding is modelled at
      the binders themselves (T_Lam_L1_Affine, T_Let_L1_Affine,
      T_LetLin_L1_Affine, T_Case_L1_Affine: the bound variable's output
      flag is a free [u : bool] rather than forced [true]). The earlier
      free-floating [T_Forget_Affine_L1] rule was removed: it prepended
      an extra binding to the output context, breaking length
      preservation and value-typing invariants. See PRESERVATION-
      DESIGN.md §5 and the T_Let/T_LetLin block above. *)

where "R ';' G '|=L1[' m ']' e ':' T '-|' R' ';' G'" := (has_type_l1 m R G e T R' G').

(** ** Trivial sanity check on the new judgment.

    Every value rule preserves both R and G. This is by inspection
    of the rule shapes above, not a deep theorem. Documented here
    so future readers can re-derive the property without re-reading
    every rule. *)

Lemma value_rules_preserve_R_G_l1 :
  forall m G,
    (forall R, R ; G |=L1[m] EUnit : TBase TUnit -| R ; G) /\
    (forall R b, R ; G |=L1[m] EBool b : TBase TBool -| R ; G) /\
    (forall R n, R ; G |=L1[m] EI32 n : TBase TI32 -| R ; G).
Proof.
  intros m G. split; [|split]; intros.
  - apply T_Unit_L1.
  - apply T_Bool_L1.
  - apply T_I32_L1.
Qed.

(** ** L2 weakening: Linear ⇒ Affine.

    Every derivation in [has_type_l1 Linear ...] is also a derivation
    in [has_type_l1 Affine ...]. This is the modality weakening
    promised by PRESERVATION-DESIGN.md §5 — the "thin-poset
    decoration" lemma, mirror of [EchoLinear.agda:38-58] [weaken :
    LEcho linear → LEcho affine].

    Proof structure: induction on the Linear derivation.
    20 modality-polymorphic constructors close via [econstructor;
    eauto]. The mode-split constructors (T_Lam_L1_Linear,
    T_Case_L1_Linear, T_If_L1_Linear) re-apply the corresponding
    Affine variant — for T_Lam this means choosing [u := true]
    (the Affine rule's binding-output flag), since the Linear rule
    fixed that to [true]. T_Case_L1_Affine takes [u1 := true; u2 :=
    true] similarly.

    This closes success criterion #2 from the L2 task. *)

Lemma linear_to_affine :
  forall R G e T R' G',
    R ; G |=L1[Linear] e : T -| R' ; G' ->
    R ; G |=L1[Affine] e : T -| R' ; G'.
Proof.
  intros R G e T R' G' Ht.
  remember Linear as m eqn:Hm.
  induction Ht; subst; try discriminate;
    try (econstructor; eauto; fail).
Qed.
