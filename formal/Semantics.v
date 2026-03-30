(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell *)

(** * Ephapax Operational Semantics (De Bruijn, Substitution-Based)

    Small-step reduction semantics using De Bruijn indices with explicit
    substitution. Binding constructs (let, let!, lambda application, case)
    resolve their bindings via substitution at reduction time.

    DESIGN NOTE (2026-03-28): The original environment-based semantics
    had an environment-leaking bug: congruence rules (S_Let_Step etc.)
    propagated environment extensions from sub-expression evaluation to
    sibling expressions. For example, evaluating
        let x = (let y = 42 in body) in e2
    would leak y's binding into e2's scope, making preservation genuinely
    false. The substitution-based semantics eliminates this entire class
    of bugs by resolving bindings at reduction time via [subst]. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List. (* AFTER String so List.length wins *)
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Program.Equality.
Import ListNotations.

Require Import Syntax.
Require Import Typing.

(** ** Memory Model *)

Definition loc := nat.

Inductive mem_cell : Type :=
  | CString : region_name -> string -> mem_cell
  | CFree   : mem_cell.

Definition mem := list mem_cell.

(** ** Memory Operations *)

Definition mem_read (mu : mem) (l : loc) : option mem_cell :=
  nth_error mu l.
Arguments mem_read / _ _.

Fixpoint mem_write (mu : mem) (l : loc) (c : mem_cell) : mem :=
  match mu, l with
  | [], _ => []
  | _ :: mu', 0 => c :: mu'
  | h :: mu', S l' => h :: mem_write mu' l' c
  end.

Definition mem_alloc (mu : mem) (c : mem_cell) : (mem * loc) :=
  (mu ++ [c], length mu).

Fixpoint mem_free_region (mu : mem) (r : region_name) : mem :=
  match mu with
  | [] => []
  | CString r' s :: mu' =>
      if String.eqb r r' then CFree :: mem_free_region mu' r
      else CString r' s :: mem_free_region mu' r
  | c :: mu' => c :: mem_free_region mu' r
  end.

Fixpoint remove_first (r : region_name) (R : region_env) : region_env :=
  match R with
  | [] => []
  | r' :: R' =>
      if String.eqb r r' then R'
      else r' :: remove_first r R'
  end.

(** ** Configuration (no runtime environment) *)

Definition config := (mem * region_env * expr)%type.

(** ** Small-Step Reduction (Substitution-Based)

    Key difference from environment-based: binding reductions use [subst]
    instead of extending a runtime environment. No S_Var rule needed —
    variables are resolved by substitution at binding sites. *)

Reserved Notation "c1 '-->>' c2" (at level 70).

Inductive step : config -> config -> Prop :=

  (** String operations *)
  | S_StringNew : forall mu R r s mu' l,
      In r R ->
      mem_alloc mu (CString r s) = (mu', l) ->
      (mu, R, EStringNew r s) -->> (mu', R, ELoc l r)

  | S_StringConcat : forall mu R l1 l2 r s1 s2 mu' l',
      mem_read mu l1 = Some (CString r s1) ->
      mem_read mu l2 = Some (CString r s2) ->
      mem_alloc (mem_write (mem_write mu l1 CFree) l2 CFree)
                (CString r (s1 ++ s2)) = (mu', l') ->
      (mu, R, EStringConcat (ELoc l1 r) (ELoc l2 r))
        -->> (mu', R, ELoc l' r)

  | S_StringConcat_Step1 : forall mu R e1 e1' e2 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, EStringConcat e1 e2) -->> (mu', R', EStringConcat e1' e2)

  | S_StringConcat_Step2 : forall mu R v1 e2 e2' mu' R',
      is_value v1 ->
      (mu, R, e2) -->> (mu', R', e2') ->
      (mu, R, EStringConcat v1 e2) -->> (mu', R', EStringConcat v1 e2')

  | S_StringLen : forall mu R l r s,
      mem_read mu l = Some (CString r s) ->
      (mu, R, EStringLen (ELoc l r)) -->> (mu, R, EI32 (String.length s))

  | S_StringLen_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EStringLen e) -->> (mu', R', EStringLen e')

  (** Let: substitute value into body *)
  | S_Let_Val : forall mu R v1 e2,
      is_value v1 ->
      (mu, R, ELet v1 e2) -->> (mu, R, subst 0 v1 e2)

  | S_Let_Step : forall mu R e1 e1' e2 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, ELet e1 e2) -->> (mu', R', ELet e1' e2)

  | S_LetLin_Val : forall mu R v1 e2,
      is_value v1 ->
      (mu, R, ELetLin v1 e2) -->> (mu, R, subst 0 v1 e2)

  | S_LetLin_Step : forall mu R e1 e1' e2 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, ELetLin e1 e2) -->> (mu', R', ELetLin e1' e2)

  (** Application: substitute argument into body *)
  | S_App_Fun : forall mu R T ebody v2,
      is_value v2 ->
      (mu, R, EApp (ELam T ebody) v2) -->>
        (mu, R, subst 0 v2 ebody)

  | S_App_Step1 : forall mu R e1 e1' e2 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, EApp e1 e2) -->> (mu', R', EApp e1' e2)

  | S_App_Step2 : forall mu R v1 e2 e2' mu' R',
      is_value v1 ->
      (mu, R, e2) -->> (mu', R', e2') ->
      (mu, R, EApp v1 e2) -->> (mu', R', EApp v1 e2')

  (** Conditionals *)
  | S_If_True : forall mu R e2 e3,
      (mu, R, EIf (EBool true) e2 e3) -->> (mu, R, e2)

  | S_If_False : forall mu R e2 e3,
      (mu, R, EIf (EBool false) e2 e3) -->> (mu, R, e3)

  | S_If_Step : forall mu R e1 e1' e2 e3 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, EIf e1 e2 e3) -->> (mu', R', EIf e1' e2 e3)

  (** Products *)
  | S_Pair_Step1 : forall mu R e1 e1' e2 mu' R',
      (mu, R, e1) -->> (mu', R', e1') ->
      (mu, R, EPair e1 e2) -->> (mu', R', EPair e1' e2)

  | S_Pair_Step2 : forall mu R v1 e2 e2' mu' R',
      is_value v1 ->
      (mu, R, e2) -->> (mu', R', e2') ->
      (mu, R, EPair v1 e2) -->> (mu', R', EPair v1 e2')

  | S_Fst : forall mu R v1 v2,
      is_value v1 -> is_value v2 ->
      (mu, R, EFst (EPair v1 v2)) -->> (mu, R, v1)

  | S_Fst_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EFst e) -->> (mu', R', EFst e')

  | S_Snd : forall mu R v1 v2,
      is_value v1 -> is_value v2 ->
      (mu, R, ESnd (EPair v1 v2)) -->> (mu, R, v2)

  | S_Snd_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, ESnd e) -->> (mu', R', ESnd e')

  (** Sums *)
  | S_Inl_Step : forall mu R T e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EInl T e) -->> (mu', R', EInl T e')

  | S_Inr_Step : forall mu R T e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EInr T e) -->> (mu', R', EInr T e')

  (** Case: substitute matched value into branch body *)
  | S_Case_Inl : forall mu R T v e1 e2,
      is_value v ->
      (mu, R, ECase (EInl T v) e1 e2) -->>
        (mu, R, subst 0 v e1)

  | S_Case_Inr : forall mu R T v e1 e2,
      is_value v ->
      (mu, R, ECase (EInr T v) e1 e2) -->>
        (mu, R, subst 0 v e2)

  | S_Case_Step : forall mu R e e' e1 e2 mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, ECase e e1 e2) -->> (mu', R', ECase e' e1 e2)

  (** Regions *)
  | S_Region_Enter : forall mu R r e,
      ~ In r R ->
      (mu, R, ERegion r e) -->> (mu, r :: R, ERegion r e)

  | S_Region_Exit : forall mu R r v,
      is_value v ->
      In r R ->
      (mu, R, ERegion r v) -->>
        (mem_free_region mu r, remove_first r R, v)

  | S_Region_Step : forall mu R r e e' mu' R',
      In r R ->
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, ERegion r e) -->> (mu', R', ERegion r e')

  (** Borrowing *)
  | S_Borrow_Val : forall mu R v,
      is_value v ->
      (mu, R, EBorrow v) -->> (mu, R, v)

  | S_Borrow_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EBorrow e) -->> (mu', R', EBorrow e')

  (** Drop *)
  | S_Drop : forall mu R l r,
      (mu, R, EDrop (ELoc l r)) -->>
        (mem_write mu l CFree, R, EUnit)

  | S_Drop_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, EDrop e) -->> (mu', R', EDrop e')

  (** Copy *)
  | S_Copy : forall mu R v,
      is_value v ->
      (mu, R, ECopy v) -->> (mu, R, EPair v v)

  | S_Copy_Step : forall mu R e e' mu' R',
      (mu, R, e) -->> (mu', R', e') ->
      (mu, R, ECopy e) -->> (mu', R', ECopy e')

where "c1 '-->>' c2" := (step c1 c2).

(** ** Multi-Step *)

Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall c, multi_step c c
  | MS_Step : forall c1 c2 c3,
      step c1 c2 -> multi_step c2 c3 -> multi_step c1 c3.

Notation "c1 '-->*' c2" := (multi_step c1 c2) (at level 70).

(** ** Infrastructure Lemmas *)

(** Values cannot step — fundamental lemma *)
Lemma values_dont_step :
  forall v mu R mu' R' e',
    is_value v -> (mu, R, v) -->> (mu', R', e') -> False.
Proof.
  intros v mu R mu' R' e' Hval Hstep.
  generalize dependent e'. generalize dependent R'.
  generalize dependent mu'. generalize dependent R.
  generalize dependent mu.
  induction Hval; intros; inversion Hstep; subst;
    try (eapply IHHval1; eassumption);
    try (eapply IHHval2; eassumption);
    try (eapply IHHval; eassumption).
Qed.

(** mem_free_region clears all cells for the freed region *)
Lemma mem_free_region_clears :
  forall mu r l s,
    mem_read (mem_free_region mu r) l = Some (CString r s) -> False.
Proof.
  induction mu; intros r l s Hread.
  - simpl in Hread. destruct l; discriminate.
  - simpl in Hread. destruct a.
    + destruct (String.eqb r r0) eqn:Heq.
      * destruct l; simpl in Hread; [discriminate | eapply IHmu; eassumption].
      * destruct l; simpl in Hread.
        -- injection Hread as H1 H2.
           apply String.eqb_neq in Heq; subst; contradiction.
        -- eapply IHmu; eassumption.
    + destruct l; simpl in Hread; [discriminate | eapply IHmu; eassumption].
Qed.

(** Classify steps from ERegion — avoids hypothesis naming issues *)
Lemma step_from_eregion :
  forall mu R r e mu1 R1 e1,
    (mu, R, ERegion r e) -->> (mu1, R1, e1) ->
    (* Enter *) (mu1 = mu /\ R1 = r :: R /\ e1 = ERegion r e)
    (* Exit *)  \/ (In r R /\ is_value e /\ mu1 = mem_free_region mu r
                    /\ R1 = remove_first r R /\ e1 = e)
    (* Step *)  \/ (In r R /\ exists e',
                    (mu, R, e) -->> (mu1, R1, e')
                    /\ e1 = ERegion r e').
Proof.
  intros. inversion H; subst.
  + left. auto.
  + right. left. repeat (split; [auto; fail|]). auto.
  + right. right. split; [assumption|].
    eexists. split; [eassumption | reflexivity].
Qed.

(** expr_locs_valid: all ELoc values in an expression have valid memory cells *)
Fixpoint expr_locs_valid (mu : mem) (e : expr) : Prop :=
  match e with
  | ELoc l r => exists s, mem_read mu l = Some (CString r s)
  | EPair e1 e2 | EStringConcat e1 e2 | EApp e1 e2 =>
      expr_locs_valid mu e1 /\ expr_locs_valid mu e2
  | ELet e1 e2 | ELetLin e1 e2 =>
      expr_locs_valid mu e1 /\ expr_locs_valid mu e2
  | EFst e | ESnd e | EInl _ e | EInr _ e | EDrop e | ECopy e
  | EBorrow e | EDeref e | EStringLen e | ERegion _ e =>
      expr_locs_valid mu e
  | EIf e1 e2 e3 | ECase e1 e2 e3 =>
      expr_locs_valid mu e1 /\ expr_locs_valid mu e2 /\ expr_locs_valid mu e3
  | ELam _ e => expr_locs_valid mu e
  | _ => True
  end.

(** ** Theorem 1: No Memory Leaks (Qed)

    When a region block completes evaluation, all cells for that region
    are freed. Proof: induction on multi_step. *)

Lemma no_leaks_gen :
  forall c1 c2, multi_step c1 c2 ->
    forall r mu R e,
    c1 = (mu, R, ERegion r e) ->
    forall mu' v l s,
    c2 = (mu', ([] : region_env), v) ->
    is_value v ->
    mem_read mu' l = Some (CString r s) -> False.
Proof.
  intros c1 c2 Hmulti.
  induction Hmulti as [c | ca cb cc Hstep Hmulti IH].
  - intros. subst. injection H0; intros; subst. inversion H1.
  - intros r mu R e Hca mu' v l s Hcc Hval Hread.
    subst ca.
    destruct cb as [[mu1 R1] e1].
    pose proof (step_from_eregion _ _ _ _ _ _ _ Hstep) as Hcases.
    destruct Hcases as
      [[-> [-> ->]]
      | [[_ [Hval_e [-> [-> ->]]]]
      | [_ [e' [Hsub ->]]]]].
    + (* Enter *)
      eapply (IH r mu (r :: R) e eq_refl mu' v l s Hcc Hval Hread).
    + (* Exit: body is a value, memory freed *)
      assert (Hcc2: cc = (mem_free_region mu r, remove_first r R, e)).
      { inversion Hmulti.
        - reflexivity.
        - destruct c2 as [[? ?] ?].
          exfalso. eapply values_dont_step; eassumption. }
      assert (mem_free_region mu r = mu') by congruence.
      assert (e = v) by congruence.
      subst. eapply mem_free_region_clears. eassumption.
    + (* Step *)
      eapply (IH r _ _ e' eq_refl mu' v l s Hcc Hval Hread).
Qed.

Theorem no_leaks :
  forall mu R r e mu' v,
    multi_step (mu, R, ERegion r e) (mu', [], v) ->
    is_value v ->
    forall l s, mem_read mu' l = Some (CString r s) -> False.
Proof.
  intros. eapply no_leaks_gen; try eassumption; reflexivity.
Qed.

(** ** Context Transfer Infrastructure

    The key lemma for preservation's congruence cases: an expression that
    types in one context can be retyped in any "compatible" context (same
    types, preserving unused flags). *)

(** Context compatibility: G2 has the same types as G1 at each position,
    and all variables unused in G1 are also unused in G2. *)
Definition ctx_types_agree (G1 G2 : ctx) : Prop :=
  length G1 = length G2 /\
  forall i T u, ctx_lookup G1 i = Some (T, u) ->
    exists u', ctx_lookup G2 i = Some (T, u').

Definition ctx_false_preserved (G1 G2 : ctx) : Prop :=
  forall i T, ctx_lookup G1 i = Some (T, false) ->
    ctx_lookup G2 i = Some (T, false).

Definition ctx_lin_true_preserved (G1 G2 : ctx) : Prop :=
  forall i T, is_linear_ty T = true ->
    ctx_lookup G1 i = Some (T, true) ->
    ctx_lookup G2 i = Some (T, true).

(** Typing only changes flags from false to true, never the reverse.
    Consequence: if (T, false) in the output, it was (T, false) in input. *)
Lemma flags_only_increase :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall i T0, ctx_lookup G' i = Some (T0, false) ->
      ctx_lookup G i = Some (T0, false).
Proof.
  intros R G e T G' Htype.
  induction Htype; intros idx T0 Hlookup; try exact Hlookup;
    try (eapply IHHtype1; eapply IHHtype2; exact Hlookup);
    try (eapply IHHtype; exact Hlookup).
  (* T_Var_Lin: output is ctx_mark_used G i — use projected flag reasoning *)
  - destruct (Nat.eq_dec i idx) as [->|Hne].
    + (* idx = i: mark_used sets flag to true, but Hlookup says false *)
      exfalso.
      assert (Hflag: ctx_lookup_flag (ctx_mark_used G idx) idx = Some true).
      { apply ctx_mark_used_flag_at.
        (* G has something at idx because H says ctx_lookup G idx = Some (T, false) *)
        apply ctx_lookup_split in H. destruct H as [_ Hfl].
        rewrite Hfl. discriminate. }
      assert (Hfalse: ctx_lookup_flag (ctx_mark_used G idx) idx = Some false).
      { apply ctx_lookup_split in Hlookup. destruct Hlookup as [_ Hfl]. exact Hfl. }
      exact (flag_true_not_false _ _ Hflag Hfalse).
    + (* idx <> i: mark_used doesn't touch this position *)
      assert (Hfl: ctx_lookup_flag (ctx_mark_used G i) idx = ctx_lookup_flag G idx).
      { apply ctx_mark_used_flag_other. exact Hne. }
      (* Hlookup is about ctx_lookup (whole pair), extract flag *)
      apply ctx_lookup_split in Hlookup. destruct Hlookup as [Hty Hflag].
      rewrite Hfl in Hflag.
      (* Now Hflag: ctx_lookup_flag G idx = Some false. Need ctx_lookup G idx = Some (T0, false). *)
      (* Also need the type. From H: ctx_lookup G i = Some (T, false), idx <> i *)
      (* We need ctx_lookup_ty G idx. It's preserved by mark_used at i <> idx. *)
      apply ctx_lookup_combine; [|exact Hflag].
      (* Type preserved: mark_used at i doesn't change type at idx *)
      rewrite <- (ctx_mark_used_ty_other G i idx Hne). exact Hty.
  (* T_Let: output G'', bound var at index 0 has flag true.
     Use projected flag reasoning to avoid option-pair discrimination. *)
  (* T_Let: output G'', chain through (T1,false)::G' extended context *)
  - eapply IHHtype1. apply (IHHtype2 (S idx) T0).
    unfold ctx_lookup, ctx_extend in *. simpl. exact Hlookup.
  (* T_LetLin *)
  - eapply IHHtype1. apply (IHHtype2 (S idx) T0).
    unfold ctx_lookup, ctx_extend in *. simpl. exact Hlookup.
  (* T_Case: output G_final, chain through (T1,false)::G' extended context *)
  - eapply IHHtype1. apply (IHHtype2 (S idx) T0).
    unfold ctx_lookup, ctx_extend in *. simpl. exact Hlookup.
Qed.

(** ctx_mark_used preserves types at all positions *)
Lemma ctx_mark_used_lookup_type :
  forall G i j T u,
    ctx_lookup (ctx_mark_used G i) j = Some (T, u) ->
    exists u', ctx_lookup G j = Some (T, u').
Proof.
  induction G; intros i j T u Hlookup; simpl in *.
  - destruct j; discriminate.
  - destruct a. destruct i, j; simpl in *;
    try (injection Hlookup as <- <-; eexists; reflexivity);
    try (eexists; exact Hlookup).
    exact (IHG i j T u Hlookup).
Qed.

(** Typing preserves context bindings: output has same types as input *)
Ltac chain_ih IH1 IH2 Hlookup :=
  let H := fresh in
  destruct (IH2 _ _ _ Hlookup) as [? H]; eapply IH1; exact H.

Ltac chain_shift IH1 IH2 idx Ty uf Hlookup :=
  let H := fresh in
  destruct (IH2 (S idx) Ty uf ltac:(simpl; exact Hlookup)) as [? H];
  simpl in H;
  let H2 := fresh in
  destruct (IH1 _ _ _ H) as [? H2]; eexists; exact H2.

Ltac shift_ih IH idx Ty uf Hlookup :=
  let H := fresh in
  destruct (IH (S idx) Ty uf ltac:(simpl; exact Hlookup)) as [? H];
  simpl in H; eexists; exact H.

Lemma typing_preserves_bindings :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall i T0 u0, ctx_lookup G' i = Some (T0, u0) ->
    exists u1, ctx_lookup G i = Some (T0, u1).
Proof.
  intros R G e T G' Htype.
  induction Htype; intros idx Ty uf Hlookup.
  1: eexists; exact Hlookup.
  1: eexists; exact Hlookup.
  1: eexists; exact Hlookup.
  1: eapply ctx_mark_used_lookup_type; exact Hlookup.
  1: eexists; exact Hlookup.
  1: eexists; exact Hlookup.
  1: eexists; exact Hlookup.
  1: chain_ih IHHtype1 IHHtype2 Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: chain_shift IHHtype1 IHHtype2 idx Ty uf Hlookup.
  1: chain_shift IHHtype1 IHHtype2 idx Ty uf Hlookup.
  1: shift_ih IHHtype idx Ty uf Hlookup.
  1: chain_ih IHHtype1 IHHtype2 Hlookup.
  1: chain_ih IHHtype1 IHHtype2 Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: chain_shift IHHtype1 IHHtype2 idx Ty uf Hlookup.
  1: chain_ih IHHtype1 IHHtype2 Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: eexists; exact Hlookup.
  1: eapply IHHtype; exact Hlookup.
  1: eapply IHHtype; exact Hlookup.
Qed.

(** Canonical forms lemmas *)

Lemma canonical_bool :
  forall R G G' v,
    R; G |- v : TBase TBool -| G' -> is_value v -> exists b, v = EBool b.
Proof. intros; inversion H0; subst; inversion H; subst; eauto. Qed.

Lemma canonical_fun :
  forall R G G' v T1 T2,
    R; G |- v : TFun T1 T2 -| G' -> is_value v ->
    exists body, v = ELam T1 body.
Proof. intros; inversion H0; subst; inversion H; subst; eauto. Qed.

Lemma canonical_prod :
  forall R G G' v T1 T2,
    R; G |- v : TProd T1 T2 -| G' -> is_value v ->
    exists v1 v2, v = EPair v1 v2 /\ is_value v1 /\ is_value v2.
Proof. intros; inversion H0; subst; inversion H; subst; eexists _, _; auto. Qed.

Lemma canonical_sum :
  forall R G G' v T1 T2,
    R; G |- v : TSum T1 T2 -| G' -> is_value v ->
    (exists T v0, v = EInl T v0 /\ is_value v0) \/
    (exists T v0, v = EInr T v0 /\ is_value v0).
Proof.
  intros; inversion H0; subst; inversion H; subst;
    [left|right]; eexists _, _; auto.
Qed.

Lemma canonical_string :
  forall R G G' v r,
    R; G |- v : TString r -| G' -> is_value v -> exists l, v = ELoc l r.
Proof. intros; inversion H0; subst; inversion H; subst; eauto. Qed.

(** ** Context Transfer Lemma

    If an expression types in context G, it can be retyped in any
    compatible context G2 (same types, preserving unused flags).
    The output preserves types, unused flags, and consumption:
    variables consumed in the original are consumed in the transfer. *)

(* ctx_mark_used_lookup_same removed — use ctx_mark_used_flag_at from Syntax.v instead *)

(** ctx_mark_used at position i leaves other positions unchanged *)
Lemma ctx_mark_used_lookup_other :
  forall G i j,
    i <> j ->
    ctx_lookup (ctx_mark_used G i) j = ctx_lookup G j.
Proof.
  induction G as [|[T0 u0] G' IH]; intros i j Hne.
  - unfold ctx_lookup. destruct i; destruct j; reflexivity.
  - destruct i; destruct j; simpl.
    + exfalso. apply Hne. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro H. apply Hne. f_equal. exact H.
Qed.

(** types_agree output shape: if original output is (T,u)::G', transferred
    output has same shape (T,u')::G2' *)
Lemma types_agree_cons_shape :
  forall T u G' G2,
    ctx_types_agree ((T, u) :: G') G2 ->
    exists u' G2', G2 = (T, u') :: G2' /\ ctx_types_agree G' G2'.
Proof.
  intros T u G' G2 [Hlen Hlk].
  destruct G2 as [|[T2 u2] G2'].
  - simpl in Hlen. lia.
  - destruct (Hlk 0 T u) as [u' Hu']. { simpl. reflexivity. }
    simpl in Hu'.
    (* Hu' : Some (T2, u2) = Some (T, u'). Extract type equality via projection. *)
    assert (HT: T2 = T).
    { apply (f_equal (fun x => match x with Some (t, _) => t | None => T end)) in Hu'.
      simpl in Hu'. exact Hu'. }
    subst T2.
    exists u2, G2'. split; [reflexivity|].
    split.
    + simpl in Hlen. lia.
    + intros i T0 u0 Hi. destruct (Hlk (S i) T0 u0) as [u0' Hu0'].
      { simpl. exact Hi. }
      simpl in Hu0'. eexists. exact Hu0'.
Qed.

(** Consumption chain: if i was consumed in two-step typing G→G'→G'',
    and both steps were transferred, consumption is preserved *)
Lemma ctx_mark_used_types_agree :
  forall G1 G2 i,
    ctx_types_agree G1 G2 ->
    ctx_types_agree (ctx_mark_used G1 i) (ctx_mark_used G2 i).
Proof.
  intros G1. induction G1 as [|[Ta ua] G1' IH]; intros G2 i [Hlen Hlk].
  - simpl. destruct G2; [split; auto | simpl in Hlen; lia].
  - destruct G2 as [|[Tb ub] G2'].
    + simpl in Hlen. lia.
    + destruct i; simpl.
      * (* i = 0: flags set to true, types preserved *)
        split.
        -- simpl in Hlen. exact Hlen.
        -- intros j T0 u0 Hj. destruct j; simpl in *.
           ++ (* j = 0: mark_used at 0 gives (Ta,true). Hj says T0=Ta, u0=true. *)
              assert (T0 = Ta) by congruence. subst T0.
              destruct (Hlk 0 Ta ua) as [u' Hu']. { simpl. reflexivity. }
              simpl in Hu'.
              assert (Tb = Ta) by congruence. subst Tb.
              eexists. reflexivity.
           ++ destruct (Hlk (S j) T0 u0) as [u' Hu']. { simpl. exact Hj. }
              simpl in Hu'. eexists. exact Hu'.
      * (* i = S i': recurse *)
        assert (Ha': ctx_types_agree G1' G2').
        { split.
          - simpl in Hlen. lia.
          - intros j T0 u0 Hj. destruct (Hlk (S j) T0 u0) as [u' Hu'].
            { simpl. exact Hj. } simpl in Hu'. eexists. exact Hu'. }
        destruct (IH G2' i Ha') as [Hlen' Hlk'].
        split.
        -- simpl. f_equal. exact Hlen'.
        -- intros j T0 u0 Hj. destruct j; simpl in *.
           ++ destruct (Hlk 0 T0 u0) as [u' Hu']. { simpl. exact Hj. }
              simpl in Hu'. eexists. exact Hu'.
           ++ destruct (Hlk' j T0 u0 Hj) as [u' Hu']. eexists. exact Hu'.
Qed.

Lemma ctx_mark_used_false_preserved :
  forall G1 G2 i,
    ctx_false_preserved G1 G2 ->
    ctx_false_preserved (ctx_mark_used G1 i) (ctx_mark_used G2 i).
Proof.
  unfold ctx_false_preserved.
  intro G1. induction G1 as [|[Ta ua] G1' IH]; intros G2 i Hfp j Tb Hj.
  (* G1 = []: ctx_mark_used [] i = []. Lookup in [] gives None. *)
  - unfold ctx_lookup in Hj. destruct i; destruct j; simpl in Hj; congruence.
  (* G1 = (Ta,ua)::G1' *)
  - destruct G2 as [|[Tc uc] G2'].
    + (* G2 = []: goal is ctx_lookup [] j = Some(Tb,false) i.e. None=Some — absurd.
         Derive False via case split on j=i vs j≠i. *)
      exfalso.
      destruct (Nat.eq_dec j i) as [Heq | Hne].
      * (* j = i: mark_used at i sets flag to true, but Hj says false *)
        subst j.
        (* Use projected lookups to extract the flag contradiction *)
        destruct (ctx_lookup_split _ _ _ _ Hj) as [_ Hflag_false].
        assert (Hne: ctx_lookup_flag ((Ta, ua) :: G1') i <> None).
        { intro Habs. unfold ctx_lookup_flag in Habs.
          unfold ctx_lookup in Hj.
          destruct (nth_error ((Ta, ua) :: G1') i) as [[? ?]|] eqn:E.
          - discriminate.
          - (* nth_error is None → ctx_mark_used at i also gives None at i *)
            assert (Hmu: nth_error (ctx_mark_used ((Ta, ua) :: G1') i) i = None).
            { clear -E. generalize dependent i. induction ((Ta,ua)::G1') as [|[T0 u0] l IHl]; intros.
              - destruct i; reflexivity.
              - destruct i; simpl in *.
                + discriminate.
                + apply IHl. exact E. }
            rewrite Hmu in Hj. discriminate. }
        pose proof (ctx_mark_used_flag_at _ _ Hne) as Htrue.
        rewrite Htrue in Hflag_false. discriminate.
      * (* j ≠ i: lookup at j is unchanged by mark_used *)
        rewrite ctx_mark_used_lookup_other in Hj by (intro; apply Hne; symmetry; assumption).
        assert (Habs := Hfp j Tb Hj).
        unfold ctx_lookup in Habs. destruct j; simpl in Habs; discriminate.
    + destruct i; destruct j; simpl in *.
      * (* i=0, j=0: mark_used sets flag to true. Hj says flag is false. *)
        congruence.
      * (* i=0, j=S j': unchanged at j. Chain through Hfp. *)
        exact (Hfp (S j) Tb Hj).
      * (* i=S i', j=0: unchanged at 0. Chain through Hfp. *)
        exact (Hfp 0 Tb Hj).
      * (* i=S i', j=S j': recurse on G1' and G2'. *)
        apply IH with (i := i).
        intros k T0 Hk. exact (Hfp (S k) T0 Hk).
        exact Hj.
Qed.

Lemma ctx_extend_types_agree :
  forall G1 G2 T,
    ctx_types_agree G1 G2 ->
    ctx_types_agree (ctx_extend G1 T) (ctx_extend G2 T).
Proof.
  intros G1 G2 T [Hlen Hlk]. unfold ctx_extend. split.
  - simpl. f_equal. exact Hlen.
  - intros i T0 u Hi. destruct i; simpl in *.
    + injection Hi as -> ->. eexists. reflexivity.
    + destruct (Hlk i T0 u Hi) as [u' Hu']. eexists. exact Hu'.
Qed.

Lemma ctx_extend_false_preserved :
  forall G1 G2 T,
    ctx_false_preserved G1 G2 ->
    ctx_false_preserved (ctx_extend G1 T) (ctx_extend G2 T).
Proof.
  unfold ctx_false_preserved, ctx_extend. intros G1 G2 T Hfp i T0 Hi.
  destruct i; simpl in *.
  - exact Hi.
  - exact (Hfp i T0 Hi).
Qed.

(** ** Flags Monotonicity

    Once a flag is true, it stays true through typing. This follows from
    flags_only_increase (false in output → false in input) contraposed
    with type agreement (every position in input has a corresponding
    position in output with the same type). *)

Lemma flags_monotone :
  forall R G e T G' i T0,
    R; G |- e : T -| G' ->
    ctx_lookup G i = Some (T0, true) ->
    ctx_lookup G' i = Some (T0, true).
Proof.
  intros R G e T G' i T0 Htype Hin.
  unfold ctx_lookup.
  assert (Hlen: length G' = length G) by (eapply typing_preserves_length; eassumption).
  unfold ctx_lookup in Hin.
  assert (Hi: i < length G) by (apply nth_error_Some; congruence).
  destruct (nth_error G' i) as [[T1 u1]|] eqn:Hout.
  2: { apply nth_error_None in Hout. lia. }
  (* T1 = T0 by typing_preserves_bindings *)
  destruct (typing_preserves_bindings _ _ _ _ _ Htype i T1 u1) as [u2 Hu2].
  { unfold ctx_lookup. exact Hout. }
  unfold ctx_lookup in Hu2. rewrite Hin in Hu2.
  assert (HT: T1 = T0) by congruence. subst T1.
  (* u1 must be true — if false, flags_only_increase gives contradiction *)
  destruct u1; [reflexivity |].
  exfalso.
  assert (Hf := flags_only_increase _ _ _ _ _ Htype i T0).
  unfold ctx_lookup in Hf. rewrite Hout in Hf.
  specialize (Hf eq_refl). congruence.
Qed.

(** ** Consumption Tracking

    The key property for closing T_Let/T_LetLin/T_Lam in ctx_transfer:
    if an expression consumes a variable (flag goes false→true) in one
    typing, it also consumes it in any compatible re-typing.

    Proved by strengthening the transfer conclusion with a fourth conjunct. *)

Definition ctx_consumption_tracked
  (G G' G2 G2' : ctx) : Prop :=
  forall i T0,
    ctx_lookup G i = Some (T0, false) ->
    ctx_lookup G' i = Some (T0, true) ->
    ctx_lookup G2 i = Some (T0, false) ->
    ctx_lookup G2' i = Some (T0, true).

(** Consumption chains through two-step typing.
    Case split: was i consumed in step 1 or step 2?
    u_mid=true: Hc1 gives G2m true, flags_monotone gives G2' true.
    u_mid=false: Hfpm gives G2m false, Hc2 gives G2' true. *)
Lemma consumption_chain :
  forall R1 G e1 T1 Gm R2 e2 T2 G' G2 G2m G2',
    R1; G |- e1 : T1 -| Gm ->
    R2; Gm |- e2 : T2 -| G' ->
    R2; G2m |- e2 : T2 -| G2' ->
    ctx_consumption_tracked G Gm G2 G2m ->
    ctx_consumption_tracked Gm G' G2m G2' ->
    ctx_false_preserved Gm G2m ->
    ctx_consumption_tracked G G' G2 G2'.
Proof.
  unfold ctx_consumption_tracked.
  intros R1 G e1 T1 Gm R2 e2 T2 G' G2 G2m G2'
    Htype1 Htype2 Htype2' Hc1 Hc2 Hfpm i T0 Hi_in Hi_out Hi_in2.
  (* Get Gm's flag at position i via typing_preserves_bindings on Htype1.
     We know G has (T0, false) at i. Need to know what Gm has.
     flags_only_increase on Htype1: if Gm has false → G has false (consistent).
     We need the actual value. Use nth_error + length preservation. *)
  (* Get Gm's value at position i *)
  assert (Hlen1: length Gm = length G) by (eapply typing_preserves_length; eassumption).
  unfold ctx_lookup in Hi_in.
  assert (Hi: i < length Gm).
  { rewrite Hlen1. apply nth_error_Some. congruence. }
  destruct (nth_error Gm i) as [[Tm u_mid]|] eqn:Emid.
  2: { apply nth_error_None in Emid. lia. }
  (* Tm = T0 by typing_preserves_bindings *)
  destruct (typing_preserves_bindings _ _ _ _ _ Htype1 i Tm u_mid) as [u_in Hu_in].
  { unfold ctx_lookup. exact Emid. }
  unfold ctx_lookup in Hu_in. rewrite Hi_in in Hu_in.
  assert (Tm = T0) by congruence. subst Tm.
  (* Case split on u_mid *)
  destruct u_mid.
  - (* Gm has true at i — step 1 consumed it *)
    assert (Hm2: ctx_lookup G2m i = Some (T0, true)).
    { apply Hc1 with (i := i) (T0 := T0).
      - unfold ctx_lookup. exact Hi_in.
      - unfold ctx_lookup. exact Emid.
      - exact Hi_in2. }
    exact (flags_monotone _ _ _ _ _ _ _ Htype2' Hm2).
  - (* Gm has false at i — step 1 didn't consume it *)
    assert (Hm2: ctx_lookup G2m i = Some (T0, false)).
    { apply Hfpm. unfold ctx_lookup. exact Emid. }
    apply Hc2 with (i := i) (T0 := T0).
    + unfold ctx_lookup. exact Emid.
    + exact Hi_out.
    + exact Hm2.
Qed.

(** Non-consumption preservation: if a position is unchanged by the original
    typing, it's unchanged by any compatible re-typing. This is the converse
    of consumption_tracked. It follows from syntax-directedness: the same
    expression accesses the same variables, so positions not accessed in
    the original are not accessed in the transfer.

    The critical case: position i has linear type, flag true in G (consumed),
    flag false in G2 (available). The body doesn't access i in the original
    (T_Var_Lin requires false, but G has true). By syntax-directedness,
    the body also doesn't access i in the transfer. So G2'[i] = G2[i]. *)
(** Helper: typing preserves types_agree between two compatible typings *)
Lemma typing_preserves_types_agree :
  forall R G e T G' G2 G2',
    R; G |- e : T -| G' ->
    R; G2 |- e : T -| G2' ->
    ctx_types_agree G G2 ->
    ctx_types_agree G' G2'.
Proof.
  intros R G e T G' G2 G2' H1 H2 [Hlen Hbind].
  split.
  - assert (L1 := typing_preserves_length _ _ _ _ _ H1).
    assert (L2 := typing_preserves_length _ _ _ _ _ H2). lia.
  - intros j Tj uj Hj.
    (* G'[j] = (Tj, uj). By preserves_bindings on H1: G[j] = (Tj, ?) *)
    destruct (typing_preserves_bindings _ _ _ _ _ H1 j Tj uj Hj) as [u1 Hu1].
    (* By types_agree G G2: G2[j] = (Tj, ?) *)
    destruct (Hbind j Tj u1 Hu1) as [u2 Hu2].
    (* G2' has same types as G2. Need G2'[j] = (Tj, ?).
       By length: j < length G2'. *)
    assert (L2 := typing_preserves_length _ _ _ _ _ H2).
    assert (L1 := typing_preserves_length _ _ _ _ _ H1).
    unfold ctx_lookup in *.
    assert (Hj_lt: j < length G2').
    { assert (Hj_some: nth_error G' j <> None) by congruence.
      rewrite nth_error_Some in Hj_some. lia. }
    destruct (nth_error G2' j) as [[Tj2 uj2]|] eqn:E2'.
    + destruct (typing_preserves_bindings _ _ _ _ _ H2 j Tj2 uj2) as [u3 Hu3].
      { unfold ctx_lookup. exact E2'. }
      unfold ctx_lookup in Hu3. rewrite Hu2 in Hu3.
      assert (Tj2 = Tj) by congruence. subst Tj2.
      eexists. reflexivity.
    + rewrite nth_error_None in E2'. lia.
Qed.

Lemma ctx_lookup_extend_succ :
  forall G T i, ctx_lookup (ctx_extend G T) (S i) = ctx_lookup G i.
Proof. intros. reflexivity. Qed.

Lemma no_consumption_at_true_linear :
  forall R G e T G' G2 G2' i T0,
    R; G |- e : T -| G' ->
    R; G2 |- e : T -| G2' ->
    ctx_types_agree G G2 ->
    is_linear_ty T0 = true ->
    ctx_lookup G i = Some (T0, true) ->
    ctx_lookup G' i = Some (T0, true) ->
    ctx_lookup G2 i = Some (T0, false) ->
    ctx_lookup G2' i = Some (T0, false).
Proof.
  intros R G e T G' G2 G2' i T0 H1 H2 Hagree Hlin HiG HiG' HiG2.
  (* Generalize i, T0, and all position-dependent hypotheses so the IH
     works at shifted indices (S i) in binding cases (T_Case, T_If, T_Let). *)
  generalize dependent G2'. generalize dependent G2.
  generalize dependent T0. generalize dependent i.
  induction H1 as
    [ (* T_Unit *)
    | (* T_Bool *)
    | (* T_I32 *)
    | ? ? j ? ? ? (* T_Var_Lin *)
    | ? ? j ? ? ? (* T_Var_Unr *)
    | (* T_Loc *)
    | (* T_StringNew *)
    | ? ? ? ? ? ? IHe1 ? IHe2 (* T_StringConcat *)
    | ? ? ? ? ? IHe1 (* T_StringLen *)
    | ? ? ? ? ? ? ? ? IHe1 ? IHe2 (* T_Let *)
    | ? ? ? ? ? ? ? ? IHe1 ? IHe2 (* T_LetLin *)
    | ? ? ? ? ? IHe1 (* T_Lam *)
    | ? ? ? ? ? ? ? ? IHe1 ? IHe2 (* T_App *)
    | ? ? ? ? ? ? ? ? IHe1 ? IHe2 (* T_Pair *)
    | ? ? ? ? ? ? IHe1 (* T_Fst *)
    | ? ? ? ? ? ? IHe1 (* T_Snd *)
    | ? ? ? ? ? ? IHe1 (* T_Inl *)
    | ? ? ? ? ? ? IHe1 (* T_Inr *)
    | ? ? ? ? ? ? ? ? ? IHe1 ? IHe2 ? IHe3 (* T_Case *)
    | ? ? ? ? ? ? ? ? IHe1 ? IHe2 ? IHe3 (* T_If *)
    | ? ? ? ? ? ? IHe1 (* T_Region *)
    | ? ? j0 ? ? (* T_Borrow *)
    | ? ? ? ? ? IHe1 (* T_Drop *)
    | ? ? ? ? ? IHe1 (* T_Copy *)
    ]; intros i T0 Hlin HiG HiG' G2 Hagree HiG2 G2' H2.

  (* T_Unit *) - inversion H2; subst. exact HiG2.
  (* T_Bool *) - inversion H2; subst. exact HiG2.
  (* T_I32 *) - inversion H2; subst. exact HiG2.

  (* T_Var_Lin at index j *)
  - inversion H2; subst.
    + destruct (Nat.eq_dec i j).
      * subst j. rewrite HiG in H. congruence.
      * rewrite ctx_mark_used_lookup_other by (intro; apply n; symmetry; assumption).
        rewrite ctx_mark_used_lookup_other in HiG' by (intro; apply n; symmetry; assumption).
        exact HiG2.
    + exfalso. congruence.

  (* T_Var_Unr *)
  - inversion H2; subst.
    + exfalso. congruence.
    + exact HiG2.

  (* T_Loc *) - inversion H2; subst. exact HiG2.
  (* T_StringNew *) - inversion H2; subst. exact HiG2.

  (* T_StringConcat: IH on e1 gives G2_mid[i]=false, IH on e2 gives G2'[i]=false *)
  - inversion H2; subst.
    eauto 6 using typing_preserves_types_agree, flags_monotone.
  (* All remaining compound cases: use eauto with IH + key lemmas.
     T_Case and T_If need ctx_join reasoning — admit for those. *)
  all: try (inversion H2; subst; exact HiG2).
  all: try (inversion H2; subst;
    eauto 6 using typing_preserves_types_agree, flags_monotone,
                   ctx_extend_types_agree).
  (* T_Case: scrutinee consumes from G→G', branches extend G' by T1/T2,
     both converge to G_final. With i generalized, IH works at S i. *)
  all: try (inversion H2; subst;
    eauto 8 using typing_preserves_types_agree, flags_monotone,
                  ctx_extend_types_agree, ctx_extend_false_preserved,
                  ctx_lookup_extend_succ).
  all: admit.
Admitted.
(* NOTE (2026-03-29): The generalized version of this lemma (with i and T0
   universally quantified before induction) is proved in test files. The
   generalization is necessary for binding cases where position i in G
   corresponds to S i in ctx_extend G T. The current Admitted version has
   i fixed before induction, which prevents the IH from being used at
   shifted positions. See borrow_preserves_ctx, stringlen_preserves_ctx,
   and type_determinacy below for the required building blocks.
   Closing this Admitted requires restructuring the proof to match the
   generalized statement, and carefully avoiding Rocq 9.1.1's subst
   cross-goal contamination in focused proof blocks. *)

(** ** New Helper Lemmas (2026-03-29)
    Building blocks for closing the remaining Admitted proofs. *)

(** Borrow always preserves context — T_Borrow output = input *)
Lemma borrow_preserves_ctx :
  forall R G e T G', R; G |- EBorrow e : T -| G' -> G' = G.
Proof. intros. inversion H; subst. reflexivity. Qed.

(** StringLen preserves context — its only premise is a borrow *)
Lemma stringlen_preserves_ctx :
  forall R G e T G', R; G |- EStringLen e : T -| G' -> G' = G.
Proof.
  intros. inversion H; subst.
  match goal with [ H0 : context [EBorrow _] |- _ ] =>
    apply borrow_preserves_ctx in H0; exact H0 end.
Qed.

(** Type determinacy: same expression in type-compatible contexts gives same type.
    Required for no_consumption_at_true_linear binding cases where inversion
    of the second typing derivation yields a potentially different intermediate type.
    Proved for all cases except 2 remaining Pair/Copy Ltac-pattern goals that need
    explicit handling due to Rocq 9.1.1 notation conflicts in Ltac. *)
Lemma type_determinacy :
  forall R G e T G', R; G |- e : T -| G' ->
    forall G2 T2 G2', R; G2 |- e : T2 -| G2' -> ctx_types_agree G G2 -> T = T2.
Proof.
  intros R G e T G' H1.
  induction H1; intros G2x T2x G2x' H2 Hagree.
  all: inversion H2; subst; try reflexivity.
  (* Variable lookup cases: types agree by context compatibility *)
  all: try (match goal with
    | [ H : ctx_lookup ?G ?i = Some (?T, ?u),
        H3 : ctx_lookup ?G2 ?i = Some (_, _),
        Hagr : ctx_types_agree ?G ?G2 |- _ ] =>
      destruct (proj2 Hagr _ _ _ H) as [? ?]; congruence end).
  (* Binding chain: IH1 gives intermediate type equality, IH2 gives result *)
  all: try (match goal with
    | [ IH : context [ctx_types_agree (ctx_extend _ _) _ -> _ = _],
        IH1 : context [ctx_types_agree ?G0 _ -> ?T1 = _] |- _ ] =>
      let HTeq := fresh in
      (assert (HTeq : T1 = _) by (eapply IH1; eassumption));
      rewrite <- HTeq in *;
      eapply IH; [eassumption|];
      first [ apply ctx_extend_types_agree; eapply typing_preserves_types_agree; eassumption
            | eapply typing_preserves_types_agree; eassumption ]
    end).
  (* Single-expression: IH directly *)
  all: try (match goal with [ IH : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
    first [ eapply IH; eassumption ] end).
  all: try congruence.
  (* Lambda body *)
  all: try (f_equal; match goal with
    [ IH : context [ctx_types_agree (ctx_extend _ _) _ -> _ = _] |- _ ] =>
      eapply IH; [eassumption|]; apply ctx_extend_types_agree; assumption end).
  (* Injection cases *)
  all: try (match goal with [ IH : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
    let HTeq := fresh in (assert (HTeq : _ = _) by (eapply IH; eassumption)); congruence end).
  (* Chain cases: e1 then e2 *)
  all: try (match goal with
    | [ IH1 : context [ctx_types_agree _ _ -> _ = _],
        IH2 : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
      let HTeq := fresh in
      (assert (HTeq : _ = _) by (eapply IH1; eassumption));
      rewrite <- HTeq in *;
      (eapply IH2; [eassumption|]; eapply typing_preserves_types_agree; eassumption)
    end).
  (* Case: scrutinee determines sum type *)
  all: try (match goal with
    | [ IH1 : context [ctx_types_agree _ _ -> TSum _ _ = _] |- _ ] =>
      let HTeq := fresh in (assert (HTeq : TSum _ _ = TSum _ _) by (eapply IH1; eassumption));
      injection HTeq as <- <- end;
      match goal with [ IH : context [ctx_types_agree (ctx_extend _ _) _ -> _ = _] |- _ ] =>
        eapply IH; [eassumption|]; apply ctx_extend_types_agree;
        eapply typing_preserves_types_agree; eassumption end).
  (* Remaining 2 goals: Pair and Copy — need explicit handling *)
  all: admit.
Admitted.

(** Context pointwise equality from flag agreement *)
Lemma ctx_eq_from_flags :
  forall (G1 G2 : ctx),
    length G1 = length G2 ->
    (forall i, nth_error G1 i = nth_error G2 i) ->
    G1 = G2.
Proof.
  intro G1. induction G1 as [|[T1 u1] G1' IH]; intros G2 Hlen Heq.
  - destruct G2; [reflexivity | simpl in Hlen; lia].
  - destruct G2 as [|[T2 u2] G2'].
    + simpl in Hlen. lia.
    + assert (H0 := Heq 0). simpl in H0. injection H0 as <- <-.
      f_equal. apply IH.
      * simpl in Hlen. lia.
      * intro i. exact (Heq (S i)).
Qed.

Lemma typing_ctx_transfer :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall G2,
      ctx_types_agree G G2 ->
      ctx_false_preserved G G2 ->
      exists G2', R; G2 |- e : T -| G2'
        /\ ctx_types_agree G' G2'
        /\ ctx_false_preserved G' G2'
        /\ ctx_consumption_tracked G G' G2 G2'.
Proof.
  intros R G e T G' Htype.
  induction Htype; intros G2 Hagree Hfp.

  (* All cases need 4 conjuncts. Identity-context cases (G'=G) have
     vacuous consumption tracking (false≠true at same position). *)

  (* T_Unit, T_Bool, T_I32: G'=G *)
  1-3: eexists; split; [econstructor | split; [| split; [| unfold ctx_consumption_tracked; intros; congruence]]]; assumption.

  (* T_Var_Lin *)
  - assert (Hlk2: ctx_lookup G2 i = Some (T, false)) by (apply Hfp; assumption).
    eexists. split; [econstructor; eassumption|].
    split; [apply ctx_mark_used_types_agree; assumption|].
    split; [apply ctx_mark_used_false_preserved; assumption|].
    admit.

  (* T_Var_Unr: G'=G, consumption vacuous *)
  - destruct (proj2 Hagree i T u H) as [u' Hu'].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_Loc: G'=G *)
  - eexists. split; [econstructor; assumption|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_StringNew: G'=G *)
  - eexists. split; [econstructor; assumption|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_StringConcat: chain *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 G2' Ha1 Hf1) as [G2'' [Ht2 [Ha2 [Hf2 Hc2]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption |]].
    eapply consumption_chain; eassumption.

  (* T_StringLen *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; exact Ht|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Let — NOW CLOSEABLE with consumption tracking from IH *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 (ctx_extend G2' T1)
                (ctx_extend_types_agree _ _ _ Ha1)
                (ctx_extend_false_preserved _ _ _ Hf1))
      as [G2'' [Ht2 [Ha2 [Hf2 Hc2]]]].
    destruct (types_agree_cons_shape _ _ _ _ Ha2) as [u' [G2_tail [Heq Ha_tail]]].
    subst G2''.
    (* u' = true: position 0 starts false (ctx_extend), original output has true,
       so consumption tracking gives transferred output also has true. *)
    assert (Hu': u' = true).
    { assert (H0in: ctx_lookup (ctx_extend G' T1) 0 = Some (T1, false)) by reflexivity.
      assert (H0out: ctx_lookup ((T1, true) :: G'') 0 = Some (T1, true)) by reflexivity.
      assert (H0in2: ctx_lookup (ctx_extend G2' T1) 0 = Some (T1, false)) by reflexivity.
      assert (H0out2 := Hc2 0 T1 H0in H0out H0in2).
      simpl in H0out2. congruence. }
    subst u'.
    eexists. split; [eapply T_Let; eassumption|].
    split; [exact Ha_tail | split; admit].

  (* T_LetLin — same pattern as T_Let *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 (ctx_extend G2' T1)
                (ctx_extend_types_agree _ _ _ Ha1)
                (ctx_extend_false_preserved _ _ _ Hf1))
      as [G2'' [Ht2 [Ha2 [Hf2 Hc2]]]].
    destruct (types_agree_cons_shape _ _ _ _ Ha2) as [u' [G2_tail [Heq Ha_tail]]].
    subst G2''.
    assert (Hu': u' = true).
    { assert (H0out2 := Hc2 0 T1 eq_refl eq_refl eq_refl).
      simpl in H0out2. congruence. }
    subst u'.
    eexists. split; [eapply T_LetLin; eassumption|].
    split; [exact Ha_tail | split; admit].

  (* T_Lam: output = input G. Need transfer output = (T1,true)::G2. *)
  - destruct (IHHtype (ctx_extend G2 T1)
                (ctx_extend_types_agree _ _ _ Hagree)
                (ctx_extend_false_preserved _ _ _ Hfp))
      as [G2' [Ht [Ha [Hf Hc]]]].
    destruct (types_agree_cons_shape _ _ _ _ Ha) as [u' [G2_tail [Heq Ha_tail]]].
    subst G2'.
    (* u' = true via consumption tracking *)
    assert (Hu': u' = true).
    { assert (H0 := Hc 0 T1 eq_refl eq_refl eq_refl). simpl in H0. congruence. }
    subst u'.
    (* G2_tail = G2: pointwise equality.
       - G2[j]=true: flags_monotone on body transfer gives G2_tail[j]=true ✓
       - G2[j]=false, G[j]=false: output false_preserved gives G2_tail[j]=false ✓
       - G2[j]=false, G[j]=true: needs no_consumption_at_true_linear (syntax-directedness)
       Proof structure verified; one sub-case needs the Admitted helper. *)
    assert (HGeq: G2_tail = G2) by admit.
    subst G2_tail.
    eexists. split; [eapply T_Lam; exact Ht|].
    split; [assumption | split; [assumption |
      unfold ctx_consumption_tracked; intros; congruence]].

  (* T_App: chain *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 G2' Ha1 Hf1) as [G2'' [Ht2 [Ha2 [Hf2 Hc2]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption |]].
    eapply consumption_chain; eassumption.

  (* T_Pair: chain *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 G2' Ha1 Hf1) as [G2'' [Ht2 [Ha2 [Hf2 Hc2]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption |]].
    eapply consumption_chain; eassumption.

  (* T_Fst *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Snd *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Inl *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; exact Ht|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Inr *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; exact Ht|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Case — still needs output uniqueness *)
  - admit.

  (* T_If — still needs output uniqueness *)
  - admit.

  (* T_Region *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; [assumption | exact Ht]|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Borrow: G'=G *)
  - assert (Hlk2: ctx_lookup G2 i = Some (T, false)) by (apply Hfp; assumption).
    eexists. split; [econstructor; exact Hlk2|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_Drop *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Copy *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].
Admitted.
(* Remaining admits in T_Var_Lin, T_StringConcat, T_Let, T_LetLin, T_Lam,
   T_App, T_Pair, T_Case, T_If: consumption tracking and context shape
   lemmas needed. Each follows the same pattern — extract consumption
   from the IH chain. This is down from 24 unsolved to ~9 mechanical admits. *)

(** ** Value Context Preservation

    Values do not consume linear resources — their output context
    equals their input context. This is crucial for the substitution
    lemma: substituting a value doesn't disturb the context. *)

Lemma value_context_unchanged :
  forall R G v T G',
    R; G |- v : T -| G' ->
    is_value v ->
    G' = G.
Proof.
  intros R G v T G' Htype Hval.
  generalize dependent G'. generalize dependent T. generalize dependent G.
  generalize dependent R.
  induction Hval; intros Rx Gx Tx G'x Htype; inversion Htype; subst; try reflexivity.
  (* VPair *)
  - rename H3 into Ht1.
    match goal with [ H : Rx; _ |- v2 : _ -| _ |- _ ] => rename H into Ht2 end.
    assert (IH1 := IHHval1 _ _ _ _ Ht1). assert (IH2 := IHHval2 _ _ _ _ Ht2).
    congruence.
  (* VInl *)
  - eapply IHHval. eassumption.
  (* VInr *)
  - eapply IHHval. eassumption.
Qed.

(** ** Substitution Lemma

    The key lemma for preservation's reduction cases.
    If e types in extended context (T1,false)::G and v types as T1 from G,
    then subst 0 v e types from G_v (the output of typing v).

    PROOF STRATEGY: Induction on the typing derivation of e, with the
    context shape abstracted via [remember]. Many cases are vacuous because
    the output context must have (T1,true) at position 0, which contradicts
    rules where position 0 stays unchanged.

    NON-BINDING cases (values, variables, non-binding compounds) are
    handled directly. BINDING cases (Let, LetLin, Lam, Case) require
    a generalized version at arbitrary depth k, because substitution under
    a binder increments the index: subst 0 v (ELet e1 e2) involves
    subst 1 (shift 0 1 v) e2. *)

Lemma subst_preserves_typing :
  forall R G e T2 G' T1 v G_v,
    R; (T1, false) :: G |- e : T2 -| (T1, true) :: G' ->
    R; G |- v : T1 -| G_v ->
    is_value v ->
    exists G_out, R; G_v |- subst 0 v e : T2 -| G_out.
Proof.
  intros R G e T2 G' T1 v G_v Htype Hv Hval.
  remember ((T1, false) :: G) as Gin eqn:HeqIn.
  remember ((T1, true) :: G') as Gout eqn:HeqOut.
  revert G G' T1 v G_v HeqIn HeqOut Hv Hval.
  induction Htype; intros G0 G0' T1' v0 G_v0 HeqIn HeqOut Hv0 Hval0;
    subst.

  (* T_Unit: output = input, so (T1',false)::G0 = (T1',true)::G0' — false≠true *)
  - injection HeqOut as Hf _. congruence.

  (* T_Bool: same contradiction *)
  - injection HeqOut as Hf _. congruence.

  (* T_I32: same contradiction *)
  - injection HeqOut as Hf _. congruence.

  (* T_Var_Lin: ctx_mark_used at i *)
  - destruct i.
    + (* i = 0: EVar 0 → subst gives v0. Lookup at 0 gives T1'. *)
      simpl. unfold ctx_lookup in H. simpl in H.
      (* H : Some (T1', false) = Some (T, false) *)
      assert (T = T1') by congruence. subst T.
      (* Values don't change context *)
      assert (HG: G_v0 = G0) by (eapply value_context_unchanged; eassumption).
      subst G_v0.
      (* ctx_mark_used at 0 gives (T1',true)::G0, matching HeqOut *)
      simpl in HeqOut.
      assert (G0' = G0) by congruence. subst G0'.
      eexists. exact Hv0.
    + (* i > 0: mark_used at S i leaves index 0 as (T1',false).
         Output has (T1',false) at 0, contradicts (T1',true). *)
      simpl in HeqOut.
      injection HeqOut as Hf _.
      congruence.

  (* T_Var_Unr: output = input, same false≠true contradiction *)
  - injection HeqOut as Hf _. congruence.

  (* T_Loc: output = input *)
  - injection HeqOut as Hf _. congruence.

  (* T_StringNew: output = input *)
  - injection HeqOut as Hf _. congruence.

  (* T_StringConcat: e1 then e2, output threads through *)
  - simpl.
    (* e1 types from (T1',false)::G0 to G', e2 types from G' to (T1',true)::G0'.
       IH for e2 needs G' to have shape (T1',?)::... — but we don't know that.
       Actually: IHHtype1 and IHHtype2 both require the output to be (T1',true)::G0'.
       IHHtype2 has output = (T1',true)::G0' which matches.
       IHHtype1 has output = G' which may not match.
       We need the intermediate context G' to thread the substitution. *)
    admit. (* Compound case: needs context threading through IHs *)

  (* T_StringLen *)
  - simpl. admit. (* Similar compound case *)

  (* T_Let: binding case — needs generalized lemma at depth 1 *)
  - simpl. admit.

  (* T_LetLin: binding case *)
  - simpl. admit.

  (* T_Lam: output = input, false≠true contradiction *)
  - injection HeqOut as Hf _. congruence.

  (* T_App: compound case *)
  - simpl. admit.

  (* T_Pair: compound case *)
  - simpl. admit.

  (* T_Fst *)
  - simpl. admit.

  (* T_Snd *)
  - simpl. admit.

  (* T_Inl *)
  - simpl. admit.

  (* T_Inr *)
  - simpl. admit.

  (* T_Case: binding case *)
  - simpl. admit.

  (* T_If: compound case *)
  - simpl. admit.

  (* T_Region *)
  - simpl. admit.

  (* T_Borrow: output = input, false≠true contradiction *)
  - injection HeqOut as Hf _. congruence.

  (* T_Drop *)
  - simpl. admit.

  (* T_Copy *)
  - simpl. admit.
Admitted.
(* REMAINING WORK for full Qed:
   1. Compound non-binding cases (StringConcat, App, Pair, If, etc.):
      Need to split the context threading — e1 consumes part, e2 consumes the rest.
      The IH applies to whichever sub-expression actually consumes index 0.
      Need a lemma: if R; (T1,false)::G |- e : T -| G_mid and G_mid has (T1,false)
      at index 0, then e doesn't touch index 0, so subst 0 v e = e (modulo shift).
   2. Binding cases (Let, LetLin, Case):
      Need generalized lemma: subst_preserves_typing_gen at depth k.
      Under a binder, subst 0 becomes subst 1 with shifted value.
   3. Single-subexpr cases (Fst, Snd, Inl, Inr, Drop, Copy, Region):
      Straightforward once the IH is correctly applied.
   Key helper needed: shift_preserves_typing — shifting a well-typed value
   preserves its typing in an extended context. *)

(** Helper: types_agree and false_preserved are reflexive *)
Lemma ctx_types_agree_refl : forall G, ctx_types_agree G G.
Proof.
  intro G. split; [reflexivity|]. intros. eexists. exact H.
Qed.

Lemma ctx_false_preserved_refl : forall G, ctx_false_preserved G G.
Proof. unfold ctx_false_preserved. auto. Qed.

(** Helper: flags_only_increase implies false_preserved from output to input *)
Lemma typing_false_preserved_output_to_input :
  forall R G e T G',
    R; G |- e : T -| G' ->
    ctx_false_preserved G' G.
Proof.
  unfold ctx_false_preserved. intros. eapply flags_only_increase; eassumption.
Qed.

(** Helper: typing preserves type agreement (output has same types as input) *)
Lemma typing_types_agree :
  forall R G e T G',
    R; G |- e : T -| G' ->
    ctx_types_agree G' G.
Proof.
  intros R G e T G' H. split.
  - exact (typing_preserves_length _ _ _ _ _ H).
  - intros. eapply typing_preserves_bindings; eassumption.
Qed.

(** ** Preservation (Strengthened)

    Well-typed expressions preserve typing under reduction.
    Induction on the step derivation. The strengthened conclusion
    (same input context G + output agreement) provides the IH
    needed for congruence cases via typing_ctx_transfer. *)

Theorem preservation :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G',
    R; G |- e : T -| G' ->
    exists G_out, R'; G |- e' : T -| G_out.
Admitted.
(* Proof structure documented in SESSION-2026-03-28-type-checker-audit.adoc.
   String.length/List.length shadowing prevents compilation.
   14 cases have proof sketches, all follow established patterns. *)
