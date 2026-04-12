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

  (** Borrowing — EBorrow v is a value (VBorrow) when v is a value,
      so there is no S_Borrow_Val reduction rule: EBorrow v is already
      in normal form. S_Borrow_Step reduces the inner expression until
      it becomes a value, at which point EBorrow v is itself a value. *)
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
  1: eapply IHHtype; exact Hlookup. (* T_Region *)
  1: eapply IHHtype; exact Hlookup. (* T_Region_Active *)
  1: eexists; exact Hlookup.
  1: eexists; exact Hlookup. (* T_Borrow_Val: G'=G *)
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

(** ctx_mark_used at position i sets the full lookup to (T, true) when G[i]=(T,_) *)
Lemma ctx_mark_used_lookup_at :
  forall G i T u,
    ctx_lookup G i = Some (T, u) ->
    ctx_lookup (ctx_mark_used G i) i = Some (T, true).
Proof.
  induction G as [|[T0 u0] G' IH]; intros i T u Hlk.
  - unfold ctx_lookup in Hlk. destruct i; discriminate.
  - destruct i; simpl in *.
    + injection Hlk as <- <-. reflexivity.
    + exact (IH i T u Hlk).
Qed.

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

(** True flags stay true under typing: if G[i]=(T0,true) then G'[i]=(T0,true).
    Uses typing_preserves_length, typing_preserves_bindings, flags_only_increase. *)
Lemma true_flag_preserved :
  forall R G e T G' i T0,
    R; G |- e : T -| G' ->
    ctx_lookup G i = Some (T0, true) ->
    ctx_lookup G' i = Some (T0, true).
Proof.
  intros R G e T G' i T0 Htype HiG.
  assert (Hlen : length G' = length G) by (eapply typing_preserves_length; eassumption).
  assert (Hi : i < length G).
  { unfold ctx_lookup in HiG. apply nth_error_Some. congruence. }
  assert (Hex : exists p, ctx_lookup G' i = Some p).
  { unfold ctx_lookup. destruct (nth_error G' i) eqn:E.
    - eexists; reflexivity.
    - apply nth_error_None in E. lia. }
  destruct Hex as [[T0' u'] Hlk].
  destruct (typing_preserves_bindings _ _ _ _ _ Htype _ _ _ Hlk) as [u1 Hu1].
  assert (T0' = T0) by congruence. subst T0'.
  destruct u'; [exact Hlk|].
  exfalso. assert (Hf := flags_only_increase _ _ _ _ _ Htype _ _ Hlk). congruence.
Qed.

(** ** Helpers moved before no_consumption_at_true_linear (2026-04-03)
    These were originally defined after it but are needed in chain case proofs. *)

(** Borrow always preserves context — T_Borrow output = input *)
Lemma borrow_preserves_ctx :
  forall R G e T G', R; G |- EBorrow e : T -| G' -> G' = G.
Proof. intros. inversion H; subst; reflexivity. Qed.

(** StringLen preserves context — its only premise is a borrow *)
Lemma stringlen_preserves_ctx :
  forall R G e T G', R; G |- EStringLen e : T -| G' -> G' = G.
Proof.
  intros. inversion H; subst.
  match goal with [ H0 : context [EBorrow _] |- _ ] =>
    apply borrow_preserves_ctx in H0; exact H0 end.
Qed.

(** Type determinacy: same expression in type-compatible contexts gives same type. *)
Lemma type_determinacy :
  forall R G e T G', R; G |- e : T -| G' ->
    forall G2 T2 G2', R; G2 |- e : T2 -| G2' -> ctx_types_agree G G2 -> T = T2.
Proof.
  intros R G e T G' H1.
  induction H1; intros G2x T2x G2x' H2 Hagree.
  all: inversion H2; subst; try reflexivity.
  all: try (match goal with
    | [ H : ctx_lookup ?G ?i = Some (?T, ?u),
        H3 : ctx_lookup ?G2 ?i = Some (_, _),
        Hagr : ctx_types_agree ?G ?G2 |- _ ] =>
      destruct (proj2 Hagr _ _ _ H) as [? ?]; congruence end).
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
  all: try (match goal with [ IH : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
    first [ eapply IH; eassumption ] end).
  all: try congruence.
  all: try (f_equal; match goal with
    [ IH : context [ctx_types_agree (ctx_extend _ _) _ -> _ = _] |- _ ] =>
      eapply IH; [eassumption|]; apply ctx_extend_types_agree; assumption end).
  all: try (match goal with [ IH : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
    let HTeq := fresh in (assert (HTeq : _ = _) by (eapply IH; eassumption)); congruence end).
  all: try (match goal with
    | [ IH1 : context [ctx_types_agree _ _ -> _ = _],
        IH2 : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
      let HTeq := fresh in
      (assert (HTeq : _ = _) by (eapply IH1; eassumption));
      rewrite <- HTeq in *;
      (eapply IH2; [eassumption|]; eapply typing_preserves_types_agree; eassumption)
    end).
  all: try (match goal with
    | [ IH1 : context [ctx_types_agree _ _ -> TSum _ _ = _] |- _ ] =>
      let HTeq := fresh in (assert (HTeq : TSum _ _ = TSum _ _) by (eapply IH1; eassumption));
      injection HTeq as <- <- end;
      match goal with [ IH : context [ctx_types_agree (ctx_extend _ _) _ -> _ = _] |- _ ] =>
        eapply IH; [eassumption|]; apply ctx_extend_types_agree;
        eapply typing_preserves_types_agree; eassumption end).
  all: try (
    repeat match goal with
    | [ IH : forall (_ : ctx) (_ : ty) (_ : ctx), _ -> ctx_types_agree ?G_ _ -> ?T_ = _,
        Htyp : context [has_type],
        Hagr : ctx_types_agree ?G_ _ |- _ ] =>
      let HTeq := fresh "HTeq" in
      assert (HTeq : T_ = _) by (eapply IH; [exact Htyp | exact Hagr]);
      clear IH; try subst
    | [ IH : forall (_ : ctx) (_ : ty) (_ : ctx), _ -> ctx_types_agree ?G_ _ -> ?T_ = _ |- _ ] =>
      let Hagr := fresh "Hagr" in
      assert (Hagr : ctx_types_agree G_ _) by
        (eapply typing_preserves_types_agree; eassumption);
      let HTeq := fresh "HTeq" in
      assert (HTeq : T_ = _) by (eapply IH; eassumption);
      clear IH; try subst
    end;
    first [ reflexivity | f_equal; congruence | congruence ]).
  (* T_Borrow / T_Borrow_Val cross-cases: EVar is not a value *)
  all: try (exfalso; match goal with
    | [ H : is_value (EVar _) |- _ ] => inversion H end).
  (* T_Borrow_Val vs T_Borrow_Val: use IH *)
  all: try (match goal with
    | [ IH : context [ctx_types_agree _ _ -> _ = _] |- _ ] =>
      f_equal; eapply IH; eassumption end).
Qed.

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
    | ? ? ? ? ? ? IHe1 (* T_Region_Active *)
    | ? ? j0 ? ? (* T_Borrow *)
    | ? ? ? ? ? ? IHe1 (* T_Borrow_Val *)
    | ? ? ? ? ? IHe1 (* T_Drop *)
    | ? ? ? ? ? IHe1 (* T_Copy *)
    ]; intros i T0 Hlin HiG HiG' G2 Hagree HiG2 G2' H2.

  (* Tactic: unify types for two derivations of the same expression in
     type-compatible contexts. Uses type_determinacy then rewrites in the
     SECOND derivation's hypotheses (from inversion), preserving all IHs.
     Leaves HTeq in context for reference. *)
  Local Ltac ncatl_unify_rewrite :=
    repeat match goal with
    | [ He1 : has_type ?R ?G ?e ?T1 _,
        He2 : has_type ?R ?G2 ?e ?T2 _,
        Hagr_ : ctx_types_agree ?G ?G2 |- _ ] =>
      first [ unify T1 T2 |
        let HTeq := fresh "HTeq" in
        pose proof (type_determinacy _ _ _ _ _ He1 _ _ _ He2 Hagr_) as HTeq;
        (* Rewrite compound equality, then decompose via injection.
           Use subst for variable equalities (safe when one side is fresh). *)
        rewrite <- HTeq in *;
        (injection HTeq; clear HTeq; intros; subst) || clear HTeq ]
    end.

  (* Tactic: derive ctx_types_agree for intermediate contexts.
     Requires types to be already unified. *)
  Local Ltac ncatl_mid_agree :=
    match goal with
    | [ He1 : has_type ?R ?G ?e ?T ?Gmid,
        He2 : has_type ?R ?G2 ?e ?T ?G2mid,
        Hagr_ : ctx_types_agree ?G ?G2 |- _ ] =>
      let Hagr' := fresh "Hagr'" in
      pose proof (typing_preserves_types_agree _ _ _ _ _ _ _ He1 He2 Hagr_) as Hagr'
    end.

  (* Tactic: apply the first IH (for the first sub-expression) to derive
     the intermediate false flag. *)
  Local Ltac ncatl_ih1_false :=
    match goal with
    | [ IH1 : forall i_ T0_, is_linear_ty T0_ = true ->
                ctx_lookup ?Gin i_ = Some (T0_, true) -> _,
        HiGx : ctx_lookup ?Gin ?ix = Some (?T0x, true) |- _ ] =>
      let HiG2m := fresh "HiG2m" in
      assert (HiG2m : _ = Some (T0x, false)) by (eapply IH1; eassumption)
    end.

  (* Tactic: apply the remaining IH to close the goal (non-binding case). *)
  Local Ltac ncatl_ih_final :=
    match goal with
    | [ IH : forall i_ T0_, is_linear_ty T0_ = true -> _ -> _ -> _ -> _ -> _ -> _ |- _ ] =>
      eapply IH; eassumption
    end.

  (* 1: T_Unit *)       - inversion H2; subst; exact HiG2.
  (* 2: T_Bool *)       - inversion H2; subst; exact HiG2.
  (* 3: T_I32 *)        - inversion H2; subst; exact HiG2.
  (* 4: T_Var_Lin *)
  - inversion H2; subst.
    + destruct (Nat.eq_dec i j).
      * subst j; rewrite HiG in H; congruence.
      * rewrite ctx_mark_used_lookup_other by (intro; apply n; symmetry; assumption).
        rewrite ctx_mark_used_lookup_other in HiG' by (intro; apply n; symmetry; assumption).
        exact HiG2.
    + exfalso; congruence.
  (* 5: T_Var_Unr *)
  - inversion H2; subst.
    + exfalso; congruence.
    + exact HiG2.
  (* 6: T_Loc *)        - inversion H2; subst; exact HiG2.
  (* 7: T_StringNew *)  - inversion H2; subst; exact HiG2.
  (* 8: T_StringConcat — chain, non-binding *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_ih1_false. ncatl_ih_final.
  (* 9: T_StringLen — borrow preserves context *)
  - inversion H2; subst.
    match goal with
    | [ Hb : has_type _ _ (EBorrow _) _ ?Gout |- ctx_lookup ?Gout _ = _ ] =>
      inversion Hb; subst; exact HiG2
    end.
  (* 10: T_Let — binding chain *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_ih1_false.
    (* The body IH expects ctx_lookup at (S i) in the extended output *)
    match goal with
    | [ H_body : has_type _ _ _ _ (?hd :: G2') |- ctx_lookup G2' i = Some (T0, false) ] =>
      change (ctx_lookup G2' i = Some (T0, false))
        with (ctx_lookup (hd :: G2') (S i) = Some (T0, false))
    end.
    match goal with
    | [ IH2 : forall (x : var), _ |- _ ] =>
      first [
        eapply IH2;
          [exact Hlin | simpl; eassumption | simpl; exact HiG'
          | eapply ctx_extend_types_agree; exact Hagr' | simpl; exact HiG2m | eassumption ]
      | fail 1 ]
    end.
  (* 11: T_LetLin — binding chain *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_ih1_false.
    match goal with
    | [ H_body : has_type _ _ _ _ (?hd :: G2') |- ctx_lookup G2' i = Some (T0, false) ] =>
      change (ctx_lookup G2' i = Some (T0, false))
        with (ctx_lookup (hd :: G2') (S i) = Some (T0, false))
    end.
    match goal with
    | [ IH2 : forall (x : var), _ |- _ ] =>
      first [
        eapply IH2;
          [exact Hlin | simpl; eassumption | simpl; exact HiG'
          | eapply ctx_extend_types_agree; exact Hagr' | simpl; exact HiG2m | eassumption ]
      | fail 1 ]
    end.
  (* 12: T_Lam — identity *)
  - inversion H2; subst; exact HiG2.
  (* 13: T_App — chain, non-binding *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_unify_rewrite. ncatl_ih1_false. ncatl_ih_final.
  (* 14: T_Pair — chain, non-binding *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_ih1_false. ncatl_ih_final.
  (* 15: T_Fst — single IH, needs type unification *)
  - inversion H2; subst. ncatl_unify_rewrite. ncatl_ih_final.
  (* 16: T_Snd — single IH, needs type unification *)
  - inversion H2; subst. ncatl_unify_rewrite. ncatl_ih_final.
  (* 17: T_Inl — single IH *)
  - inversion H2; subst. ncatl_ih_final.
  (* 18: T_Inr — single IH *)
  - inversion H2; subst. ncatl_ih_final.
  (* 19: T_Case — scrutinee + two binding branches *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_unify_rewrite. ncatl_ih1_false.
    (* For Case: after rewriting TSum, standalone type components may differ.
       Find type equality from rewritten hypotheses via type_determinacy on branches,
       then rewrite. *)
    repeat match goal with
    | [ He1 : has_type ?R ?G ?e ?T1 _,
        He2 : has_type ?R ?G2 ?e ?T2 _,
        Hagr_ : ctx_types_agree ?G ?G2 |- _ ] =>
      first [ unify T1 T2 |
        let HTeq := fresh in
        pose proof (type_determinacy _ _ _ _ _ He1 _ _ _ He2 Hagr_) as HTeq;
        rewrite <- HTeq in *; clear HTeq ]
    end.
    (* Now apply binding IH *)
    match goal with
    | [ H_body : has_type _ _ _ _ (?hd :: G2') |- ctx_lookup G2' i = Some (T0, false) ] =>
      change (ctx_lookup G2' i = Some (T0, false))
        with (ctx_lookup (hd :: G2') (S i) = Some (T0, false))
    end.
    match goal with
    | [ IH2 : forall (x : var), _ |- _ ] =>
      first [
        eapply IH2;
          [exact Hlin | simpl; eassumption | simpl; exact HiG'
          | eapply ctx_extend_types_agree; exact Hagr' | simpl; exact HiG2m | eassumption ]
      | fail 1 ]
    end.
  (* 20: T_If — scrutinee + two non-binding branches *)
  - inversion H2; subst.
    assert (Hmid : ctx_lookup G' i = Some (T0, true))
      by (eapply true_flag_preserved; eassumption).
    ncatl_unify_rewrite. ncatl_mid_agree. ncatl_ih1_false. ncatl_ih_final.
  (* 21: T_Region — H1 has ~ In r R; H2 inverts to T_Region (consistent) or
     T_Region_Active (In r R contradicts ~ In r R → exfalso; tauto). *)
  - inversion H2; subst; [ncatl_ih_final | exfalso; tauto].
  (* 22: T_Region_Active — H1 has In r R; H2 inverts to T_Region (~ In r R
     contradicts In r R → exfalso; tauto) or T_Region_Active (consistent). *)
  - inversion H2; subst; [exfalso; tauto | ncatl_ih_final].
  (* 23: T_Borrow — identity *)
  - inversion H2; subst;
      try exact HiG2;
      try (exfalso; match goal with [ H : is_value (EVar _) |- _ ] => inversion H end).
  (* 23: T_Borrow_Val — identity *)
  - inversion H2; subst;
      try exact HiG2;
      try (exfalso; match goal with
        [ Hval : is_value ?v, Heq : EVar _ = ?v |- _ ] =>
          rewrite <- Heq in Hval; inversion Hval end).
  (* 24: T_Drop — single IH, needs type unification *)
  - inversion H2; subst. ncatl_unify_rewrite. ncatl_ih_final.
  (* 25: T_Copy — single IH *)
  - inversion H2; subst. ncatl_ih_final.
Qed.

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

(** Unrestricted bindings are never consumed: if is_linear_ty T0 = false
    then typing preserves the flag at that position unchanged. *)
Lemma unrestricted_flag_unchanged :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall j T0 u,
      is_linear_ty T0 = false ->
      ctx_lookup G j = Some (T0, u) ->
      ctx_lookup G' j = Some (T0, u).
Proof.
  intros R G e T G' Htype.
  induction Htype; intros idx T0 u0 Hnlin Hlk.
  (* T_Unit *)       - exact Hlk.
  (* T_Bool *)       - exact Hlk.
  (* T_I32 *)        - exact Hlk.
  (* T_Var_Lin *)
  - destruct (Nat.eq_dec i idx) as [->|Hne].
    + (* idx = i: T_Var_Lin requires is_linear_ty T = true, but Hlk says
         G[idx] = (T0, u0) with is_linear_ty T0 = false. Since G[i] = (T, false)
         (from H), we have T0 = T and is_linear_ty T = true. Contradiction. *)
      unfold ctx_lookup in *. rewrite H in Hlk.
      injection Hlk as <- <-.
      rewrite Hnlin in H0. discriminate.
    + (* idx <> i: ctx_mark_used doesn't change position idx *)
      rewrite ctx_mark_used_lookup_other by exact Hne.
      exact Hlk.
  (* T_Var_Unr *)    - exact Hlk.
  (* T_Loc *)        - exact Hlk.
  (* T_StringNew *)  - exact Hlk.
  (* T_StringConcat: chain *)
  - eapply IHHtype2. exact Hnlin. eapply IHHtype1. exact Hnlin. exact Hlk.
  (* T_StringLen *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Let: chain through (T1,false)::G' *)
  - apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  (* T_LetLin: chain through (T1,false)::G' *)
  - apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  (* T_Lam: body from (T1,false)::G to (T1,true)::G, output is G *)
  - assert (HlkS: ctx_lookup (ctx_extend G T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  (* T_App: chain *)
  - eapply IHHtype2. exact Hnlin. eapply IHHtype1. exact Hnlin. exact Hlk.
  (* T_Pair: chain *)
  - eapply IHHtype2. exact Hnlin. eapply IHHtype1. exact Hnlin. exact Hlk.
  (* T_Fst *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Snd *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Inl *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Inr *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Case: chain through (T1,false)::G' *)
  - apply (IHHtype1 idx T0 u0 Hnlin) in Hlk.
    assert (HlkS: ctx_lookup (ctx_extend G' T1) (S idx) = Some (T0, u0)) by exact Hlk.
    apply (IHHtype2 (S idx) T0 u0 Hnlin) in HlkS.
    unfold ctx_lookup, ctx_extend in HlkS. simpl in HlkS. exact HlkS.
  (* T_If: chain *)
  - eapply IHHtype2. exact Hnlin. eapply IHHtype1. exact Hnlin. exact Hlk.
  (* T_Region *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Region_Active *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Borrow *)     - exact Hlk.
  (* T_Borrow_Val *)  - exact Hlk.
  (* T_Drop *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
  (* T_Copy *)
  - eapply IHHtype. exact Hnlin. exact Hlk.
Qed.

(** ** Value Context Preservation (moved before typing_ctx_transfer)

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
  (* VBorrow: both T_Borrow and T_Borrow_Val give G'=G, closed by try reflexivity above. *)
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
    (* Consumption tracking for ctx_mark_used: the only position that
       changes false→true is i itself. If G[j]=(T0,false) and
       (ctx_mark_used G i)[j]=(T0,true), then j=i (otherwise the flag
       is unchanged). Since G2[i]=(T0,false), ctx_mark_used G2 i gives true. *)
    unfold ctx_consumption_tracked. intros j T0 Hj_in Hj_out Hj_in2.
    destruct (Nat.eq_dec j i) as [Heq|Hne].
    + subst j.
      (* j = i: ctx_mark_used sets flag to true at position i *)
      eapply ctx_mark_used_lookup_at. exact Hj_in2.
    + (* j ≠ i: ctx_mark_used doesn't change position j, contradiction *)
      exfalso.
      rewrite ctx_mark_used_lookup_other in Hj_out by (intro; apply Hne; symmetry; assumption).
      congruence.

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
    split; [exact Ha_tail|].
    split.
    + (* ctx_false_preserved G'' G2_tail *)
      unfold ctx_false_preserved. intros j T0 Hj.
      assert (HjS: ctx_lookup ((T1, true) :: G'') (S j) = Some (T0, false)).
      { unfold ctx_lookup. simpl. exact Hj. }
      assert (HjS2 := Hf2 (S j) T0 HjS).
      unfold ctx_lookup in HjS2. simpl in HjS2. exact HjS2.
    + (* ctx_consumption_tracked G G'' G2 G2_tail *)
      unfold ctx_consumption_tracked. intros j T0 Hj_in Hj_out Hj_in2.
      (* Chain through G'. Get G'[j] flag. *)
      assert (Hlen1 := typing_preserves_length _ _ _ _ _ Htype1).
      assert (Hlt: j < length G) by (unfold ctx_lookup in Hj_in; apply nth_error_Some; congruence).
      assert (Hlt': j < length G') by lia.
      destruct (nth_error G' j) as [[Tj' uj_mid]|] eqn:EG'.
      * assert (HT0: Tj' = T0).
        { destruct (typing_preserves_bindings _ _ _ _ _ Htype1 j Tj' uj_mid) as [uf Huf].
          { unfold ctx_lookup. exact EG'. }
          rewrite Hj_in in Huf. congruence. }
        subst Tj'.
        destruct uj_mid.
        -- (* G'[j] = (T0, true): consumed in first step.
              Hc1 gives G2'[j] = (T0, true). Then true_flag_preserved on body Ht2
              at shifted index gives G2_tail[j] = (T0, true). *)
           assert (Hg2mid: ctx_lookup G2' j = Some (T0, true)).
           { apply (Hc1 j T0 Hj_in). unfold ctx_lookup. exact EG'. exact Hj_in2. }
           assert (HgS: ctx_lookup ((T1, true) :: G2_tail) (S j) = Some (T0, true)).
           { eapply true_flag_preserved.
             exact Ht2.
             unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           unfold ctx_lookup in HgS. simpl in HgS. exact HgS.
        -- (* G'[j] = (T0, false): not consumed in first step.
              By Hf1: G2'[j] = (T0, false).
              Hc2 at (S j) chains through the body. *)
           assert (Hg2mid: ctx_lookup G2' j = Some (T0, false)).
           { apply (Hf1 j T0). unfold ctx_lookup. exact EG'. }
           assert (HinS: ctx_lookup (ctx_extend G' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact EG'. }
           assert (HoutS: ctx_lookup ((T1, true) :: G'') (S j) = Some (T0, true)).
           { unfold ctx_lookup. simpl. exact Hj_out. }
           assert (Hin2S: ctx_lookup (ctx_extend G2' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           assert (Hout2S := Hc2 (S j) T0 HinS HoutS Hin2S).
           unfold ctx_lookup, ctx_extend in Hout2S. simpl in Hout2S. exact Hout2S.
      * apply nth_error_None in EG'. lia.

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
    split; [exact Ha_tail|].
    split.
    + (* ctx_false_preserved G'' G2_tail *)
      unfold ctx_false_preserved. intros j T0 Hj.
      assert (HjS: ctx_lookup ((T1, true) :: G'') (S j) = Some (T0, false)).
      { unfold ctx_lookup. simpl. exact Hj. }
      assert (HjS2 := Hf2 (S j) T0 HjS).
      unfold ctx_lookup in HjS2. simpl in HjS2. exact HjS2.
    + (* ctx_consumption_tracked G G'' G2 G2_tail *)
      unfold ctx_consumption_tracked. intros j T0 Hj_in Hj_out Hj_in2.
      assert (Hlen1 := typing_preserves_length _ _ _ _ _ Htype1).
      assert (Hlt: j < length G) by (unfold ctx_lookup in Hj_in; apply nth_error_Some; congruence).
      assert (Hlt': j < length G') by lia.
      destruct (nth_error G' j) as [[Tj' uj_mid]|] eqn:EG'.
      * assert (HT0: Tj' = T0).
        { destruct (typing_preserves_bindings _ _ _ _ _ Htype1 j Tj' uj_mid) as [uf Huf].
          { unfold ctx_lookup. exact EG'. }
          rewrite Hj_in in Huf. congruence. }
        subst Tj'.
        destruct uj_mid.
        -- assert (Hg2mid: ctx_lookup G2' j = Some (T0, true)).
           { apply (Hc1 j T0 Hj_in). unfold ctx_lookup. exact EG'. exact Hj_in2. }
           assert (HgS: ctx_lookup ((T1, true) :: G2_tail) (S j) = Some (T0, true)).
           { eapply true_flag_preserved. exact Ht2.
             unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           unfold ctx_lookup in HgS. simpl in HgS. exact HgS.
        -- assert (Hg2mid: ctx_lookup G2' j = Some (T0, false)).
           { apply (Hf1 j T0). unfold ctx_lookup. exact EG'. }
           assert (HinS: ctx_lookup (ctx_extend G' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact EG'. }
           assert (HoutS: ctx_lookup ((T1, true) :: G'') (S j) = Some (T0, true)).
           { unfold ctx_lookup. simpl. exact Hj_out. }
           assert (Hin2S: ctx_lookup (ctx_extend G2' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           assert (Hout2S := Hc2 (S j) T0 HinS HoutS Hin2S).
           unfold ctx_lookup, ctx_extend in Hout2S. simpl in Hout2S. exact Hout2S.
      * apply nth_error_None in EG'. lia.

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
    (* G2_tail = G2: pointwise equality via ctx_eq_from_flags.
       Now closeable with no_consumption_at_true_linear (proved 2026-04-03). *)
    assert (HGeq: G2_tail = G2).
    { apply ctx_eq_from_flags.
      - (* length: Ha_tail gives ctx_types_agree, Hagree gives original agreement *)
        destruct Ha_tail as [Hlen' _]. destruct Hagree as [Hlen _]. lia.
      - intro j. unfold ctx_lookup.
        (* For each position j in G2_tail vs G2:
           Both have the same type (from types_agree).
           Flag: 3 cases based on G[j] and G2[j]. *)
        destruct (nth_error G2_tail j) as [[Tj uj]|] eqn:Etail;
        destruct (nth_error G2 j) as [[Tj' uj']|] eqn:E2.
        + (* Both exist *)
          assert (Tj = Tj').
          { (* Both G2_tail and G2 agree with G on types.
               G[j] must exist (length G = length G2_tail, position j exists in G2_tail). *)
            assert (Hlen_tail := proj1 Ha_tail).
            assert (Hlen_agree := proj1 Hagree).
            destruct (nth_error G j) as [[T_orig u_orig]|] eqn:EG.
            - (* G[j] = (T_orig, u_orig).
                 Ha_tail: G[j]=(T_orig, u_orig) -> G2_tail[j]=(T_orig, ?). So Tj=T_orig.
                 Hagree: G[j]=(T_orig, u_orig) -> G2[j]=(T_orig, ?). So Tj'=T_orig. *)
              destruct (proj2 Ha_tail j T_orig u_orig) as [u1 Hu1].
              { unfold ctx_lookup. exact EG. }
              unfold ctx_lookup in Hu1. rewrite Etail in Hu1.
              injection Hu1 as HTeq1 _. subst T_orig.
              destruct (proj2 Hagree j Tj u_orig) as [u2 Hu2].
              { unfold ctx_lookup. exact EG. }
              unfold ctx_lookup in Hu2. rewrite E2 in Hu2. congruence.
            - exfalso. apply nth_error_None in EG.
              assert (j < length G2_tail) by (apply nth_error_Some; congruence).
              lia. }
          subst Tj'.
          (* uj and uj' must agree *)
          destruct uj, uj'; try reflexivity.
          * (* uj=true, uj'=false: derive contradiction.
               G2_tail[j]=(Tj,true), G2[j]=(Tj,false). *)
            exfalso.
            (* Determine G[j] flag *)
            assert (Hlen_tail := proj1 Ha_tail).
            assert (Hlt: j < length G).
            { assert (j < length G2_tail) by (apply nth_error_Some; congruence). lia. }
            destruct (nth_error G j) as [[T_orig u_orig]|] eqn:EG;
              [|apply nth_error_None in EG; lia].
            assert (HT_orig: T_orig = Tj).
            { destruct (proj2 Hagree j T_orig u_orig) as [u2 Hu2].
              { unfold ctx_lookup. exact EG. }
              unfold ctx_lookup in Hu2. rewrite E2 in Hu2. congruence. }
            subst T_orig.
            destruct u_orig.
            -- (* G[j]=(Tj,true): two sub-cases on linearity *)
               destruct (is_linear_ty Tj) eqn:Hlin.
               ++ (* Tj is linear: use no_consumption_at_true_linear.
                     Original body: (T1,false)::G -> (T1,true)::G.
                     Input G[S j] = (Tj, true), Output G[S j] = (Tj, true).
                     Transferred body: (T1,false)::G2 -> (T1,true)::G2_tail.
                     Input G2[S j] = (Tj, false).
                     no_consumption_at_true_linear gives G2_tail[S j] = (Tj, false).
                     But Etail says G2_tail[j] = (Tj, true). Contradiction. *)
                  assert (Hncatl := no_consumption_at_true_linear _ _ _ _ _
                    _ _ (S j) Tj Htype Ht
                    (ctx_extend_types_agree _ _ _ Hagree)
                    Hlin
                    (EG : ctx_lookup (ctx_extend G T1) (S j) = Some (Tj, true))
                    (EG : ctx_lookup ((T1, true) :: G) (S j) = Some (Tj, true))
                    (E2 : ctx_lookup (ctx_extend G2 T1) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hncatl. simpl in Hncatl.
                  rewrite Etail in Hncatl. congruence.
               ++ (* Tj is unrestricted: use unrestricted_flag_unchanged.
                     Transferred body: (T1,false)::G2 -> (T1,true)::G2_tail.
                     Input at S j: G2[j] = (Tj, false).
                     unrestricted_flag_unchanged gives output at S j: G2_tail[j] = (Tj, false).
                     But Etail says (Tj, true). Contradiction. *)
                  assert (Hufu := unrestricted_flag_unchanged _ _ _ _ _ Ht
                    (S j) Tj false Hlin
                    (E2 : ctx_lookup (ctx_extend G2 T1) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hufu. simpl in Hufu.
                  rewrite Etail in Hufu. congruence.
            -- (* G[j]=(Tj,false): Hf gives G2_tail[j]=(Tj,false), contradicting uj=true. *)
               assert (HfpS := Hf (S j) Tj
                 (EG : ctx_lookup ((T1, true) :: G) (S j) = Some (Tj, false))).
               unfold ctx_lookup in HfpS. simpl in HfpS.
               rewrite Etail in HfpS. congruence.
          * (* uj=false, uj'=true: contradiction via flags_only_increase.
               Body Ht output at S j: G2_tail[j]=(Tj,false).
               flags_only_increase: input at S j must also be false.
               Input: G2[j]=(Tj,false). But E2 says (Tj,true). Contradiction. *)
            exfalso.
            assert (Hfoi := flags_only_increase _ _ _ _ _ Ht (S j) Tj
              (Etail : ctx_lookup ((T1, true) :: G2_tail) (S j) = Some (Tj, false))).
            unfold ctx_lookup, ctx_extend in Hfoi. simpl in Hfoi.
            rewrite E2 in Hfoi. congruence.
        + (* G2_tail exists, G2 doesn't — impossible by length *)
          exfalso.
          assert (Hlen_tail := proj1 Ha_tail).
          assert (Hlen_agree := proj1 Hagree).
          apply nth_error_None in E2.
          assert (j < length G2_tail) by (apply nth_error_Some; congruence). lia.
        + (* G2_tail doesn't exist, G2 does — impossible by length *)
          exfalso.
          assert (Hlen_tail := proj1 Ha_tail).
          assert (Hlen_agree := proj1 Hagree).
          apply nth_error_None in Etail.
          assert (j < length G2) by (apply nth_error_Some; congruence). lia.
        + (* Both don't exist *)
          reflexivity.
    }
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

  (* T_Case — output uniqueness for binding branches. *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 (ctx_extend G2' T1)
                (ctx_extend_types_agree _ _ _ Ha1)
                (ctx_extend_false_preserved _ _ _ Hf1))
      as [G2_e1 [Hte1 [Hae1 [Hfe1 Hce1]]]].
    destruct (IHHtype3 (ctx_extend G2' T2)
                (ctx_extend_types_agree _ _ _ Ha1)
                (ctx_extend_false_preserved _ _ _ Hf1))
      as [G2_e2 [Hte2 [Hae2 [Hfe2 Hce2]]]].
    destruct (types_agree_cons_shape _ _ _ _ Hae1) as [u1 [G2_tail1 [Heq1 Ha_tail1]]].
    subst G2_e1.
    destruct (types_agree_cons_shape _ _ _ _ Hae2) as [u2 [G2_tail2 [Heq2 Ha_tail2]]].
    subst G2_e2.
    (* u1 = true, u2 = true via consumption_tracked at position 0 *)
    assert (Hu1: u1 = true).
    { assert (H0 := Hce1 0 T1 eq_refl eq_refl eq_refl). simpl in H0. congruence. }
    subst u1.
    assert (Hu2: u2 = true).
    { assert (H0 := Hce2 0 T2 eq_refl eq_refl eq_refl). simpl in H0. congruence. }
    subst u2.
    (* G2_tail1 = G2_tail2: pointwise equality *)
    assert (HGeq: G2_tail1 = G2_tail2).
    { apply ctx_eq_from_flags.
      - assert (L1 := proj1 Ha_tail1). assert (L2 := proj1 Ha_tail2). lia.
      - intro j. unfold ctx_lookup.
        destruct (nth_error G2_tail1 j) as [[Tj uj]|] eqn:E_t1;
        destruct (nth_error G2_tail2 j) as [[Tj' uj']|] eqn:E_t2.
        + (* Both exist: types equal, then flags equal *)
          assert (Tj = Tj').
          { assert (Hlen1 := proj1 Ha_tail1). assert (Hlen2 := proj1 Ha_tail2).
            destruct (nth_error G_final j) as [[T_orig u_orig]|] eqn:EGf.
            - destruct (proj2 Ha_tail1 j T_orig u_orig) as [v1 Hv1].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hv1. rewrite E_t1 in Hv1.
              injection Hv1 as HTeq1 _. subst T_orig.
              destruct (proj2 Ha_tail2 j Tj u_orig) as [v2 Hv2].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hv2. rewrite E_t2 in Hv2. congruence.
            - exfalso. apply nth_error_None in EGf.
              assert (j < length G2_tail1) by (apply nth_error_Some; congruence). lia. }
          subst Tj'.
          destruct uj, uj'; try reflexivity.
          * (* uj=true, uj'=false *)
            exfalso.
            (* G2_tail1[j]=(Tj,true), G2_tail2[j]=(Tj,false).
               From flags_only_increase on Hte2 at (S j):
               ((T2,true)::G2_tail2)[S j] = G2_tail2[j] = (Tj,false)
               -> (ctx_extend G2' T2)[S j] = G2'[j] must be (Tj,false). *)
            assert (HG2'_false := flags_only_increase _ _ _ _ _ Hte2 (S j) Tj
              (E_t2 : ctx_lookup ((T2, true) :: G2_tail2) (S j) = Some (Tj, false))).
            unfold ctx_lookup, ctx_extend in HG2'_false. simpl in HG2'_false.
            (* Now HG2'_false: G2'[j] = (Tj, false). Get G'[j]. *)
            assert (Hlen_G' := typing_preserves_length _ _ _ _ _ Htype1).
            assert (Hlen_Gf := typing_preserves_length _ _ _ _ _ Htype2).
            assert (L1 := proj1 Ha_tail1).
            assert (Hlt: j < length G').
            { assert (Hjt: j < length G2_tail1).
              { apply nth_error_Some. congruence. }
              simpl in Hlen_Gf. lia. }
            destruct (nth_error G' j) as [[Tjm um]|] eqn:EG';
              [|apply nth_error_None in EG'; lia].
            assert (HTjm: Tjm = Tj).
            { (* G'[j]=(Tjm,um). Use types_agree G' G2' to get G2'[j]=(Tjm,?).
                 HG2'_false: G2'[j]=(Tj,false). So Tjm=Tj. *)
              destruct (proj2 Ha1 j Tjm um) as [uy Huy].
              { unfold ctx_lookup. exact EG'. }
              unfold ctx_lookup in Huy. rewrite HG2'_false in Huy. congruence. }
            subst Tjm.
            destruct um.
            -- (* G'[j]=(Tj,true): ncatl/ufu gives G2_tail1[j]=false contradiction *)
               (* First derive G_final[j]=(Tj,true) via true_flag_preserved on Htype2 *)
               assert (HGf_true: ctx_lookup ((T1, true) :: G_final) (S j) = Some (Tj, true)).
               { eapply true_flag_preserved. exact Htype2.
                 unfold ctx_lookup, ctx_extend. simpl. exact EG'. }
               destruct (is_linear_ty Tj) eqn:Hlin.
               ++ assert (Hncatl := no_consumption_at_true_linear _ _ _ _ _
                    _ _ (S j) Tj Htype2 Hte1
                    (ctx_extend_types_agree _ _ _ Ha1) Hlin
                    (EG' : ctx_lookup (ctx_extend G' T1) (S j) = Some (Tj, true))
                    HGf_true
                    (HG2'_false : ctx_lookup (ctx_extend G2' T1) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hncatl. simpl in Hncatl. rewrite E_t1 in Hncatl. congruence.
               ++ assert (Hufu := unrestricted_flag_unchanged _ _ _ _ _ Hte1
                    (S j) Tj false Hlin
                    (HG2'_false : ctx_lookup (ctx_extend G2' T1) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hufu. simpl in Hufu. rewrite E_t1 in Hufu. congruence.
            -- (* G'[j]=(Tj,false): case split on G_final[j] flag *)
               assert (Hlen_Gf2 := typing_preserves_length _ _ _ _ _ Htype2).
               assert (Hlt2: j < length G_final).
               { assert (j < length G2_tail1) by (apply nth_error_Some; congruence).
                 simpl in Hlen_Gf2. lia. }
               destruct (nth_error G_final j) as [[Tjf uf]|] eqn:EGf;
                 [|apply nth_error_None in EGf; lia].
               assert (HTjf: Tjf = Tj).
               { destruct (proj2 Ha_tail1 j Tjf uf) as [v Hv].
                 { unfold ctx_lookup. exact EGf. }
                 unfold ctx_lookup in Hv. rewrite E_t1 in Hv. congruence. }
               subst Tjf.
               destruct uf.
               ++ (* G_final[j]=(Tj,true): use Hce2 to derive G2_tail2[j]=true.
                     Then E_t2=(Tj,false) contradicts. *)
                  assert (Hout2 := Hce2 (S j) Tj
                    (EG' : ctx_lookup (ctx_extend G' T2) (S j) = Some (Tj, false))
                    (EGf : ctx_lookup ((T2, true) :: G_final) (S j) = Some (Tj, true))
                    (HG2'_false : ctx_lookup (ctx_extend G2' T2) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hout2. simpl in Hout2. rewrite E_t2 in Hout2. congruence.
               ++ (* G_final[j]=(Tj,false): use Hfe1 to derive G2_tail1[j]=false.
                     Then E_t1=(Tj,true) contradicts. *)
                  assert (HfpS := Hfe1 (S j) Tj
                    (EGf : ctx_lookup ((T1, true) :: G_final) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in HfpS. simpl in HfpS. rewrite E_t1 in HfpS. congruence.
          * (* uj=false, uj'=true: symmetric *)
            exfalso.
            assert (HG2'_false := flags_only_increase _ _ _ _ _ Hte1 (S j) Tj
              (E_t1 : ctx_lookup ((T1, true) :: G2_tail1) (S j) = Some (Tj, false))).
            unfold ctx_lookup, ctx_extend in HG2'_false. simpl in HG2'_false.
            assert (Hlen_G' := typing_preserves_length _ _ _ _ _ Htype1).
            assert (Hlen_Gf := typing_preserves_length _ _ _ _ _ Htype3).
            assert (L2 := proj1 Ha_tail2).
            assert (Hlt: j < length G').
            { assert (Hjt: j < length G2_tail2).
              { apply nth_error_Some. congruence. }
              simpl in Hlen_Gf. lia. }
            destruct (nth_error G' j) as [[Tjm um]|] eqn:EG';
              [|apply nth_error_None in EG'; lia].
            assert (HTjm: Tjm = Tj).
            { destruct (proj2 Ha1 j Tjm um) as [uy Huy].
              { unfold ctx_lookup. exact EG'. }
              unfold ctx_lookup in Huy. rewrite HG2'_false in Huy. congruence. }
            subst Tjm.
            destruct um.
            -- assert (HGf_true: ctx_lookup ((T2, true) :: G_final) (S j) = Some (Tj, true)).
               { eapply true_flag_preserved. exact Htype3.
                 unfold ctx_lookup, ctx_extend. simpl. exact EG'. }
               destruct (is_linear_ty Tj) eqn:Hlin.
               ++ assert (Hncatl := no_consumption_at_true_linear _ _ _ _ _
                    _ _ (S j) Tj Htype3 Hte2
                    (ctx_extend_types_agree _ _ _ Ha1) Hlin
                    (EG' : ctx_lookup (ctx_extend G' T2) (S j) = Some (Tj, true))
                    HGf_true
                    (HG2'_false : ctx_lookup (ctx_extend G2' T2) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hncatl. simpl in Hncatl. rewrite E_t2 in Hncatl. congruence.
               ++ assert (Hufu := unrestricted_flag_unchanged _ _ _ _ _ Hte2
                    (S j) Tj false Hlin
                    (HG2'_false : ctx_lookup (ctx_extend G2' T2) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hufu. simpl in Hufu. rewrite E_t2 in Hufu. congruence.
            -- (* G'[j]=(Tj,false): case split on G_final[j] flag *)
               assert (Hlen_Gf2 := typing_preserves_length _ _ _ _ _ Htype3).
               assert (Hlt2: j < length G_final).
               { assert (j < length G2_tail2) by (apply nth_error_Some; congruence).
                 simpl in Hlen_Gf2. lia. }
               destruct (nth_error G_final j) as [[Tjf uf]|] eqn:EGf;
                 [|apply nth_error_None in EGf; lia].
               assert (HTjf: Tjf = Tj).
               { destruct (proj2 Ha_tail2 j Tjf uf) as [v Hv].
                 { unfold ctx_lookup. exact EGf. }
                 unfold ctx_lookup in Hv. rewrite E_t2 in Hv. congruence. }
               subst Tjf.
               destruct uf.
               ++ (* G_final[j]=(Tj,true): use Hce1 to derive G2_tail1[j]=true.
                     Then E_t1=(Tj,false) contradicts. *)
                  assert (Hout1 := Hce1 (S j) Tj
                    (EG' : ctx_lookup (ctx_extend G' T1) (S j) = Some (Tj, false))
                    (EGf : ctx_lookup ((T1, true) :: G_final) (S j) = Some (Tj, true))
                    (HG2'_false : ctx_lookup (ctx_extend G2' T1) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in Hout1. simpl in Hout1. rewrite E_t1 in Hout1. congruence.
               ++ (* G_final[j]=(Tj,false): use Hfe2 to derive G2_tail2[j]=false.
                     Then E_t2=(Tj,true) contradicts. *)
                  assert (HfpS := Hfe2 (S j) Tj
                    (EGf : ctx_lookup ((T2, true) :: G_final) (S j) = Some (Tj, false))).
                  unfold ctx_lookup in HfpS. simpl in HfpS. rewrite E_t2 in HfpS. congruence.
        + (* G2_tail1 exists, G2_tail2 doesn't *)
          exfalso. apply nth_error_None in E_t2.
          assert (j < length G2_tail1) by (apply nth_error_Some; congruence).
          assert (L1 := proj1 Ha_tail1). assert (L2 := proj1 Ha_tail2). lia.
        + (* G2_tail1 doesn't exist, G2_tail2 does *)
          exfalso. apply nth_error_None in E_t1.
          assert (j < length G2_tail2) by (apply nth_error_Some; congruence).
          assert (L1 := proj1 Ha_tail1). assert (L2 := proj1 Ha_tail2). lia.
        + (* Both don't exist *)
          reflexivity.
    }
    subst G2_tail2.
    eexists. split; [eapply T_Case; eassumption|].
    split; [exact Ha_tail1|].
    split.
    + (* ctx_false_preserved G_final G2_tail1: from Hfe1 at shifted indices *)
      unfold ctx_false_preserved. intros j T0 Hj.
      assert (HjS := Hfe1 (S j) T0
        (Hj : ctx_lookup ((T1, true) :: G_final) (S j) = Some (T0, false))).
      unfold ctx_lookup in HjS. simpl in HjS. exact HjS.
    + (* ctx_consumption_tracked G G_final G2 G2_tail1: chain through G' *)
      unfold ctx_consumption_tracked. intros j T0 Hj_in Hj_out Hj_in2.
      assert (Hlen1 := typing_preserves_length _ _ _ _ _ Htype1).
      assert (Hlt: j < length G) by (unfold ctx_lookup in Hj_in; apply nth_error_Some; congruence).
      assert (Hlt': j < length G') by lia.
      destruct (nth_error G' j) as [[Tj' uj_mid]|] eqn:EG'.
      * assert (HT0: Tj' = T0).
        { destruct (typing_preserves_bindings _ _ _ _ _ Htype1 j Tj' uj_mid) as [uf Huf].
          { unfold ctx_lookup. exact EG'. }
          rewrite Hj_in in Huf. congruence. }
        subst Tj'.
        destruct uj_mid.
        -- (* G'[j] = (T0, true): consumed in first step *)
           assert (Hg2mid: ctx_lookup G2' j = Some (T0, true)).
           { apply (Hc1 j T0 Hj_in). unfold ctx_lookup. exact EG'. exact Hj_in2. }
           (* true_flag_preserved on Hte1 at shifted index *)
           assert (HgS: ctx_lookup ((T1, true) :: G2_tail1) (S j) = Some (T0, true)).
           { eapply true_flag_preserved. exact Hte1.
             unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           unfold ctx_lookup in HgS. simpl in HgS. exact HgS.
        -- (* G'[j] = (T0, false): not consumed in first step *)
           assert (Hg2mid: ctx_lookup G2' j = Some (T0, false)).
           { apply (Hf1 j T0). unfold ctx_lookup. exact EG'. }
           (* Hce1 at (S j) *)
           assert (HinS: ctx_lookup (ctx_extend G' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact EG'. }
           assert (HoutS: ctx_lookup ((T1, true) :: G_final) (S j) = Some (T0, true)).
           { unfold ctx_lookup. simpl. exact Hj_out. }
           assert (Hin2S: ctx_lookup (ctx_extend G2' T1) (S j) = Some (T0, false)).
           { unfold ctx_lookup, ctx_extend. simpl. exact Hg2mid. }
           assert (Hout2S := Hce1 (S j) T0 HinS HoutS Hin2S).
           unfold ctx_lookup in Hout2S. simpl in Hout2S. exact Hout2S.
      * apply nth_error_None in EG'. lia.

  (* T_If — output uniqueness: both branches from G2' give same output. *)
  - destruct (IHHtype1 G2 Hagree Hfp) as [G2' [Ht1 [Ha1 [Hf1 Hc1]]]].
    destruct (IHHtype2 G2' Ha1 Hf1) as [G2_e2 [Ht2 [Ha2 [Hf2 Hc2]]]].
    destruct (IHHtype3 G2' Ha1 Hf1) as [G2_e3 [Ht3 [Ha3 [Hf3 Hc3]]]].
    (* Show G2_e2 = G2_e3 *)
    assert (HGeq: G2_e2 = G2_e3).
    { apply ctx_eq_from_flags.
      - (* length *)
        assert (L2 := proj1 Ha2). assert (L3 := proj1 Ha3). lia.
      - intro j. unfold ctx_lookup.
        destruct (nth_error G2_e2 j) as [[Tj uj]|] eqn:E_e2;
        destruct (nth_error G2_e3 j) as [[Tj' uj']|] eqn:E_e3.
        + (* Both exist: show types equal, then flags equal *)
          assert (Tj = Tj').
          { (* Both agree with G'' on types. G''[j] must exist. *)
            assert (Hlen2 := proj1 Ha2). assert (Hlen3 := proj1 Ha3).
            destruct (nth_error G'' j) as [[T_orig u_orig]|] eqn:EGf.
            - destruct (proj2 Ha2 j T_orig u_orig) as [u1 Hu1].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hu1. rewrite E_e2 in Hu1.
              injection Hu1 as HTeq1 _. subst T_orig.
              destruct (proj2 Ha3 j Tj u_orig) as [u2 Hu2].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hu2. rewrite E_e3 in Hu2. congruence.
            - exfalso. apply nth_error_None in EGf.
              assert (j < length G2_e2) by (apply nth_error_Some; congruence). lia. }
          subst Tj'.
          destruct uj, uj'; try reflexivity.
          * (* uj=true, uj'=false *)
            exfalso.
            (* G2_e2[j]=(Tj,true), G2_e3[j]=(Tj,false).
               flags_only_increase on Ht3: G2_e3[j]=(Tj,false) -> G2'[j]=(Tj,false).
               Then flags_only_increase on Ht2: if G2_e2[j]=false then G2'[j]=false.
               But we need the contradiction the other way.
               Actually: if G2'[j]=(Tj,false), then by Hf2: G''[j]=(Tj,false) -> G2_e2[j]=(Tj,false).
               Wait, Hf2 goes from G'' to G2_e2. If G''[j]=(Tj,false) then G2_e2[j]=(Tj,false). That contradicts uj=true.
               If G''[j]=(Tj,true): then by Hf3: doesn't apply.
               Need a different approach. *)
            (* From G2_e3[j]=(Tj,false): by flags_only_increase on Ht3,
               G2'[j]=(Tj,false). *)
            assert (HG2'_false := flags_only_increase _ _ _ _ _ Ht3 j Tj
              (E_e3 : ctx_lookup G2_e3 j = Some (Tj, false))).
            (* From G2'[j]=(Tj,false):
               Case on G''[j] flag: *)
            assert (Hlen2 := proj1 Ha2).
            assert (Hlt: j < length G'').
            { assert (j < length G2_e2) by (apply nth_error_Some; congruence). lia. }
            destruct (nth_error G'' j) as [[Tjf uf]|] eqn:EGf;
              [|apply nth_error_None in EGf; lia].
            assert (HTjf: Tjf = Tj).
            { destruct (proj2 Ha2 j Tjf uf) as [u1 Hu1].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hu1. rewrite E_e2 in Hu1. congruence. }
            subst Tjf.
            destruct uf.
            -- (* G''[j]=(Tj,true), G'[j] must be determined.
                  G''[j]=(Tj,true) and G'[j]=(Tj,false) (from flags_only_increase on Htype2).
                  Wait — we don't have Htype2 directly, but we have Ht2 and the original.
                  Use Hc2: consumption_tracked G' G'' G2' G2_e2.
                  G'[j]=(Tj,?) and G''[j]=(Tj,true).
                  If G'[j]=(Tj,false): Hc2 says G2'[j]=(Tj,false)->G2_e2[j]=(Tj,true). OK.
                  If G'[j]=(Tj,true): true_flag_preserved on Htype2: G''[j]=(Tj,true). OK.
                  For G2_e3: if G'[j]=(Tj,false): Hc3 says G2'[j]=(Tj,false)->G2_e3[j]=(Tj,true). But E_e3 says false. Contradiction!
                  If G'[j]=(Tj,true): by true_flag_preserved on Ht3, G2_e3[j]=(Tj,true). But E_e3 says false. Contradiction! *)
               assert (Hlen_G' := typing_preserves_length _ _ _ _ _ Htype1).
               assert (Hlen_G'' := typing_preserves_length _ _ _ _ _ Htype2).
               assert (Hlt': j < length G').
               { assert (j < length G2_e2) by (apply nth_error_Some; congruence). lia. }
               destruct (nth_error G' j) as [[Tjm um]|] eqn:EG';
                 [|apply nth_error_None in EG'; lia].
               assert (HTjm: Tjm = Tj).
               { destruct (typing_preserves_bindings _ _ _ _ _ Htype2 j Tj true) as [ux Hux].
                 { unfold ctx_lookup. exact EGf. }
                 unfold ctx_lookup in Hux. rewrite EG' in Hux. congruence. }
               subst Tjm.
               destruct um.
               ++ (* G'[j]=(Tj,true): true_flag_preserved on Ht3.
                     But we need G2'[j]=(Tj,true), not G'[j]. *)
                  (* G'[j]=(Tj,true) and G2'[j]=(Tj,false) from HG2'_false.
                     But Ha1: ctx_types_agree G' G2'. So types match.
                     flags_only_increase on Ht2: G2_e2[j]=true means input could be anything.
                     Actually, if G'[j]=true, by Hf1: G'[j]=true doesn't apply (Hf1 is false_preserved).
                     But we can use the fact that G'[j]=(Tj,true) implies through Hc3:
                     Since G'[j]=(Tj,true) = input for branch3, but output is G''[j]=(Tj,true).
                     true_flag_preserved on Htype3 at j: G'[j]=(Tj,true) -> G''[j]=(Tj,true). Consistent.
                     For G2': G2'[j]=(Tj,false) from HG2'_false.
                     Hc3: G'[j]=(Tj,false)? No, G'[j]=(Tj,true). So consumption_tracked doesn't apply.
                     unrestricted_flag_unchanged on Ht3: if Tj is unrestricted, G2'[j]=false -> G2_e3[j]=false. Matches E_e3.
                     no_consumption_at_true_linear: G'[j]=true, G''[j]=true, G2'[j]=false -> G2_e3[j]=false. Matches E_e3.
                     But same for Ht2: if Tj is unrestricted, G2'[j]=false -> G2_e2[j]=false. But E_e2 says true!
                     And ncatl: G'[j]=true, G''[j]=true, G2'[j]=false -> G2_e2[j]=false. But E_e2 says true!
                     So actually this case is a contradiction!
                     Use no_consumption_at_true_linear if linear, or unrestricted_flag_unchanged if not. *)
                  destruct (is_linear_ty Tj) eqn:Hlin.
                  ** assert (Hncatl := no_consumption_at_true_linear _ _ _ _ _
                       _ _ j Tj Htype2 Ht2 Ha1 Hlin
                       (EG' : ctx_lookup G' j = Some (Tj, true))
                       (EGf : ctx_lookup G'' j = Some (Tj, true))
                       HG2'_false).
                     unfold ctx_lookup in Hncatl. rewrite E_e2 in Hncatl. congruence.
                  ** assert (Hufu := unrestricted_flag_unchanged _ _ _ _ _ Ht2 j Tj false Hlin HG2'_false).
                     unfold ctx_lookup in Hufu. rewrite E_e2 in Hufu. congruence.
               ++ (* G'[j]=(Tj,false): Hc3 gives G2_e3[j]=true. Contradiction with E_e3. *)
                  assert (H3out := Hc3 j Tj
                    (EG' : ctx_lookup G' j = Some (Tj, false))
                    (EGf : ctx_lookup G'' j = Some (Tj, true))
                    HG2'_false).
                  unfold ctx_lookup in H3out. rewrite E_e3 in H3out. congruence.
            -- (* G''[j]=(Tj,false): by Hf2: G2_e2[j]=(Tj,false). But uj=true. Contradiction. *)
               assert (Hfp2 := Hf2 j Tj (EGf : ctx_lookup G'' j = Some (Tj, false))).
               unfold ctx_lookup in Hfp2. rewrite E_e2 in Hfp2. congruence.
          * (* uj=false, uj'=true: symmetric to above *)
            exfalso.
            assert (HG2'_false := flags_only_increase _ _ _ _ _ Ht2 j Tj
              (E_e2 : ctx_lookup G2_e2 j = Some (Tj, false))).
            assert (Hlen3 := proj1 Ha3).
            assert (Hlt: j < length G'').
            { assert (j < length G2_e3) by (apply nth_error_Some; congruence). lia. }
            destruct (nth_error G'' j) as [[Tjf uf]|] eqn:EGf;
              [|apply nth_error_None in EGf; lia].
            assert (HTjf: Tjf = Tj).
            { destruct (proj2 Ha3 j Tjf uf) as [u1 Hu1].
              { unfold ctx_lookup. exact EGf. }
              unfold ctx_lookup in Hu1. rewrite E_e3 in Hu1. congruence. }
            subst Tjf.
            destruct uf.
            -- assert (Hlen_G' := typing_preserves_length _ _ _ _ _ Htype1).
               assert (Hlen_G'' := typing_preserves_length _ _ _ _ _ Htype2).
               assert (Hlt': j < length G').
               { assert (j < length G2_e2) by (apply nth_error_Some; congruence). lia. }
               destruct (nth_error G' j) as [[Tjm um]|] eqn:EG';
                 [|apply nth_error_None in EG'; lia].
               assert (HTjm: Tjm = Tj).
               { destruct (typing_preserves_bindings _ _ _ _ _ Htype2 j Tj true) as [ux Hux].
                 { unfold ctx_lookup. exact EGf. }
                 unfold ctx_lookup in Hux. rewrite EG' in Hux. congruence. }
               subst Tjm.
               destruct um.
               ++ (* G'[j]=(Tj,true), G2'[j]=(Tj,false): contradiction via ncatl/ufu on Ht3 *)
                  destruct (is_linear_ty Tj) eqn:Hlin.
                  ** assert (Hncatl := no_consumption_at_true_linear _ _ _ _ _
                       _ _ j Tj Htype3 Ht3 Ha1 Hlin
                       (EG' : ctx_lookup G' j = Some (Tj, true))
                       (EGf : ctx_lookup G'' j = Some (Tj, true))
                       HG2'_false).
                     unfold ctx_lookup in Hncatl. rewrite E_e3 in Hncatl. congruence.
                  ** assert (Hufu := unrestricted_flag_unchanged _ _ _ _ _ Ht3 j Tj false Hlin HG2'_false).
                     unfold ctx_lookup in Hufu. rewrite E_e3 in Hufu. congruence.
               ++ (* G'[j]=(Tj,false): Hc2 gives G2_e2[j]=true. Contradiction with E_e2. *)
                  assert (H2out := Hc2 j Tj
                    (EG' : ctx_lookup G' j = Some (Tj, false))
                    (EGf : ctx_lookup G'' j = Some (Tj, true))
                    HG2'_false).
                  unfold ctx_lookup in H2out. rewrite E_e2 in H2out. congruence.
            -- assert (Hfp3 := Hf3 j Tj (EGf : ctx_lookup G'' j = Some (Tj, false))).
               unfold ctx_lookup in Hfp3. rewrite E_e3 in Hfp3. congruence.
        + (* G2_e2 exists, G2_e3 doesn't *)
          exfalso. apply nth_error_None in E_e3.
          assert (j < length G2_e2) by (apply nth_error_Some; congruence).
          assert (L2 := proj1 Ha2). assert (L3 := proj1 Ha3). lia.
        + (* G2_e2 doesn't exist, G2_e3 does *)
          exfalso. apply nth_error_None in E_e2.
          assert (j < length G2_e3) by (apply nth_error_Some; congruence).
          assert (L2 := proj1 Ha2). assert (L3 := proj1 Ha3). lia.
        + (* Both don't exist *)
          reflexivity.
    }
    subst G2_e3.
    eexists. split; [eapply T_If; eassumption|].
    split; [exact Ha2 | split; [exact Hf2 |]].
    eapply consumption_chain; eassumption.

  (* T_Region *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; [assumption | exact Ht]|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Region_Active: same structure, uses T_Region_Active in conclusion *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [eapply T_Region_Active; [assumption | exact Ht]|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Borrow: G'=G *)
  - assert (Hlk2: ctx_lookup G2 i = Some (T, false)) by (apply Hfp; assumption).
    eexists. split; [econstructor; exact Hlk2|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_Borrow_Val: G'=G, use IH to transfer sub-value typing *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    (* G2' = G2: value doesn't change context *)
    assert (HG2'eq: G2' = G2).
    { eapply value_context_unchanged; eassumption. }
    subst G2'.
    eexists. split; [eapply T_Borrow_Val; eassumption|].
    split; [assumption | split; [assumption | unfold ctx_consumption_tracked; intros; congruence]].

  (* T_Drop *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Copy *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [econstructor; eassumption|].
    split; [assumption | split; [assumption | exact Hc]].
Qed.
(* PROOF OBLIGATION [typing_ctx_transfer] — all 24 cases proved (2026-04-04).
   Key helpers: no_consumption_at_true_linear, unrestricted_flag_unchanged,
   flags_only_increase, true_flag_preserved, consumption_chain.
   T_Lam: output uniqueness via ctx_eq_from_flags + ncatl/ufu.
   T_Case: output uniqueness with binding branches + consumption chaining.
   T_If: output uniqueness with non-binding branches. *)

(** ** Substitution Lemma

    The key lemma for preservation's reduction cases.
    If e types in extended context (T1,false)::G and v types as T1 from G,
    then subst 0 v e types from G_v (the output of typing v).

    PROOF STRATEGY: Induction on the typing derivation of e, with a
    strengthened conclusion that covers both the "consumed" (false->true)
    and "not consumed" (false->false) output flag cases. The IH for the
    typing derivation provides substitution at depth 0. For binding cases,
    substitution at depth 1 is handled using typing_ctx_transfer on the
    original (unsubstituted) body, combined with the depth-0 IH. *)

(** Helper: get intermediate context shape from typing_preserves_length
    and typing_preserves_bindings. If input is (T1,u)::G, output has
    the same length, so output = (T1_out, u_out) :: G_tail for some
    T1_out, u_out, G_tail with T1_out = T1. *)
Lemma output_head_shape :
  forall R T1 u G e T Gout,
    R; (T1, u) :: G |- e : T -| Gout ->
    exists u_out G_tail, Gout = (T1, u_out) :: G_tail.
Proof.
  intros R T1 u G e T Gout Htype.
  assert (Hlen := typing_preserves_length _ _ _ _ _ Htype).
  simpl in Hlen.
  destruct Gout as [|[T1' u'] Gout'].
  - simpl in Hlen. lia.
  - assert (T1' = T1).
    { destruct (typing_preserves_bindings _ _ _ _ _ Htype 0 T1' u') as [u1 Hu1].
      { reflexivity. }
      simpl in Hu1. congruence. }
    subst T1'. eexists _, _. reflexivity.
Qed.

(** ** Generalized Shift-Typing

    Shifting a well-typed expression preserves typing when we insert
    a fresh binding at position k in the context. *)

(** Insert element at position k in a list *)
Fixpoint insert_at {A : Type} (k : nat) (x : A) (l : list A) : list A :=
  match k, l with
  | 0, _ => x :: l
  | S k', [] => [x]
  | S k', h :: t => h :: insert_at k' x t
  end.

Lemma nth_error_insert_at_lt :
  forall {A} k j (x : A) l,
    j < k -> k <= length l -> nth_error (insert_at k x l) j = nth_error l j.
Proof.
  induction k; intros j x l Hlt Hle; [lia|].
  destruct l as [|h t]; [simpl in Hle; lia|].
  destruct j; simpl; [reflexivity|].
  apply IHk; [lia | simpl in Hle; lia].
Qed.

Lemma nth_error_insert_at_eq :
  forall {A} k (x : A) l,
    k <= length l ->
    nth_error (insert_at k x l) k = Some x.
Proof.
  induction k; intros x l Hle; simpl.
  - reflexivity.
  - destruct l; simpl in *; [lia|].
    apply IHk. lia.
Qed.

Lemma nth_error_insert_at_gt :
  forall {A} k j (x : A) l,
    k <= j -> k <= length l -> nth_error (insert_at k x l) (S j) = nth_error l j.
Proof.
  induction k; intros j x l Hle Hle2; simpl.
  - reflexivity.
  - destruct l as [|h t]; [simpl in Hle2; lia|].
    destruct j; [lia|].
    simpl. apply IHk; [lia | simpl in Hle2; lia].
Qed.

Lemma insert_at_length :
  forall {A} k (x : A) l,
    k <= length l ->
    length (insert_at k x l) = S (length l).
Proof.
  induction k; intros x l Hle; simpl.
  - simpl. reflexivity.
  - destruct l; simpl in *; [lia|].
    f_equal. apply IHk. lia.
Qed.

Lemma insert_at_zero : forall {A} (x : A) l, insert_at 0 x l = x :: l.
Proof. reflexivity. Qed.

Lemma insert_at_succ_cons :
  forall {A} k (x h : A) t, insert_at (S k) x (h :: t) = h :: insert_at k x t.
Proof. reflexivity. Qed.

(** ctx_mark_used commutes with insert_at (with length guard) *)
Lemma insert_at_ctx_mark_used_lt :
  forall G k i entry,
    i < k -> k <= length G ->
    insert_at k entry (ctx_mark_used G i) = ctx_mark_used (insert_at k entry G) i.
Proof.
  induction G as [|[T u] G' IH]; intros k i entry Hlt Hle.
  - simpl in Hle. lia.
  - destruct i; destruct k; try lia; simpl.
    + reflexivity.
    + f_equal. apply IH; [lia | simpl in Hle; lia].
Qed.

Lemma insert_at_ctx_mark_used_ge :
  forall G k i entry,
    k <= i -> k <= length G ->
    insert_at k entry (ctx_mark_used G i) = ctx_mark_used (insert_at k entry G) (S i).
Proof.
  induction G as [|[T u] G' IH]; intros k i [Te ue] Hle Hle2.
  - simpl in Hle2. assert (k = 0) by lia. subst k.
    simpl. destruct i; reflexivity.
  - destruct k; simpl.
    + reflexivity.
    + destruct i; [lia|]. simpl. f_equal. apply IH; [lia | simpl in Hle2; lia].
Qed.

(** Generalized shift-typing: shifting by 1 at cutoff k inserts a
    fresh binding (T_new, false) at position k in both input and output *)
Lemma shift_typing_gen :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall k T_new,
      k <= length G ->
      R; insert_at k (T_new, false) G |- shift k 1 e : T -| insert_at k (T_new, false) G'.
Proof.
  intros R G e T G' Htype.
  induction Htype; intros k T_new Hk; simpl.

  (* T_Unit *) - constructor.
  (* T_Bool *) - constructor.
  (* T_I32 *)  - constructor.

  (* T_Var_Lin *)
  - destruct (Nat.leb_spec k i).
    + (* k <= i: shifted to i+1 *)
      rewrite (insert_at_ctx_mark_used_ge G k i (T_new, false) H1 Hk).
      replace (i + 1) with (S i) by lia.
      econstructor.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
    + (* i < k: unchanged *)
      rewrite (insert_at_ctx_mark_used_lt G k i (T_new, false) H1 Hk).
      econstructor.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.

  (* T_Var_Unr: output = G, insert_at commutes trivially *)
  - destruct (Nat.leb_spec k i).
    + replace (i + 1) with (S i) by lia.
      econstructor.
      * unfold ctx_lookup. rewrite nth_error_insert_at_gt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.
    + econstructor.
      * unfold ctx_lookup. rewrite nth_error_insert_at_lt by (try assumption; try lia).
        unfold ctx_lookup in H. exact H.
      * exact H0.

  (* T_Loc *) - constructor. assumption.
  (* T_StringNew *) - constructor. assumption.

  (* T_StringConcat *)
  - econstructor.
    + apply IHHtype1. assumption.
    + apply IHHtype2.
      assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1). lia.

  (* T_StringLen *)
  - econstructor. apply IHHtype. assumption.

  (* T_Let *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2.
    eapply T_Let; eassumption.

  (* T_LetLin *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2.
    eapply T_LetLin; eassumption.

  (* T_Lam *)
  - assert (IH := IHHtype (S k) T_new ltac:(simpl; lia)).
    simpl in IH.
    eapply T_Lam. exact IH.

  (* T_App *)
  - econstructor.
    + apply IHHtype1. assumption.
    + apply IHHtype2.
      assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1). lia.

  (* T_Pair *)
  - econstructor.
    + apply IHHtype1. assumption.
    + apply IHHtype2.
      assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1). lia.

  (* T_Fst *)
  - econstructor.
    + apply IHHtype. assumption.
    + assumption.

  (* T_Snd *)
  - econstructor.
    + apply IHHtype. assumption.
    + assumption.

  (* T_Inl *)
  - econstructor. apply IHHtype. assumption.

  (* T_Inr *)
  - econstructor. apply IHHtype. assumption.

  (* T_Case *)
  - assert (IH1 := IHHtype1 k T_new Hk).
    assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1).
    assert (IH2 := IHHtype2 (S k) T_new ltac:(simpl; lia)).
    assert (IH3 := IHHtype3 (S k) T_new ltac:(simpl; lia)).
    simpl in IH2, IH3.
    eapply T_Case; eassumption.

  (* T_If *)
  - econstructor.
    + apply IHHtype1. assumption.
    + apply IHHtype2.
      assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1). lia.
    + apply IHHtype3.
      assert (Hlen := typing_preserves_length _ _ _ _ _ Htype1). lia.

  (* T_Region *)
  - econstructor.
    + assumption.
    + apply IHHtype. assumption.

  (* T_Region_Active *)
  - eapply T_Region_Active.
    + assumption.
    + apply IHHtype. assumption.

  (* T_Borrow *)
  - destruct (Nat.leb_spec k i).
    + replace (i + 1) with (S i) by lia.
      econstructor. unfold ctx_lookup.
      rewrite nth_error_insert_at_gt by (try assumption; try lia).
      unfold ctx_lookup in H. exact H.
    + econstructor. unfold ctx_lookup.
      rewrite nth_error_insert_at_lt by (try assumption; try lia).
      unfold ctx_lookup in H. exact H.

  (* T_Borrow_Val *)
  - eapply T_Borrow_Val.
    + (* shift preserves values — inline proof *)
      clear IHHtype. clear Htype.
      induction H; simpl; constructor; auto.
    + apply IHHtype. assumption.

  (* T_Drop *)
  - eapply T_Drop.
    + eassumption.
    + apply IHHtype. assumption.

  (* T_Copy *)
  - eapply T_Copy.
    + eassumption.
    + apply IHHtype. assumption.
Qed.

(** Corollary: shift 0 1 inserts at position 0 *)
Lemma shift_typing_zero :
  forall R G e T G' T_new,
    R; G |- e : T -| G' ->
    R; (T_new, false) :: G |- shift 0 1 e : T -| (T_new, false) :: G'.
Proof.
  intros. apply (shift_typing_gen _ _ _ _ _ H 0). lia.
Qed.

(** ** Generalized Depth-k Substitution Lemma

    For any position k in the context, substitution at depth k
    preserves typing. The output context is obtained by removing
    position k from the original output. *)

(** remove_at definition and helpers *)
Fixpoint remove_at {A : Type} (k : nat) (l : list A) : list A :=
  match l, k with
  | [], _ => []
  | _ :: l', 0 => l'
  | x :: l', S k' => x :: remove_at k' l'
  end.

Lemma remove_at_length :
  forall {A} k (l : list A),
    k < length l ->
    length (remove_at k l) = length l - 1.
Proof.
  intros A k. induction k; intros l Hlt.
  - destruct l; [simpl in Hlt; lia | simpl; lia].
  - destruct l as [|x l']; [simpl in Hlt; lia|].
    simpl. simpl in Hlt. rewrite IHk by lia. simpl. lia.
Qed.

Lemma nth_error_remove_at_lt :
  forall {A} k j (l : list A),
    j < k -> nth_error (remove_at k l) j = nth_error l j.
Proof.
  intros A k. induction k; intros j l Hlt; [lia|].
  destruct l as [|x l']; [destruct j; reflexivity|].
  destruct j; [reflexivity|].
  simpl. apply IHk. lia.
Qed.

Lemma nth_error_remove_at_ge :
  forall {A} k j (l : list A),
    k <= j -> nth_error (remove_at k l) j = nth_error l (S j).
Proof.
  intros A k. induction k; intros j l Hle.
  - destruct l; [destruct j; reflexivity | simpl; reflexivity].
  - destruct l as [|x l']; [destruct j; reflexivity|].
    destruct j; [lia|].
    simpl. apply IHk. lia.
Qed.

Lemma remove_at_ctx_mark_used_lt :
  forall G k i,
    i < k ->
    remove_at k (ctx_mark_used G i) = ctx_mark_used (remove_at k G) i.
Proof.
  induction G as [|[T u] G' IH]; intros k i Hlt.
  - destruct k; destruct i; reflexivity.
  - destruct k; [lia|]. destruct i; simpl.
    + reflexivity.
    + f_equal. apply IH. lia.
Qed.

Lemma remove_at_ctx_mark_used_gt :
  forall G k j,
    k <= j ->
    remove_at k (ctx_mark_used G (S j)) = ctx_mark_used (remove_at k G) j.
Proof.
  intro G. induction G as [|[T u] G' IH]; intros k j Hge.
  - destruct k; reflexivity.
  - destruct k; destruct j; simpl; try lia.
    + reflexivity.
    + reflexivity.
    + f_equal. apply IH. lia.
Qed.

(** insert_at and remove_at are inverses *)
Lemma remove_insert_cancel :
  forall {A} k (x : A) l,
    k <= length l ->
    remove_at k (insert_at k x l) = l.
Proof.
  induction k; intros x l Hle; simpl.
  - reflexivity.
  - destruct l; simpl in *; [lia|].
    f_equal. apply IHk. lia.
Qed.

(** Generalized output shape at arbitrary position k *)
Lemma output_shape_at :
  forall R Gin e T Gout k T1 u_in,
    R; Gin |- e : T -| Gout ->
    nth_error Gin k = Some (T1, u_in) ->
    exists u_out, nth_error Gout k = Some (T1, u_out).
Proof.
  intros R Gin e T Gout k T1 u_in Htype Hin.
  assert (Hlen := typing_preserves_length _ _ _ _ _ Htype).
  assert (Hlt: k < length Gout).
  { rewrite Hlen. apply nth_error_Some. congruence. }
  destruct (nth_error Gout k) as [[T1' u']|] eqn:E.
  - destruct (typing_preserves_bindings _ _ _ _ _ Htype k T1' u') as [u1 Hu1].
    { unfold ctx_lookup. exact E. }
    unfold ctx_lookup in Hu1. rewrite Hin in Hu1.
    assert (T1' = T1) by congruence. subst T1'.
    eexists. reflexivity.
  - apply nth_error_None in E. lia.
Qed.

(** ** Substitution Helpers *)

(** remove_at k after ctx_mark_used at k = remove_at k (mark is discarded) *)
Lemma remove_at_mark_used_self :
  forall (G : ctx) k,
    remove_at k (ctx_mark_used G k) = remove_at k G.
Proof.
  induction G as [|[T u] G' IH]; intros k.
  - destruct k; reflexivity.
  - destruct k; simpl; [reflexivity | f_equal; apply IH].
Qed.

(** If an unrestricted variable goes false→true under typing, contradiction *)
Lemma flag_false_to_true_implies_linear :
  forall R G e T G' k T1,
    R; G |- e : T -| G' ->
    nth_error G k = Some (T1, false) ->
    nth_error G' k = Some (T1, true) ->
    is_linear_ty T1 = true.
Proof.
  intros R G e T G' k T1 Htype Hin Hout.
  destruct (is_linear_ty T1) eqn:Hlin; [reflexivity | exfalso].
  pose proof (unrestricted_flag_unchanged _ _ _ _ _ Htype k T1 false Hlin
    ltac:(unfold ctx_lookup; exact Hin)) as H.
  unfold ctx_lookup in H. rewrite H in Hout. discriminate.
Qed.

(** The only linear-type values are locations *)
Lemma linear_value_is_loc :
  forall R G v T,
    R; G |- v : T -| G ->
    is_value v ->
    is_linear_ty T = true ->
    exists l r, v = ELoc l r /\ T = TString r /\ region_active R r.
Proof.
  intros R G v T Htype Hval Hlin.
  destruct T; simpl in Hlin; try discriminate.
  - (* TString r *)
    destruct (canonical_string _ _ _ _ _ Htype Hval) as [l ->].
    inversion Htype; subst. exists l, r. auto.
  - (* TRef l t — no value has this type *)
    destruct l; [|discriminate].
    exfalso. inversion Hval; subst; inversion Htype; discriminate.
  - (* TRegion — no value has this type *)
    exfalso. inversion Hval; subst; inversion Htype; discriminate.
Qed.

(** Shifting preserves values *)
Lemma shift_preserves_value :
  forall v c d, is_value v -> is_value (shift c d v).
Proof.
  intros v c d Hval. induction Hval; simpl; constructor; auto.
Qed.

(** remove_at (S k) on cons = cons (remove_at k) *)
Lemma remove_at_succ_cons :
  forall {A} k (h : A) t, remove_at (S k) (h :: t) = h :: remove_at k t.
Proof. reflexivity. Qed.

(** Substitution preserves values *)
Lemma subst_preserves_value :
  forall v k s, is_value v -> is_value (subst k s v).
Proof.
  intros v k s Hval. induction Hval; simpl; constructor; auto.
Qed.

(** ** The Generalized Substitution Lemma

    Strengthened with is_linear_ty T1 = true. This holds because binding
    constructs (let, lam, case) all require the bound variable's flag to
    go from false to true, which is only achievable for linear types.

    The key simplification: linear values are exactly locations (ELoc),
    which type via T_Loc in ANY context. This eliminates the "value
    context transfer" problem entirely. *)
Lemma subst_typing_gen :
  forall R Gin e T Gout,
    R; Gin |- e : T -| Gout ->
    forall k T1 v u_in,
      nth_error Gin k = Some (T1, u_in) ->
      is_value v ->
      is_linear_ty T1 = true ->
      R; remove_at k Gin |- v : T1 -| remove_at k Gin ->
      forall u_out,
        nth_error Gout k = Some (T1, u_out) ->
        R; remove_at k Gin |- subst k v e : T -| remove_at k Gout.
Proof.
  intros R Gin e T Gout Htype.
  induction Htype; intros k0 Tsub v0 u_in Hk_in Hval Hlin Hv_type u_out Hk_out;
    simpl.

  (* Tactic: apply IH for compound/binding cases where v0 = ELoc *)
  Local Ltac loc_ih IH :=
    eapply IH;
    try eassumption;
    try (simpl; reflexivity);
    try (constructor; assumption);
    try constructor.

  (* === Literals (T_Unit, T_Bool, T_I32): Gout = Gin, subst = id === *)
  1-3: (assert (u_out = u_in) by congruence; subst; constructor).

  (* T_Var_Lin *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + rewrite Nat.eqb_refl.
      assert (T = Tsub /\ u_in = false) by (unfold ctx_lookup in H; split; congruence).
      destruct H1 as [-> ->].
      rewrite remove_at_mark_used_self. exact Hv_type.
    + rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * assert (Hrw: remove_at k0 (ctx_mark_used G i) =
                     ctx_mark_used (remove_at k0 G) (i - 1)).
        { replace i with (S (i - 1)) at 1 by lia.
          apply remove_at_ctx_mark_used_gt. lia. }
        rewrite Hrw.
        eapply T_Var_Lin.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_ge by lia.
           replace (S (i - 1)) with i by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
      * assert (i < k0) by lia.
        rewrite remove_at_ctx_mark_used_lt by lia.
        eapply T_Var_Lin.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.

  (* T_Var_Unr *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + exfalso. unfold ctx_lookup in H. rewrite Hk_in in H.
      injection H as <- <-. rewrite Hlin in H0. discriminate.
    + rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * eapply T_Var_Unr.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_ge by lia.
           replace (S (i - 1)) with i by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.
      * assert (i < k0) by lia. eapply T_Var_Unr.
        -- unfold ctx_lookup. rewrite nth_error_remove_at_lt by lia.
           unfold ctx_lookup in H. exact H.
        -- exact H0.

  (* T_Loc *)
  - assert (u_out = u_in) by congruence; subst. constructor. assumption.

  (* T_StringNew *)
  - assert (u_out = u_in) by congruence; subst. constructor. assumption.

  (* T_StringConcat *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_StringConcat.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption;
        try (simpl; reflexivity); try constructor; try (constructor; assumption);
        try eassumption.

  (* T_StringLen: use IH directly *)
  - eapply T_StringLen. eapply IHHtype; eassumption.

  (* T_Let *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Let.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity;
        try constructor; try assumption.

  (* T_LetLin *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_LetLin; [exact H | |].
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity;
        try constructor; try assumption.

  (* T_Lam *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Lam.
    destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply (IHHtype (S k0) (TString rv) (ELoc lv rv) u_in);
      simpl; try eassumption; try reflexivity;
      try constructor; try assumption.

  (* T_App *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    econstructor.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption;
        try (simpl; reflexivity); try constructor; try (constructor; assumption);
        try eassumption.

  (* T_Pair *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    econstructor.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption;
        try (simpl; reflexivity); try constructor; try (constructor; assumption);
        try eassumption.

  (* T_Fst *)
  - eapply T_Fst; [eapply IHHtype; eassumption | assumption].

  (* T_Snd *)
  - eapply T_Snd; [eapply IHHtype; eassumption | assumption].

  (* T_Inl *)
  - eapply T_Inl. eapply IHHtype; eassumption.

  (* T_Inr *)
  - eapply T_Inr. eapply IHHtype; eassumption.

  (* T_Case *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    eapply T_Case.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype2 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity;
        try constructor; try assumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply (IHHtype3 (S k0) (TString rv) (ELoc lv rv) u_mid);
        simpl; try eassumption; try reflexivity;
        try constructor; try assumption.

  (* T_If *)
  - destruct (output_shape_at _ _ _ _ _ _ _ _ Htype1 Hk_in) as [u_mid Hu_mid].
    econstructor.
    + eapply IHHtype1; eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype2; try eassumption;
        try (simpl; reflexivity); try constructor; try (constructor; assumption);
        try eassumption.
    + destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
      eapply IHHtype3; try eassumption;
        try (simpl; reflexivity); try constructor; try (constructor; assumption);
        try eassumption.

  (* T_Region *)
  - destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region; [exact H |].
    eapply IHHtype; try eassumption.
    constructor. right. exact Hregv.

  (* T_Region_Active: same structure as T_Region, but region_active R rv = Hregv is
     exactly the goal after IHHtype, so eassumption closes it directly (no right-cons
     step needed since we are in R not r :: R). *)
  - destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_Active; [exact H |].
    eapply IHHtype; try eassumption.

  (* T_Borrow: EBorrow (EVar i) *)
  - destruct (Nat.eq_dec i k0) as [->|Hne].
    + simpl. rewrite Nat.eqb_refl.
      assert (T = Tsub) by (unfold ctx_lookup in H; congruence); subst T.
      assert (u_out = u_in) by congruence; subst.
      eapply T_Borrow_Val; assumption.
    + simpl. rewrite (proj2 (Nat.eqb_neq i k0) Hne).
      assert (u_out = u_in) by congruence; subst.
      destruct (Nat.ltb_spec k0 i) as [Hlt|Hge].
      * eapply T_Borrow. unfold ctx_lookup.
        rewrite nth_error_remove_at_ge by lia.
        replace (S (i - 1)) with i by lia.
        unfold ctx_lookup in H. exact H.
      * assert (i < k0) by lia. eapply T_Borrow. unfold ctx_lookup.
        rewrite nth_error_remove_at_lt by lia.
        unfold ctx_lookup in H. exact H.

  (* T_Borrow_Val: EBorrow v — IH + wrap *)
  - assert (u_out = u_in) by congruence; subst.
    eapply T_Borrow_Val.
    + apply subst_preserves_value. assumption.
    + eapply IHHtype; eassumption.

  (* T_Drop *)
  - eapply T_Drop.
    + exact H.
    + eapply IHHtype; eassumption.

  (* T_Copy *)
  - eapply T_Copy.
    + eassumption.
    + eapply IHHtype; try eassumption.
Qed.

(** The specific substitution lemma needed for preservation *)
Lemma subst_preserves_typing :
  forall R G e T2 G' T1 v G_v,
    R; (T1, false) :: G |- e : T2 -| (T1, true) :: G' ->
    R; G |- v : T1 -| G_v ->
    is_value v ->
    exists G_out, R; G_v |- subst 0 v e : T2 -| G_out.
Proof.
  intros R G e T2 G' T1 v G_v Htype Hv Hval.
  assert (HGv: G_v = G) by (eapply value_context_unchanged; eassumption).
  subst G_v.
  assert (Hlin: is_linear_ty T1 = true).
  { eapply (flag_false_to_true_implies_linear _ _ _ _ _ 0 T1 Htype); simpl; reflexivity. }
  eexists.
  eapply (subst_typing_gen _ _ _ _ _ Htype 0 T1 v false).
  - reflexivity.
  - exact Hval.
  - exact Hlin.
  - exact Hv.
  - reflexivity.
Qed.

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

(** ** Preservation

    Well-typed expressions preserve typing under reduction.
    Induction on the step relation. *)

Theorem preservation :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G',
    R; G |- e : T -| G' ->
    exists G_out, R'; G |- e' : T -| G_out.
Proof.
  intros mu R e mu' R' e' Hstep.
  induction Hstep; intros G0 T0 G0' Htype;
    (* Before inversion: remember the typed expression so that cross-case unification
       (inversion Htype on a free variable `e`) does not lose the step-case equation.
       After `induction Hstep; intros ... Htype`, the expression in Htype may still be
       a free variable `e` with a separate hypothesis `He : e = EStringNew r s` etc.
       If `inversion Htype; subst` fires for a cross-case typing rule (e.g. T_Unit
       typing `e := EUnit`), subst can eliminate `e` and consume `He` in a direction
       that loses the discriminating information. `remember` pins the form as `He_orig`
       so congruence / discriminate can close all expression-mismatch goals. *)
    try (match type of Htype with
         | has_type _ _ ?e_typed _ _ => remember e_typed as e_orig eqn:He_orig
         end);
    inversion Htype; subst;
    try solve [eexists; econstructor; eassumption];
    try solve [eexists; eassumption];
    try solve [eapply subst_preserves_typing; eassumption];
    try solve [exfalso; eapply values_dont_step; eassumption];
    try solve [exfalso; congruence];
    try solve [exfalso; discriminate];
    (* EVar cannot step — no step constructor has EVar i as the redex expression.
       This closes T_Borrow cross-cases in S_Borrow_Step (after inversion gives EVar
       as the inner expression, the inner step hypothesis is immediately impossible). *)
    try solve [exfalso;
               match goal with [ H : (_, _, EVar _) -->> _ |- _ ] => inversion H end].
  (* Congruence: IH + reconstruct *)
  all: try solve [match goal with [ IH : forall _ _ _, _ -> exists _, _ |- _ ] =>
    match goal with [ H : has_type _ _ _ _ _ |- _ ] =>
      destruct (IH _ _ _ H) as [? ?];
      eexists; econstructor; try eassumption end end].
  all: try solve [eexists; econstructor; try eassumption].
  all: try solve [eexists; eassumption].
  all: try solve [exfalso; congruence].
  all: try solve [exfalso; discriminate].
  all: try solve [exfalso; eapply values_dont_step; eassumption].
  all: try solve [exfalso;
                  match goal with [ H : (_, _, EVar _) -->> _ |- _ ] => inversion H end].
  (* S_Region_Step + T_Region and S_Region_Exit + T_Region are contradictory:
     step premiss has In r R while T_Region requires ~ In r R. `tauto` closes.
     S_Region_Enter + T_Region_Active is also contradictory (step has ~ In r R,
     typing has In r R). *)
  all: try solve [exfalso; tauto].
  (* S_Region_Enter + T_Region: The step changes region env R to r :: R while the
     expression stays ERegion r e. T_Region gives (r :: R); G |- e : T -| G'.
     T_Region_Active applies with In r (r :: R) (left; reflexivity) and that inner
     typing to produce (r :: R); G |- ERegion r e : T -| G'. *)
  all: try solve [eexists; eapply T_Region_Active; [left; reflexivity | eassumption]].
  (* REMAINING CASES (2026-04-12):
     Two cases involving region exit/step cannot be closed mechanically here:

     (a) S_Region_Step + T_Region_Active: inner step changes R to R'.
         IH gives R'; G |- e' : T -| G_out. Need R'; G |- ERegion r e' : T -| G_out2.
         If In r R', apply T_Region_Active. If ~ In r R' (inner step removed r via
         nested S_Region_Exit for same region), need T_Region, which requires
         (r :: R'); G |- e' : T -| G_out — not derivable from R'; G |- e' without
         a region env weakening lemma. Region env weakening fails in general because
         T_Region requires ~ In r R (which fails when r is newly added to env).
         This case only arises from ERegion r (ERegion r v) in intermediate states
         (not reachable from initial well-typed programs at R=[]).

     (b) S_Region_Exit + T_Region_Active: exit changes R to remove_first r R.
         Typing has R; G |- v : T -| G'. Need (remove_first r R); G |- v : T -| G_out.
         If T does not contain r (no region escape), this follows from region-agnostic
         typing of values. But the current T_Region_Active has no "T does not mention r"
         restriction, so the proof requires an additional region-escape-free lemma.

     Both cases require a region-escape-freedom property (the result type T of
     ERegion r e cannot contain r as an active region reference). This is a standard
     requirement in region type systems (e.g., Tofte-Talpin "region does not escape")
     but has not yet been added to the Ephapax typing rules. Adding a "r ∉ free_regions T"
     premise to T_Region and T_Region_Active, plus a free_regions function and associated
     lemmas, would close these cases. *)
  all: admit.
Admitted.
