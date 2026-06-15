(* SPDX-License-Identifier: MPL-2.0 *)
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  🛑 ARCHAEOLOGY -- DO NOT EXTEND                                ***
  ***                                                                ***
  ***  This is the LEGACY operational semantics. The `preservation`  ***
  ***  theorem here is PROVABLY FALSE -- verified by                 ***
  ***  `formal/Counterexample.v` (5 Qed lemmas).                     ***
  ***                                                                ***
  ***  Do NOT add lemmas to close it. Do NOT add `Admitted` or       ***
  ***  `Axiom` declarations. Do NOT extend with Lemma B variants,    ***
  ***  region-weakening predicates,                                  ***
  ***  `step_preserves_type_at_pre`-style helpers, or strengthened   ***
  ***  substitution lemmas.                                          ***
  ***                                                                ***
  ***  Active proof work happens in:                                 ***
  ***    formal/TypingL1.v     -- L1 judgment (modality-indexed)     ***
  ***    formal/Semantics_L1.v -- L1 semantics                       ***
  ***    formal/Modality.v     -- L2 modality                        ***
  ***    formal/Echo.v         -- L3 echo / residue                  ***
  ***                                                                ***
  ***  See `STATUS.adoc`, `PROOF-NEEDS.md`, and                      ***
  ***  `formal/PRESERVATION-DESIGN.md` for the full doctrine.        ***
  ***  Owner directive 2026-05-27: `CLAUDE.md` "Owner directive"     ***
  ***  section.                                                      ***
  *********************************************************************

*)

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

From Ephapax Require Import Syntax.
From Ephapax Require Import Typing.

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
      expr_free_of_region r v ->
      (mu, R, ERegion r v) -->>
        (mem_free_region mu r, remove_first r R, v)

  (** L3 — parallel echo-emitting region-exit rule. Same trigger as
      [S_Region_Exit] but the output is [EEcho T v] instead of [v],
      packaging the pre-collapse witness in a runtime echo residue
      for downstream [EObserve] consumption. Quantified universally
      over the witness type [T]; preservation_l3 (slice 4) picks the
      T that matches the typing derivation in [T_Region_L1_Echo] /
      [T_Region_Active_L1_Echo].

      The legacy [S_Region_Exit] above is untouched — programs that
      typed via [T_Region_L1] (non-echo path) reduce via that rule;
      programs that typed via [T_Region_L1_Echo] reduce via this
      one. Non-deterministic at the relation level, but each typing
      derivation pins the path. See [PRESERVATION-DESIGN.md §6.3]
      and [formal/Echo.v]. *)

  | S_Region_Exit_Echo : forall mu R r v T,
      is_value v ->
      In r R ->
      expr_free_of_region r v ->
      (mu, R, ERegion r v) -->>
        (mem_free_region mu r, remove_first r R, EEcho T v)

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

  (** L3 — parallel echo-emitting drop rule. Same trigger as
      [S_Drop] but the output is [EEcho T (ELoc l r)] instead of
      [EUnit], packaging the (pre-free) location witness in a
      runtime echo residue. Quantified over witness type [T] —
      preservation_l3 (slice 4) picks T to match [T_Drop_L1_Echo]. *)

  | S_Drop_Echo : forall mu R l r T,
      (mu, R, EDrop (ELoc l r)) -->>
        (mem_write mu l CFree, R, EEcho T (ELoc l r))

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

(** Classify steps from ERegion — avoids hypothesis naming issues.
    L3 (slice 3c) adds a fourth disjunct for the [S_Region_Exit_Echo]
    rule, which mirrors Exit's memory + region effects but packages
    the post-step value in an [EEcho] residue. *)
Lemma step_from_eregion :
  forall mu R r e mu1 R1 e1,
    (mu, R, ERegion r e) -->> (mu1, R1, e1) ->
    (* Enter *)     (mu1 = mu /\ R1 = r :: R /\ e1 = ERegion r e)
    (* Exit *)      \/ (In r R /\ is_value e /\ mu1 = mem_free_region mu r
                        /\ R1 = remove_first r R /\ e1 = e)
    (* Exit_Echo *) \/ (In r R /\ is_value e /\ mu1 = mem_free_region mu r
                        /\ R1 = remove_first r R
                        /\ exists T, e1 = EEcho T e)
    (* Step *)      \/ (In r R /\ exists e',
                        (mu, R, e) -->> (mu1, R1, e')
                        /\ e1 = ERegion r e').
Proof.
  intros. inversion H; subst.
  + left. auto.
  + right. left. repeat (split; [auto; fail|]). auto.
  + right. right. left. repeat (split; [auto; fail|]). eexists. reflexivity.
  + right. right. right. split; [assumption|].
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
      | [[_ [Hval_e [-> [-> [TT ->]]]]]
      | [_ [e' [Hsub ->]]]]]].
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
    + (* Exit_Echo: mirror of Exit, but cc ends at the EEcho residue
         (also a value via VEcho). Memory is freed the same way. *)
      assert (Hcc2: cc = (mem_free_region mu r, remove_first r R, EEcho TT e)).
      { inversion Hmulti.
        - reflexivity.
        - destruct c2 as [[? ?] ?].
          exfalso. eapply values_dont_step.
          + apply VEcho. exact Hval_e.
          + eassumption. }
      assert (mem_free_region mu r = mu') by congruence.
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
    eexists. split; [eapply T_Region; [assumption | assumption | exact Ht]|].
    split; [assumption | split; [assumption | exact Hc]].

  (* T_Region_Active: same structure, uses T_Region_Active in conclusion *)
  - destruct (IHHtype G2 Hagree Hfp) as [G2' [Ht [Ha [Hf Hc]]]].
    eexists. split; [eapply T_Region_Active; [assumption | assumption | exact Ht]|].
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
(* PROOF OBLIGATION [typing_ctx_transfer] — all 25 cases proved (2026-04-11).
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
  - eapply T_Region.
    + assumption.
    + assumption.
    + apply IHHtype. assumption.

  (* T_Region_Active *)
  - eapply T_Region_Active.
    + assumption.
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
    eapply T_Region; [exact H | assumption |].
    eapply IHHtype; try eassumption.
    constructor. right. exact Hregv.

  (* T_Region_Active: same structure as T_Region, but region_active R rv = Hregv is
     exactly the goal after IHHtype, so eassumption closes it directly (no right-cons
     step needed since we are in R not r :: R). *)
  - destruct (linear_value_is_loc _ _ _ _ Hv_type Hval Hlin) as [lv [rv [-> [-> Hregv]]]].
    eapply T_Region_Active; [exact H | assumption |].
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

(** Strengthened variant that exposes the specific output context
    (instead of an existential). Used by [step_output_context_eq]
    (Lemma B, Phase 1) to discharge the beta-reduction step cases
    where the existential in [subst_preserves_typing] blocks the
    output-context equality proof.

    Both the witness ([G_v = G]) and the specific output context
    ([G']) come from [subst_typing_gen]'s explicit
    [remove_at k Gout] shape, which collapses for [k = 0] via
    [remove_at 0 ((T, b) :: G) = G]. *)
Lemma subst_preserves_typing_strong :
  forall R G e T2 G' T1 v G_v,
    R; (T1, false) :: G |- e : T2 -| (T1, true) :: G' ->
    R; G |- v : T1 -| G_v ->
    is_value v ->
    G_v = G /\ R; G |- subst 0 v e : T2 -| G'.
Proof.
  intros R G e T2 G' T1 v G_v Htype Hv Hval.
  assert (HGv: G_v = G) by (eapply value_context_unchanged; eassumption).
  split; [exact HGv|].
  subst G_v.
  assert (Hlin: is_linear_ty T1 = true).
  { eapply (flag_false_to_true_implies_linear _ _ _ _ _ 0 T1 Htype); simpl; reflexivity. }
  pose proof (subst_typing_gen _ _ _ _ _ Htype 0 T1 v false eq_refl Hval Hlin Hv true eq_refl) as Hsubst.
  simpl in Hsubst.
  exact Hsubst.
Qed.

(** Helper: types_agree and false_preserved are reflexive *)
Lemma ctx_types_agree_refl : forall G, ctx_types_agree G G.
Proof.
  intro G. split; [reflexivity|]. intros. eexists. exact H.
Qed.

(** [ctx_types_agree] is symmetric: same length + same type at each
    position (modulo used-flag) is a symmetric relation. *)
Lemma ctx_types_agree_sym : forall G1 G2,
  ctx_types_agree G1 G2 -> ctx_types_agree G2 G1.
Proof.
  intros G1 G2 [Hlen Hpos].
  split; [symmetry; exact Hlen|].
  intros i T u Hlk.
  (* Hlk : ctx_lookup G2 i = Some (T, u). Need: exists u', ctx_lookup G1 i = Some (T, u'). *)
  (* Strategy: G1 has same length as G2, so G1[i] exists. Use Hpos in
     the forward direction by case on what G1[i] is. *)
  destruct (ctx_lookup G1 i) as [[T1 u1]|] eqn:Hg1.
  - (* G1[i] = (T1, u1). By Hpos, G2[i] = (T1, ?u'). Combined with
       Hlk : G2[i] = (T, u), get T = T1. The [destruct ... eqn:Hg1]
       above rewrites [ctx_lookup G1 i] in the goal to [Some (T1, u1)],
       so after [subst T1] the goal becomes [Some (T, u1) = Some (T, u1)]
       which closes by reflexivity. *)
    pose proof (Hpos i T1 u1 Hg1) as [u' Hg2].
    assert (HT : T = T1) by congruence. subst T1.
    exists u1. reflexivity.
  - (* G1[i] = None. But |G1| = |G2| and G2[i] exists (from Hlk), so
       G1[i] should also exist. Contradiction. ctx_lookup is just
       nth_error, so we unfold and use nth_error_Some. *)
    exfalso.
    unfold ctx_lookup in *.
    assert (Hi : i < length G2).
    { apply nth_error_Some. rewrite Hlk. discriminate. }
    rewrite <- Hlen in Hi.
    apply nth_error_Some in Hi. apply Hi. exact Hg1.
Qed.

(** [ctx_types_agree] is transitive. *)
Lemma ctx_types_agree_trans : forall G1 G2 G3,
  ctx_types_agree G1 G2 -> ctx_types_agree G2 G3 -> ctx_types_agree G1 G3.
Proof.
  intros G1 G2 G3 [Hlen12 Hpos12] [Hlen23 Hpos23].
  split; [transitivity (length G2); assumption|].
  intros i T u Hg1.
  destruct (Hpos12 i T u Hg1) as [u2 Hg2].
  destruct (Hpos23 i T u2 Hg2) as [u3 Hg3].
  exists u3. exact Hg3.
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
    Induction on the step relation.
    
    NOTE (2026-04-15): T_Region and T_Region_Active now include the
    region-escape-freedom premise "r ∉ free_regions T" to ensure that
    regions do not escape their scope. This addresses the two remaining
    cases in the original preservation proof. *)

(** ** Region-shrink lemmas

    [remove_first_preserves_other] says that removing one region name
    doesn't affect membership of a distinct name. Used when re-typing
    under a shrunken region env. *)

Lemma remove_first_preserves_other :
  forall r r' R,
    r <> r' ->
    In r' R ->
    In r' (remove_first r R).
Proof.
  intros r r' R Hne. induction R as [|r0 R' IH]; intros Hin.
  - inversion Hin.
  - simpl. destruct (String.eqb r r0) eqn:Heq.
    + apply String.eqb_eq in Heq. subst r0.
      destruct Hin as [Heq' | Hin]; [subst; contradiction | exact Hin].
    + destruct Hin as [Heq' | Hin].
      * subst. left. reflexivity.
      * right. apply IH. exact Hin.
Qed.

(** [region_shrink_preserves_typing]: if an expression is typed at [R]
    and makes no syntactic reference to region [r], then its typing
    survives removing the first occurrence of [r] from [R].

    The key insight is that the typing rules depend on [R] only via
    [region_active R r' := In r' R] for specific [r']. As long as every
    [r'] the expression needs is preserved under [remove_first r], the
    derivation transports. [expr_free_of_region r e] guarantees no [r']
    demanded by [e] equals [r], so [remove_first_preserves_other]
    discharges each case. *)

Lemma region_shrink_in_preserves :
  forall r r0 R,
    r <> r0 ->
    (In r0 R <-> In r0 (remove_first r R)).
Proof.
  intros r r0 R Hne. induction R as [|r' R' IH]; simpl.
  - reflexivity.
  - destruct (String.eqb r r') eqn:Heq.
    + apply String.eqb_eq in Heq. subst r'.
      split; intros.
      * destruct H; [subst; contradiction | exact H].
      * right. exact H.
    + simpl. split; intros.
      * destruct H as [->|Hin]; [left; reflexivity | right; apply IH; exact Hin].
      * destruct H as [->|Hin]; [left; reflexivity | right; apply IH; exact Hin].
Qed.

Lemma remove_first_not_in_id :
  forall r R, ~ In r R -> remove_first r R = R.
Proof.
  intros r R Hnot. induction R as [|r' R' IH]; simpl.
  - reflexivity.
  - destruct (String.eqb r r') eqn:Heq.
    + apply String.eqb_eq in Heq. subst r'.
      exfalso. apply Hnot. left. reflexivity.
    + f_equal. apply IH. intros Hin. apply Hnot. right. exact Hin.
Qed.

Lemma remove_first_subset :
  forall r r0 R,
    In r0 (remove_first r R) -> In r0 R.
Proof.
  intros r r0 R. induction R as [|r' R' IH]; simpl; intros Hin.
  - exact Hin.
  - destruct (String.eqb r r') eqn:Heq.
    + apply String.eqb_eq in Heq. subst r'. right. exact Hin.
    + destruct Hin as [->|Hin']; [left; reflexivity | right; apply IH; exact Hin'].
Qed.

Lemma region_shrink_notin_preserves :
  forall r r0 R,
    ~ In r0 R ->
    ~ In r0 (remove_first r R).
Proof.
  intros r r0 R Hnot Hin. apply Hnot.
  apply remove_first_subset with (r := r). exact Hin.
Qed.

(** [region_env_perm_typing]: typing transfers between any two region
    environments that agree on membership (forall r0, In r0 R1 <-> In r0 R2).
    Proved by structural induction on the typing derivation.

    Key cases:
    - T_Loc / T_StringNew: membership transferred by Hagree.
    - T_Region: ~ In r R1 transfers to ~ In r R2; body transferred under
      r :: R2 via an extended agreement.
    - T_Region_Active: In r R1 transfers to In r R2; body transferred
      under R2 via Hagree directly.
    All other cases only pass Hagree to the IH. *)
Lemma region_env_perm_typing :
  forall R1 G e T G',
    R1; G |- e : T -| G' ->
    forall R2,
    (forall r0, In r0 R1 <-> In r0 R2) ->
    R2; G |- e : T -| G'.
Proof.
  intros R1 G e T G' Htype.
  induction Htype; intros R2 Hagree.
  - (* T_Unit *) apply T_Unit.
  - (* T_Bool *) apply T_Bool.
  - (* T_I32 *) apply T_I32.
  - (* T_Var_Lin *) eapply T_Var_Lin; eauto.
  - (* T_Var_Unr *) eapply T_Var_Unr; eauto.
  - (* T_Loc *) apply T_Loc. unfold region_active in *. exact (proj1 (Hagree _) H).
  - (* T_StringNew *) apply T_StringNew. unfold region_active in *. exact (proj1 (Hagree _) H).
  - (* T_StringConcat *)
    eapply T_StringConcat; [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree].
  - (* T_StringLen *) eapply T_StringLen; eapply IHHtype; exact Hagree.
  - (* T_Let *)
    eapply T_Let; [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree].
  - (* T_LetLin *)
    eapply T_LetLin; [eassumption | eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree].
  - (* T_Lam *) eapply T_Lam; eapply IHHtype; exact Hagree.
  - (* T_App *)
    eapply T_App; [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree].
  - (* T_Pair *)
    eapply T_Pair; [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree].
  - (* T_Fst *) eapply T_Fst; [eapply IHHtype; exact Hagree | eassumption].
  - (* T_Snd *) eapply T_Snd; [eapply IHHtype; exact Hagree | eassumption].
  - (* T_Inl *) eapply T_Inl; eapply IHHtype; exact Hagree.
  - (* T_Inr *) eapply T_Inr; eapply IHHtype; exact Hagree.
  - (* T_Case *)
    eapply T_Case;
      [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree | eapply IHHtype3; exact Hagree].
  - (* T_If *)
    eapply T_If;
      [eapply IHHtype1; exact Hagree | eapply IHHtype2; exact Hagree | eapply IHHtype3; exact Hagree].
  - (* T_Region: ~ In r R1, body typed under r :: R1.
       ~ In r R2 from Hagree. Apply T_Region with body under r :: R2
       via IH on body with extended agreement. *)
    eapply T_Region.
    + intro Hin2. apply H. exact (proj2 (Hagree _) Hin2).
    + exact H0.
    + eapply IHHtype.
      intro r1.
      destruct (String.eqb r r1) eqn:Heqr1.
      * apply String.eqb_eq in Heqr1. subst r1.
        split; intros; left; reflexivity.
      * apply String.eqb_neq in Heqr1.
        split; intros Hin.
        -- destruct Hin as [Hr | Hin].
           ++ exfalso. apply Heqr1. exact Hr.
           ++ right. exact (proj1 (Hagree r1) Hin).
        -- destruct Hin as [Hr | Hin].
           ++ exfalso. apply Heqr1. exact Hr.
           ++ right. exact (proj2 (Hagree r1) Hin).
  - (* T_Region_Active: In r R1 → In r R2 via Hagree; body under R2 via IH *)
    eapply T_Region_Active.
    + exact (proj1 (Hagree _) H).
    + exact H0.
    + eapply IHHtype. exact Hagree.
  - (* T_Borrow *) eapply T_Borrow. exact H.
  - (* T_Borrow_Val *) eapply T_Borrow_Val; [exact H | eapply IHHtype; exact Hagree].
  - (* T_Drop *) eapply T_Drop; [exact H | eapply IHHtype; exact Hagree].
  - (* T_Copy *) eapply T_Copy; [exact H | eapply IHHtype; exact Hagree].
Qed.

(** [remove_first_then_cons_membership_eq]: if [r ∈ R], then
    [r :: remove_first r R] and [R] have exactly the same membership.
    Note that this does NOT require [NoDup R] — even if [r] appears
    multiple times in [R], removing one occurrence and prepending one
    yields a list with the same set of elements.

    Used by [step_preserves_type]'s remove-first sub-case to bridge
    a sibling typing under [remove_first r R0] back to one under [R0]
    via [region_add_typing] + [region_env_perm_typing]. *)
Lemma remove_first_then_cons_membership_eq :
  forall r R,
    In r R ->
    forall r0, In r0 (r :: remove_first r R) <-> In r0 R.
Proof.
  intros r R HInr r0.
  destruct (String.eqb r r0) eqn:Heq.
  - apply String.eqb_eq in Heq. subst r0.
    split; intros _.
    + exact HInr.
    + left; reflexivity.
  - apply String.eqb_neq in Heq.
    split; intros Hin.
    + destruct Hin as [Heq' | Hin].
      * exfalso. apply Heq. exact Heq'.
      * apply (region_shrink_in_preserves r r0 R Heq) in Hin. exact Hin.
    + right. apply (region_shrink_in_preserves r r0 R Heq). exact Hin.
Qed.

(** [region_add_typing]: adding a region to the environment preserves
    typing, even though the region set grows.  The only structural
    difficulty is T_Region for a sub-expression [ERegion r0 e0]:

    - If r0 = r: the original derivation had ~ In r R (so T_Region),
      but under r :: R we have In r (r :: R), so switch to
      T_Region_Active using the *original* body derivation (body was
      already typed under r :: R = r0 :: R).

    - If r0 ≠ r: ~ In r0 (r :: R) still holds; the body must be typed
      under r0 :: (r :: R).  The IH gives us the body under
      r :: (r0 :: R).  These two environments have identical membership
      (both contain exactly r and r0 plus whatever was in R), so
      [region_env_perm_typing] bridges the gap. *)
Lemma region_add_typing :
  forall R G e T G' r,
    R; G |- e : T -| G' ->
    (r :: R); G |- e : T -| G'.
Proof.
  intros R G e T G' r Htype.
  induction Htype.
  - apply T_Unit.
  - apply T_Bool.
  - apply T_I32.
  - eapply T_Var_Lin; eauto.
  - eapply T_Var_Unr; eauto.
  - apply T_Loc. right. exact H.
  - apply T_StringNew. right. exact H.
  - eapply T_StringConcat; eassumption.
  - eapply T_StringLen. eassumption.
  - eapply T_Let; eassumption.
  - eapply T_LetLin; [eassumption | eassumption | eassumption].
  - eapply T_Lam. eassumption.
  - eapply T_App; eassumption.
  - eapply T_Pair; eassumption.
  - eapply T_Fst; eassumption.
  - eapply T_Snd; eassumption.
  - eapply T_Inl. eassumption.
  - eapply T_Inr. eassumption.
  - eapply T_Case; eassumption.
  - eapply T_If; eassumption.
  - (* T_Region for ERegion r0 body: ~ In r0 R, body under r0 :: R.
       Under r :: R we need to type ERegion r0 body.
       Case split on r0 = r. *)
    destruct (String.eqb r r0) eqn:Heq.
    + (* r = r0: use T_Region_Active. In r0 (r :: R) trivially.
         Body is already typed under r0 :: R = r :: R from Htype. *)
      apply String.eqb_eq in Heq. subst r0.
      eapply T_Region_Active.
      * left. reflexivity.
      * exact H0.
      * exact Htype.
    + (* r ≠ r0: use T_Region. ~ In r0 (r :: R) since r ≠ r0 and ~ In r0 R.
         Body IH gives body under r :: (r0 :: R).
         Need body under r0 :: (r :: R).
         These envs have same membership → region_env_perm_typing. *)
      apply String.eqb_neq in Heq.
      eapply T_Region.
      * (* ~ In r0 (r :: R) since r ≠ r0 and ~ In r0 R *)
        intros [Hr | Hin].
        -- apply Heq. congruence.
        -- apply H. exact Hin.
      * exact H0.
      * (* Bridge r :: (r0 :: R) ↔ r0 :: (r :: R) via perm *)
        eapply region_env_perm_typing.
        -- exact IHHtype.
        -- intro r1. simpl. tauto.
  - (* T_Region_Active: In r0 R, body under R.
       Under r :: R, In r0 (r :: R) via right. Body IH gives body under r :: R. *)
    eapply T_Region_Active.
    + right. exact H.
    + exact H0.
    + exact IHHtype.
  - eapply T_Borrow. exact H.
  - eapply T_Borrow_Val; [exact H | eassumption].
  - eapply T_Drop; [exact H | eassumption].
  - eapply T_Copy; [exact H | eassumption].
Qed.

Lemma region_shrink_preserves_typing :
  forall R G e T G' r,
    R; G |- e : T -| G' ->
    expr_free_of_region r e ->
    (remove_first r R); G |- e : T -| G'.
Proof.
  intros R G e T G' r Htype.
  induction Htype; intros Hfree; simpl in Hfree.
  - apply T_Unit.
  - apply T_Bool.
  - apply T_I32.
  - eapply T_Var_Lin; eauto.
  - eapply T_Var_Unr; eauto.
  - apply T_Loc. unfold region_active in *.
    apply (proj1 (region_shrink_in_preserves r r0 R Hfree)). exact H.
  - apply T_StringNew. unfold region_active in *.
    apply (proj1 (region_shrink_in_preserves r r0 R Hfree)). exact H.
  - destruct Hfree as [Hf1 Hf2]. eapply T_StringConcat; auto.
  - eapply T_StringLen; auto.
  - destruct Hfree as [Hf1 Hf2]. eapply T_Let; auto.
  - destruct Hfree as [Hf1 Hf2]. eapply T_LetLin.
    + exact H.
    + apply IHHtype1. exact Hf1.
    + apply IHHtype2. exact Hf2.
  - eapply T_Lam. apply IHHtype. exact Hfree.
  - destruct Hfree as [Hf1 Hf2]. eapply T_App; auto.
  - destruct Hfree as [Hf1 Hf2]. eapply T_Pair; auto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - eapply T_Inl; auto.
  - eapply T_Inr; auto.
  - destruct Hfree as [Hf1 [Hf2 Hf3]]. eapply T_Case; auto.
  - destruct Hfree as [Hf1 [Hf2 Hf3]]. eapply T_If; auto.
  - (* T_Region *)
    destruct (String.eqb r r0) eqn:Heq.
    + (* r = r0: shadowed. Hfree is True. Use remove_first_not_in_id
         since ~ In r R gives remove_first r R = R. *)
      apply String.eqb_eq in Heq. subst r0.
      rewrite (remove_first_not_in_id r R H).
      eapply T_Region; [exact H | exact H0 | exact Htype].
    + (* r <> r0: descend *)
      eapply T_Region.
      * apply region_shrink_notin_preserves. exact H.
      * exact H0.
      * specialize (IHHtype Hfree). simpl in IHHtype.
        rewrite Heq in IHHtype. exact IHHtype.
  - (* T_Region_Active *)
    destruct (String.eqb r r0) eqn:Heq.
    + apply String.eqb_eq in Heq. subst r0.
      (* r = r0: active, In r R. Hfree = True (shadowing).
         IH gives (remove_first r R); G |- e_body : T -| G'.
         Need: (remove_first r R); G |- ERegion r e_body : T -| G'.
         Case-split on In r (remove_first r R):
         - If yes: T_Region_Active directly.
         - If no:  T_Region (~ In r (remove_first r R)) + body under
                   r :: (remove_first r R) via region_add_typing. *)
      destruct (in_dec string_dec r (remove_first r R)) as [Hin | Hnotin].
      * (* In r (remove_first r R): r appears multiple times in R.
           Transport Htype : R;G|-e:T-|G' to (remove_first r R);G|-e:T-|G' via perm,
           then apply T_Region_Active. *)
        eapply T_Region_Active.
        -- exact Hin.
        -- exact H0.
        -- eapply region_env_perm_typing.
           ++ exact Htype.
           ++ intro r1.
              destruct (string_dec r r1) as [Heqr1 | Hneqr1].
              ** subst r1. split; intros _; [exact Hin | exact H].
              ** exact (region_shrink_in_preserves r r1 R Hneqr1).
      * (* ~ In r (remove_first r R): r appears exactly once in R.
           Use T_Region. Need body under (r :: remove_first r R).
           Transport Htype : R;G|-e:T-|G' to (r :: remove_first r R);G|-e:T-|G' via perm.
           Membership: In r1 R <-> In r1 (r :: remove_first r R). *)
        eapply T_Region.
        -- exact Hnotin.
        -- exact H0.
        -- eapply region_env_perm_typing.
           ++ exact Htype.
           ++ intro r1.
              destruct (string_dec r r1) as [Heqr1 | Hneqr1].
              ** subst r1. split; intros _.
                 --- left. reflexivity.
                 --- exact H.
              ** split; intros Hin2.
                 --- right. exact (proj1 (region_shrink_in_preserves r r1 R Hneqr1) Hin2).
                 --- destruct Hin2 as [Hr1 | Hin2].
                     +++ exfalso. apply Hneqr1. exact Hr1.
                     +++ exact (proj2 (region_shrink_in_preserves r r1 R Hneqr1) Hin2).
    + eapply T_Region_Active.
      * apply region_shrink_in_preserves.
        -- intros ->. rewrite String.eqb_refl in Heq. discriminate.
        -- exact H.
      * exact H0.
      * apply IHHtype. exact Hfree.
  - eapply T_Borrow. exact H.
  - eapply T_Borrow_Val; [exact H|apply IHHtype; exact Hfree].
  - eapply T_Drop; [exact H|apply IHHtype; exact Hfree].
  - eapply T_Copy; [exact H|apply IHHtype; exact Hfree].
Qed.

(** [region_shrink_preserves_typing_dup]: typing transfers from [R] to
    [remove_first r R] without a freshness side-condition on [e],
    PROVIDED [r] still appears in [remove_first r R] (i.e. [r] was
    duplicated in [R]).

    Distinct from [region_shrink_preserves_typing] (above), which
    handles the unique-[r] case and requires [expr_free_of_region r e].
    The two lemmas dispatch the same membership question on opposite
    sides: this one fires when [r] survives the removal; the other
    fires when [r] is fully gone but the expression doesn't reference it.

    Proof: pure transport via [region_env_perm_typing]. When
    [In r (remove_first r R)], the membership predicate at [r] is
    preserved by [remove_first], and at any [r0 <> r] it is preserved
    by [region_shrink_in_preserves]. Hence [R] and [remove_first r R]
    have identical membership, and typing transports unconditionally.

    Provable but does NOT close any of preservation's RIGHT-branch
    admits in isolation: the operational semantics (S_Region_Exit on
    a region [r] with [In r R]) never produces the duplicate-[r] case
    in a configuration reachable from a well-typed initial program, as
    the static [T_Region] rule's [~In r R] premise prevents shadowing.
    Lands as adjunct infrastructure: completes the case split alongside
    [region_shrink_preserves_typing], documents the III-a candidate
    explored in PRESERVATION-HANDOFF.md §"Open: region-env weakening
    for non-values". *)
Lemma region_shrink_preserves_typing_dup :
  forall R G e T G' r,
    R; G |- e : T -| G' ->
    In r (remove_first r R) ->
    (remove_first r R); G |- e : T -| G'.
Proof.
  intros R G e T G' r Htype HinDup.
  assert (HinR : In r R) by
    (eapply remove_first_subset; exact HinDup).
  eapply region_env_perm_typing; [exact Htype |].
  intro r0.
  destruct (string_dec r r0) as [Heq | Hneq].
  - subst r0. split; intros _; assumption.
  - exact (region_shrink_in_preserves r r0 R Hneq).
Qed.

(** [typing_free_of_absent_region]: if [e] is well-typed at [R] and
    region [r] is NOT in [R], then [e] is syntactically free of [r].

    This is the static-shadowing-prevention fact: T_Region's [~In r R]
    premise rules out any subterm of [e] that would reference [r],
    because T_Loc, T_StringNew, and T_Region_Active each require
    [In r0 R] for their region argument [r0], which would force
    [r0 <> r] when [~In r R]; T_Region for an inner [r0] either
    matches [r] (shadowing-true branch of expr_free_of_region — vacuous)
    or differs and recurses under [r0 :: R] where [~In r (r0 :: R)]
    still holds.

    Building block for Brief C (the C-lemma's structural recursion for
    closing preservation's 10 touches_region RIGHT branches). Brief C
    requires more than this lemma — it needs sibling-disjointness for
    the case where [R] DOES contain the exited region — but this lemma
    is the kernel of the static-no-shadowing argument and discharges
    several intermediate goals along the way.

    Proof: structural induction on the typing derivation. Each typing
    rule's region premise (where one exists) is incompatible with
    [~In r R] when applied at [r] — forcing the inner [r0 <> r] case
    where the expr_free_of_region predicate's recursive structure
    falls out. *)
Lemma typing_free_of_absent_region :
  forall R G e T G' r,
    R; G |- e : T -| G' ->
    ~ In r R ->
    expr_free_of_region r e.
Proof.
  intros R G e T G' r Htype.
  induction Htype; intros Hnot; simpl.
  - (* T_Unit *) exact I.
  - (* T_Bool *) exact I.
  - (* T_I32 *) exact I.
  - (* T_Var_Lin *) exact I.
  - (* T_Var_Unr *) exact I.
  - (* T_Loc l r0: In r0 R, so r <> r0. *)
    intros ->. apply Hnot. exact H.
  - (* T_StringNew r0 s: In r0 R, so r <> r0. *)
    intros ->. apply Hnot. exact H.
  - (* T_StringConcat *) split; [apply IHHtype1 | apply IHHtype2]; exact Hnot.
  - (* T_StringLen *) apply IHHtype; exact Hnot.
  - (* T_Let *) split; [apply IHHtype1 | apply IHHtype2]; exact Hnot.
  - (* T_LetLin *) split; [apply IHHtype1 | apply IHHtype2]; exact Hnot.
  - (* T_Lam *) apply IHHtype; exact Hnot.
  - (* T_App *) split; [apply IHHtype1 | apply IHHtype2]; exact Hnot.
  - (* T_Pair *) split; [apply IHHtype1 | apply IHHtype2]; exact Hnot.
  - (* T_Fst *) apply IHHtype; exact Hnot.
  - (* T_Snd *) apply IHHtype; exact Hnot.
  - (* T_Inl *) apply IHHtype; exact Hnot.
  - (* T_Inr *) apply IHHtype; exact Hnot.
  - (* T_Case *) split; [|split];
      [apply IHHtype1 | apply IHHtype2 | apply IHHtype3]; exact Hnot.
  - (* T_If *) split; [|split];
      [apply IHHtype1 | apply IHHtype2 | apply IHHtype3]; exact Hnot.
  - (* T_Region r0 e: ~ In r0 R; body at r0 :: R. *)
    destruct (String.eqb r r0) eqn:Heq.
    + exact I.
    + apply String.eqb_neq in Heq.
      apply IHHtype.
      intros [Hrr0 | HinR].
      * apply Heq. exact (eq_sym Hrr0).
      * apply Hnot. exact HinR.
  - (* T_Region_Active r0 e: In r0 R; if r = r0, then In r R, contradiction. *)
    destruct (String.eqb r r0) eqn:Heq.
    + exact I.
    + apply String.eqb_neq in Heq.
      apply IHHtype. exact Hnot.
  - (* T_Borrow: EVar i — trivially free of any region. *)
    exact I.
  - (* T_Borrow_Val: EBorrow v — recurse into v. *)
    apply IHHtype; exact Hnot.
  - (* T_Drop *) apply IHHtype; exact Hnot.
  - (* T_Copy *) apply IHHtype; exact Hnot.
Qed.

(** ** Output-context determinacy

    Two derivations of the same expression in the same region
    environment and input linearity context produce the same output
    linearity context. The typing relation is syntax-directed up to
    a small choice for variables / regions / borrow, and each
    choice is disambiguated by a typing-rule premise
    ([is_linear_ty], [In r R], [is_value]) — so given the same input
    state, only one rule applies and its output context is
    determined.

    Direct prerequisite for [step_output_context_eq] (Lemma B) on
    beta-reduction cases (Cluster A): combining
    [subst_preserves_typing_strong] (one typing of the substituted
    form at a specific output) with the post-step typing
    [Htype_e'] (another typing at [Gb]) collapses to [Ga = Gb] via
    this lemma. *)
Lemma output_ctx_det :
  forall R G e T G_a,
    R; G |- e : T -| G_a ->
    forall G_b, R; G |- e : T -| G_b -> G_a = G_b.
Proof.
  intros R G e T G_a H1.
  induction H1; intros G_b H2; inversion H2; subst.
  (* Identity-output value rules (T_Unit, T_Bool, T_I32, T_Loc,
     T_StringNew, T_Lam, T_Borrow): output = input, both derivations
     give the same output literally. *)
  all: try reflexivity.
  (* T_Var_Lin/T_Var_Lin and T_Var_Unr/T_Var_Unr close above via
     reflexivity. Remaining: T_Var_Lin+T_Var_Unr cross cases where
     the linear/unrestricted premises contradict. *)
  all: try (exfalso; match goal with
    | [ Hlin : is_linear_ty ?T = true, Hunr : is_linear_ty ?T = false |- _ ] =>
        congruence
    end).
  (* Compound rules: chain IHs. Heavy automation first. *)
  all: try (
    repeat match goal with
    | [ IH : forall Gb, ?R; ?G |- ?e : ?T -| Gb -> ?Ga = Gb,
        H : ?R; ?G |- ?e : ?T -| ?Gb |- _ ] =>
        let Heq := fresh "Heq" in
        assert (Heq : Ga = Gb) by (apply IH; exact H);
        clear IH; subst
    end;
    reflexivity).
  (* T_Region / T_Region_Active: dispatch on [In r R] vs [~ In r R]. *)
  all: try (exfalso; match goal with
    | [ Hin : In ?r ?R, Hnin : ~ In ?r ?R |- _ ] => contradiction
    end).
  (* T_Borrow / T_Borrow_Val: T_Borrow needs [EVar i], T_Borrow_Val
     needs [is_value v]. EVar is not a value. *)
  all: try (exfalso; match goal with
    | [ H : is_value (EVar _) |- _ ] => inversion H
    end).
  (* Compound rules where the IH application needs explicit
     type-metavariable alignment via [type_determinacy] before
     unification succeeds. Uniform tactic: for each (single-IH) goal,
     find the two has_type hypotheses for the same sub-expression
     and align their types via type_determinacy, then apply the IH. *)
  all: try solve [
    match goal with
    | [ IH : forall G_b, ?R; ?G |- ?e : ?T -| G_b -> ?Ga = G_b,
        H1 : ?R; ?G |- ?e : ?T -| ?Ga,
        H2 : ?R; ?G |- ?e : ?T' -| ?G_b
        |- ?Ga = ?G_b ] =>
        let HTeq := fresh "HTeq" in
        assert (HTeq : T = T')
          by (eapply type_determinacy;
              [exact H1 | exact H2 | apply ctx_types_agree_refl]);
        try (inversion HTeq; subst; clear HTeq);
        try subst;
        apply IH; exact H2
    end
  ].
  (* Two-IH compound rules (T_Let, T_LetLin, T_App, T_Case): chain
     IH on the first sub-expression (to align its output context)
     then IH on the second. The first-step uses `first [...]` to
     handle both constructor-equality (T_App's TFun, T_Case's TSum)
     via [inversion] and var-equality (T_Let, T_LetLin) via plain
     [subst]. *)
  all: try solve [
    match goal with
    | [ IH1 : forall G_b, ?R; ?G |- ?e1 : ?T1 -| G_b -> ?G_mid = G_b,
        H1a : ?R; ?G |- ?e1 : ?T1 -| ?G_mid,
        H2a : ?R; ?G |- ?e1 : ?T1' -| ?G_mid'
        |- _ ] =>
        let HTeq := fresh "HTeq" in
        assert (HTeq : T1 = T1')
          by (eapply type_determinacy;
              [exact H1a | exact H2a | apply ctx_types_agree_refl]);
        first [ inversion HTeq; subst; clear HTeq
              | subst T1' ; try clear HTeq
              | subst T1  ; try clear HTeq ];
        let Hmid := fresh "Hmid" in
        assert (Hmid : G_mid = G_mid') by (apply IH1; exact H2a);
        subst G_mid';
        match goal with
        | [ IH2 : forall G_b, ?R; ?Gext |- ?e2 : ?T2 -| G_b -> ?Gout = G_b,
            H2b : ?R; ?Gext |- ?e2 : ?T2 -| ?Gout' |- _ ] =>
            let Hout := fresh "Hout" in
            assert (Hout : Gout = Gout') by (apply IH2; exact H2b);
            (* Hout is of form ((T,b)::G_a) = ((T,b)::G_b); inject
               head/tail and the tail-equality matches the goal. *)
            first [ injection Hout; intros; assumption
                  | exact Hout ]
        end
    end
  ].
Qed.

(** ** Region-invariance lemma

    Captures the structural fact that the step relation only changes
    the region environment [R] when the expression contains a region
    operation (`ERegion`) at a step-reducible position. Used by
    `step_preserves_type`'s congruence cases (and below by
    `preservation`'s congruence cases) to dispatch on whether the
    step touches a region — the [R = R'] branch closes by
    [type_determinacy], leaving only the genuinely region-changing
    sub-cases to admit pending Phase 3.

    The inductive predicate [touches_region] says "this expression's
    next reducible position is inside a region operation". The lemma
    [step_R_eq_or_touches_region] then says: every step either
    preserves [R] or fires on a [touches_region] expression. *)

Inductive touches_region : expr -> Prop :=
  | TR_here :
      forall r e, touches_region (ERegion r e)
  | TR_StringConcat1 :
      forall e1 e2,
        touches_region e1 -> touches_region (EStringConcat e1 e2)
  | TR_StringConcat2 :
      forall v e,
        is_value v -> touches_region e -> touches_region (EStringConcat v e)
  | TR_StringLen :
      forall e, touches_region e -> touches_region (EStringLen e)
  | TR_Let :
      forall e1 e2, touches_region e1 -> touches_region (ELet e1 e2)
  | TR_LetLin :
      forall e1 e2, touches_region e1 -> touches_region (ELetLin e1 e2)
  | TR_App1 :
      forall e1 e2, touches_region e1 -> touches_region (EApp e1 e2)
  | TR_App2 :
      forall v e,
        is_value v -> touches_region e -> touches_region (EApp v e)
  | TR_If :
      forall e1 e2 e3,
        touches_region e1 -> touches_region (EIf e1 e2 e3)
  | TR_Pair1 :
      forall e1 e2, touches_region e1 -> touches_region (EPair e1 e2)
  | TR_Pair2 :
      forall v e,
        is_value v -> touches_region e -> touches_region (EPair v e)
  | TR_Fst :
      forall e, touches_region e -> touches_region (EFst e)
  | TR_Snd :
      forall e, touches_region e -> touches_region (ESnd e)
  | TR_Inl :
      forall T e, touches_region e -> touches_region (EInl T e)
  | TR_Inr :
      forall T e, touches_region e -> touches_region (EInr T e)
  | TR_Case :
      forall e e1 e2,
        touches_region e -> touches_region (ECase e e1 e2)
  | TR_Borrow :
      forall e, touches_region e -> touches_region (EBorrow e)
  | TR_Drop :
      forall e, touches_region e -> touches_region (EDrop e)
  | TR_Copy :
      forall e, touches_region e -> touches_region (ECopy e).

Lemma step_R_eq_or_touches_region :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    R = R' \/ touches_region e.
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    try (left; reflexivity);
    try (right; apply TR_here);
    try (destruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl) as [Heq | HTR];
         [ left; exact Heq
         | right; constructor; (try assumption); exact HTR ]).
Qed.

(** ** Finer-grained R-change shape

    [step_R_change_shape] refines [step_R_eq_or_touches_region]'s
    disjunction into the three concrete ways [R] can change under a
    step: unchanged, prepended with a new region (S_Region_Enter
    descent), or shrunk by removing a region (S_Region_Exit descent).
    Used by [step_preserves_type]'s touches_region sub-cases to
    bridge sibling typings via [region_add_typing] (for the prepend
    case) or [region_shrink_preserves_typing] (for the shrink case
    when the sibling is free of the removed region). *)
Lemma step_R_change_shape :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    R = R' \/
    (exists r, R' = r :: R /\ ~ In r R) \/
    (exists r, R' = remove_first r R /\ In r R).
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    (* Most atomic non-region step rules leave R unchanged. *)
    try (left; reflexivity);
    (* Congruence rules: inherit from inner step. *)
    try (apply (IHHstep _ _ _ _ _ _ eq_refl eq_refl)).
  - (* S_Region_Enter: R0' = r :: R0, ~ In r R0 *)
    right; left; exists r; split; [reflexivity | assumption].
  - (* S_Region_Exit: R0' = remove_first r R0, In r R0 *)
    right; right; exists r; split; [reflexivity | assumption].
  - (* S_Region_Exit_Echo: same R-shape as S_Region_Exit *)
    right; right; exists r; split; [reflexivity | assumption].
Qed.

(** [output_ctx_det_across_step]: a generalization of [output_ctx_det]
    that handles the case where the two typings of the SAME expression
    are under DIFFERENT region envs related by a step. The step's
    R-shape (via [step_R_change_shape]) is one of:
      - R = R'    : direct [output_ctx_det].
      - R' = r :: R, ~In r R : lift first typing via
        [region_add_typing], then [output_ctx_det] under shared R'.
      - R' = remove_first r R, In r R : lift second typing via
        [region_add_typing] to (r :: R'), then permute to R via
        [region_env_perm_typing] + [remove_first_then_cons_membership_eq],
        then [output_ctx_det] under shared R.

    Used by [step_output_context_eq]'s touches_region branches to
    avoid the per-case region-weakening admits. *)
Lemma output_ctx_det_across_step :
  forall mu R mu' R' e_step e_step',
    (mu, R, e_step) -->> (mu', R', e_step') ->
    forall G T e Ga Gb,
      R;  G |- e : T -| Ga ->
      R'; G |- e : T -| Gb ->
      Ga = Gb.
Proof.
  intros mu R mu' R' e_step e_step' Hstep G T e Ga Gb H1 H2.
  pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
    as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
  - (* R = R' *)
    subst R'. eapply output_ctx_det; [exact H1 | exact H2].
  - (* R' = r :: R, ~ In r R *)
    subst R'.
    pose proof (region_add_typing _ _ _ _ _ r H1) as H1lift.
    eapply output_ctx_det; [exact H1lift | exact H2].
  - (* R' = remove_first r R, In r R *)
    subst R'.
    pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift.
    pose proof (region_env_perm_typing _ _ _ _ _ H2lift R
                  (remove_first_then_cons_membership_eq r R HinR))
      as H2_under_R.
    eapply output_ctx_det; [exact H1 | exact H2_under_R].
Qed.

(** [has_type_lift_across_step]: lift a typing of [e] from the pre-step
    region env [R] to the post-step env [R'].

    Closes the LEFT (R = R') and MIDDLE (R' = r :: R) sub-cases via
    [region_add_typing]. The RIGHT (R' = remove_first r R) sub-case
    requires [expr_free_of_region r e] (passed as an optional
    hypothesis), so this lemma is stated as a 3-way structured
    closure that the caller dispatches on via [step_R_change_shape].

    Used by [preservation]'s congruence cases to bridge sibling
    typings from the pre-step R to the post-step R' before
    reconstructing the outer typing. *)
Lemma has_type_lift_across_step_no_shrink :
  forall mu R mu' R' e_step e_step',
    (mu, R, e_step) -->> (mu', R', e_step') ->
    (R = R' \/ exists r, R' = r :: R) ->
    forall G T e G',
      R; G |- e : T -| G' ->
      R'; G |- e : T -| G'.
Proof.
  intros mu R mu' R' e_step e_step' _ Hshape G T e G' Htype.
  destruct Hshape as [HeqR | [r Hadd]].
  - subst R'. exact Htype.
  - subst R'. apply region_add_typing. exact Htype.
Qed.

(** ** Step preserves type at pre-step env (Path 3 helper, 2026-05-26)

    Companion to [step_preserves_type]. Whereas [step_preserves_type]
    asks about typings of [e] and [e'] at the step's actual pre/post
    region envs (R and R'), [step_preserves_type_at_pre] asks about
    typings of BOTH at the PRE-step env R.

    Why this is needed: in [step_preserves_type]'s S_Region_Step case,
    when the outer typing pre-step is [T_Region_Active] (In r R) and
    the outer typing post-step is [T_Region] (~In r R'), the body
    [e'] gets typed under [r :: R'] (T_Region's body env), not under
    R'. Since R' = remove_first r R0 in this case (r appeared exactly
    once in R0), [r :: R' = r :: remove_first r R0] has the SAME
    MEMBERSHIP as R0 (when In r R0). Via [region_env_perm_typing] we
    can transport [e'] to a typing under R0 (= the pre-step env).
    Now both [e] and [e'] are typed under R0 — exactly what this
    lemma needs.

    The single remaining admit in [step_preserves_type] (line 4885
    in the source) plugs into this helper after the perm transport.
    See `formal/PRESERVATION-HANDOFF.md` § "S_Region_Step's
    `r = r1` cross-case" for the obstacle analysis. *)
Lemma step_preserves_type_at_pre :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G_a, R; G |- e : T -| G_a ->
    forall T' G_b, R; G |- e' : T' -| G_b ->
    T = T'.
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    intros G0 T0 Ga Hte T' Gb Hte'.
  (* Atomic-axiom closure: leaf-value typings invert + reflexivity.
     Mirrors step_preserves_type's first big block. Closes
     S_StringNew, S_StringConcat, S_StringLen, S_Region_Enter (some
     of these via the leaf inversion chain). *)
  all: try (
    inversion Hte; subst;
    inversion Hte'; subst;
    repeat match goal with
    | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EI32 _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ EUnit _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EBool _) _ _ |- _ ] =>
        inversion H; subst; clear H
    end;
    reflexivity).
  (* S_Region_Step at-pre: both typings at R0 with In r R0 force
     T_Region_Active on BOTH sides (T_Region's ~In r R0 contradicts).
     Bodies typed under R0; IH on inner step applies directly. *)
  all: try (
    match goal with
    | [ Hte : has_type ?R0 ?G0 (ERegion ?r ?e_body) _ _,
        Hte' : has_type ?R0 ?G0 (ERegion ?r ?e_body') _ _,
        Hin : In ?r ?R0 |- _ ] =>
        inversion Hte; subst; [exfalso; auto |];
        inversion Hte'; subst; [exfalso; auto |];
        match goal with
        | [ Hvt : has_type ?R0 ?G0 ?e_body ?T0 _,
            Hvt' : has_type ?R0 ?G0 ?e_body' ?T' _ |- _ ] =>
            eapply IHHstep; [reflexivity | reflexivity | exact Hvt | exact Hvt']
        end
    end).
  (* S_Region_Exit at-pre: Hte = T_Region_Active (In r R0 forces).
     Body v typed under R0 at T0. Hte' is v at R0 directly. Two
     typings of same value at same R → type_determinacy. *)
  all: try (
    match goal with
    | [ Hte : has_type ?R0 ?G0 (ERegion ?r ?v) _ _,
        Hte' : has_type ?R0 ?G0 ?v _ _,
        Hv : is_value ?v,
        Hin : In ?r ?R0 |- _ ] =>
        inversion Hte; subst; [exfalso; auto |];
        match goal with
        | [ Hvt : has_type ?R0 ?G0 ?v ?T0 _ |- ?T0 = _ ] =>
            eapply type_determinacy;
              [ exact Hvt | exact Hte' | apply ctx_types_agree_refl ]
        end
    end).
  (* Cluster A — beta-reduction. For each: invert Hte, value_context_
     unchanged, subst_preserves_typing_strong to construct a typing
     of the post-step expression at the SAME T as the original, then
     type_determinacy aligns it with Hte''s T'. *)
  (* S_Let_Val *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELet ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply type_determinacy;
              [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_LetLin_Val *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELetLin ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply type_determinacy;
              [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_App_Fun: use Tann (ELam annotation) and Tfa (TFun arg) as
     separate pattern vars; inversion Hlam forces them equal. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v2,
        Hte : has_type ?R ?G (EApp (ELam ?T1 ?ebody) ?v2) ?T2 ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v2 ?ebody) ?T' ?Gb |- ?T2 = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hlam : has_type ?Rx ?Gx (ELam ?Tann ?ebody2)
                                    (TFun ?Tfa ?Tfr) ?Gmidx,
            Harg : has_type ?Rx ?Gmidx ?v2 ?Tfa ?Ga2 |- _ ] =>
            assert (HGlam : Gmidx = Gx) by
              (eapply value_context_unchanged;
               [exact Hlam | constructor]);
            subst Gmidx;
            assert (HGv : Ga2 = Gx) by
              (eapply value_context_unchanged; eassumption);
            subst Ga2;
            inversion Hlam; subst;
            match goal with
            | [ Hbody : has_type ?Rx (ctx_extend ?Gx ?Tfa) ?ebody2 ?Tfr
                                  ((?Tfa, true) :: ?Gx) |- _ ] =>
                destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                            Hbody Harg Hv) as [_ Hsub];
                eapply type_determinacy;
                  [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
            end
        end
    end
  ].
  (* S_If_True *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool true) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e2x ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool true) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e2x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply type_determinacy;
              [exact Hbranch | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_If_False *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool false) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e3x ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool false) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e3x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply type_determinacy;
              [exact Hbranch | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_Case_Inl *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInl _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInl _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T1 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T1) ?ebody ?T
                                              ((?T1, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T' ?Gb
        |- ?T = ?T' ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply type_determinacy;
          [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
    end
  ].
  (* S_Case_Inr *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInr _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInr _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T2 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T2) ?ebody ?T
                                              ((?T2, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T' ?Gb
        |- ?T = ?T' ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply type_determinacy;
          [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
    end
  ].
  (* Cluster B — congruence cases close via the IH's type-equality.
     The IH for [step_preserves_type] handles the inner step
     directly: given e1 → e1' and typings of e1 / e1' at any types
     (each under its respective R / R'), the IH yields type-equality.
     No need to dispatch on R = R' first — the IH is universal in
     the typings' region envs. *)
  (* S_StringConcat_Step1 — inner step on e1. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EStringConcat _ _) _ _,
        Hte' : has_type _ _ (EStringConcat _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TString ?r) ?Gmid,
            H1' : has_type ?R' ?G ?e1' (TString ?r') ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_App_Step1, S_App_Step2 — TFun T1 T2; IH gives T1 = T1' AND T2 = T2'. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EApp _ _) _ _,
        Hte' : has_type _ _ (EApp _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TFun ?T1a ?T2a) ?Gmid,
            H1' : has_type ?R' ?G ?e1' (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Let_Step, S_LetLin_Step — IH on e1 → e1' aligns T1, then need
     T = T' from the body. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ELet _ _) _ _,
        Hte' : has_type _ _ (ELet _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1a ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1b ?Gmid',
            H2 : has_type ?R (ctx_extend ?Gmid ?T1a) ?e2 ?T ((?T1a, true) :: ?Ga),
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1b) ?e2 ?T' ((?T1b, true) :: ?Gb) |- _ ] =>
            (* IH aligns T1a = T1b *)
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            (* Now H2 and H2' both have body context ctx_extend ?_ T1a.
               typing_types_agree composed via G aligns Gmid and Gmid'. *)
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ G _);
                  [ exact (typing_types_agree _ _ _ _ _ H1)
                  | apply ctx_types_agree_sym;
                    exact (typing_types_agree _ _ _ _ _ H1') ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].
  (* S_LetLin_Step — same as S_Let_Step. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ELetLin _ _) _ _,
        Hte' : has_type _ _ (ELetLin _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1a ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1b ?Gmid',
            H2 : has_type ?R (ctx_extend ?Gmid ?T1a) ?e2 ?T ((?T1a, true) :: ?Ga),
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1b) ?e2 ?T' ((?T1b, true) :: ?Gb) |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ G _);
                  [ exact (typing_types_agree _ _ _ _ _ H1)
                  | apply ctx_types_agree_sym;
                    exact (typing_types_agree _ _ _ _ _ H1') ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].
  (* ===== Second-child congruences (inner step on e2, v1 value) ===== *)
  (* S_StringConcat_Step2 *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hv : is_value ?v1,
        Hte : has_type _ _ (EStringConcat ?v1 _) _ _,
        Hte' : has_type _ _ (EStringConcat ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H2' : has_type ?R' ?Gmid' ?e2' (TString ?r') ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_App_Step2 *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hv : is_value ?v1,
        Hte : has_type _ _ (EApp ?v1 _) _ _,
        Hte' : has_type _ _ (EApp ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T1a ?Ga,
            H1' : has_type ?R' ?G ?v1 (TFun ?T1b ?T2b) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' ?T1b ?Gb |- _ ] =>
            (* Align v1's TFun types via type_determinacy. *)
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            assert (HTfun : TFun T1a T2a = TFun T1b T2b)
              by (eapply type_determinacy;
                  [exact H1 | exact H1' | apply ctx_types_agree_refl]);
            inversion HTfun; subst;
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            exact Hteq
        end
    end
  ].
  (* S_Pair_Step1, S_Pair_Step2: TProd T1 T2 outer constraints both children. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EPair _ _) _ _,
        Hte' : has_type _ _ (EPair _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1 ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1' ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T1'; reflexivity
        end
    end
  ].
  (* ===== Unary congruences (single child) ===== *)
  (* S_Inl_Step: TSum T1 T2; outer T = TSum T1 T2 constrains T1. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EInl _ _) _ _,
        Hte' : has_type _ _ (EInl _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T1 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T1' ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T1'; reflexivity
        end
    end
  ].
  (* S_Inr_Step: symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EInr _ _) _ _,
        Hte' : has_type _ _ (EInr _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T2' ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T2'; reflexivity
        end
    end
  ].
  (* S_Borrow_Step: T_Borrow forces e = EVar (no step), T_Borrow_Val
     forces e is value (no step). Vacuous. *)
  all: try solve [
    match goal with
    | [ Hin : (_, _, _) -->> (_, _, _),
        Hte : has_type _ _ (EBorrow _) _ _ |- _ ] =>
        inversion Hte; subst;
        [ inversion Hin
        | exfalso;
          match goal with
          | [ Hv : is_value ?v |- _ ] =>
              eapply values_dont_step; [exact Hv | exact Hin]
          end
        ]
    end
  ].
  (* S_Drop_Step: T_Drop's inner type is independent; use sibling-
     less approach via IH directly (the inner step's IH provides
     type-equality even though outer T is fixed at TBase TUnit). *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EDrop _) _ _,
        Hte' : has_type _ _ (EDrop _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        reflexivity
    end
  ].
  (* S_Copy_Step: T_Copy outputs TProd T T — symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ECopy _) _ _,
        Hte' : has_type _ _ (ECopy _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?Ta ?Ga,
            H1' : has_type ?R' ?G ?e' ?Tb ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst Tb; reflexivity
        end
    end
  ].
  (* S_If_Step: cond at TBase TBool, branches at outer T. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EIf _ _ _) _ _,
        Hte' : has_type _ _ (EIf _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H2 : has_type ?R ?Gmid ?e2 ?T ?Ga,
            H2' : has_type ?R' ?Gmid' ?e2 ?T' ?Gb |- _ ] =>
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ _ _);
                  [ eapply typing_types_agree; eassumption
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; eassumption ]);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrMid ]
        end
    end
  ].
  (* S_Fst_Step: T_Fst's T2 independent. Use IH directly — IH on
     the inner step preserves type, so e and e' have same TProd type.
     Output's T1 component (= outer T) follows. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EFst _) _ _,
        Hte' : has_type _ _ (EFst _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e (TProd ?Ta1 ?Ta2) ?Ga,
            H1' : has_type ?R' ?G ?e' (TProd ?Tb1 ?Tb2) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Snd_Step: T_Snd's T1 independent. Symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ESnd _) _ _,
        Hte' : has_type _ _ (ESnd _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e (TProd ?Ta1 ?Ta2) ?Ga,
            H1' : has_type ?R' ?G ?e' (TProd ?Tb1 ?Tb2) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Case_Step: scrutinee steps. Outer T comes from branches; IH
     gives TSum T1 T2 alignment. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ECase _ _ _) _ _,
        Hte' : has_type _ _ (ECase _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ Hs : has_type ?R ?G ?e (TSum ?Ta1 ?Ta2) ?Gmid,
            Hb1 : has_type ?R (ctx_extend ?Gmid ?Ta1) ?eb1 ?T
                              ((?Ta1, true) :: ?Gfin),
            Hs' : has_type ?R' ?G ?e' (TSum ?Tb1 ?Tb2) ?Gmid',
            Hb1' : has_type ?R' (ctx_extend ?Gmid' ?Tb1) ?eb1 ?T'
                              ((?Tb1, true) :: ?Gfin') |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hs _ _ Hs') as Hsum;
            inversion Hsum; subst;
            (* Now Ta1 = Tb1 and Ta2 = Tb2. Apply type_determinacy on
               branch eb1 (same expression in agreeing contexts). *)
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ _ _);
                  [ eapply typing_types_agree; eassumption
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; eassumption ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid Ta1) (ctx_extend Gmid' Ta1))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact Hb1 | exact Hb1' | exact HagrExt ]
        end
    end
  ].
  (* ===== Atomic compound-value cases (post = some value form) ===== *)
  (* S_Copy: ECopy v -> EPair v v. Hte (T_Copy) gives outer TProd T T;
     Hte' (T_Pair) gives outer TProd Ta1 Ta2. By T_Copy structure,
     Ta1 = Ta2 = v's type. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type _ _ (ECopy _) _ _,
        Hte' : has_type _ _ (EPair _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v ?Ta ?Ga,
            H1' : has_type ?R ?G ?v ?Tb ?Gmid |- _ ] =>
            assert (HTeq : Ta = Tb)
              by (eapply type_determinacy;
                  [ exact H1 | exact H1' | apply ctx_types_agree_refl ]);
            subst Tb; reflexivity
        end
    end
  ].
  (* S_Fst: EFst (EPair v1 v2) -> v1. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type _ _ (EFst (EPair ?v1 ?v2)) _ _,
        Hte' : has_type _ _ ?v1 _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T2) ?Gpost |- _ ] =>
            inversion Hp; subst;
            match goal with
            | [ Hv1t : has_type ?R ?G ?v1 ?T1 ?Gmid |- _ ] =>
                assert (HTeq : T1 = _)
                  by (eapply type_determinacy;
                      [ exact Hv1t | exact Hte' | apply ctx_types_agree_refl ]);
                exact HTeq
            end
        end
    end
  ].
  (* S_Snd: ESnd (EPair v1 v2) -> v2. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type _ _ (ESnd (EPair ?v1 ?v2)) _ _,
        Hte' : has_type _ _ ?v2 _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T2) ?Gpost |- _ ] =>
            inversion Hp; subst;
            match goal with
            | [ Hv2t : has_type _ _ ?v2 ?T2 _ |- _ ] =>
                assert (HTeq : T2 = _)
                  by (eapply type_determinacy;
                      [ exact Hv2t | exact Hte' | apply ctx_types_agree_refl ]);
                exact HTeq
            end
        end
    end
  ].
  (* S_Region_Exit: ERegion r v -> v (R becomes remove_first r R).
     Hte is T_Region_Active; Hte' types v at T'. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type _ _ (ERegion _ _) ?T _,
        Hte' : has_type _ _ ?v ?T' _ |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?T ?Gmid |- _ ] =>
            eapply type_determinacy;
              [ exact Hvt | exact Hte' | apply ctx_types_agree_refl ]
        end
    end
  ].
  (* S_Region_Enter: ERegion r e (under R) -> ERegion r e (under r::R).
     Both Hte and Hte' invert to give inner e's typing under (r :: R).
     The 4 inversion sub-goals split by T_Region / T_Region_Active. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T _,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T' _ |- ?T = ?T' ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first
          [ exfalso; tauto
          | exfalso;
            match goal with
            | [ H : ~ In ?r (?r :: _) |- _ ] =>
                apply H; left; reflexivity
            end
          | match goal with
            | [ H1 : has_type ?R ?G ?e ?T ?Ga,
                H2 : has_type ?R ?G ?e ?T' ?Gb |- ?T = ?T' ] =>
                eapply type_determinacy;
                  [ exact H1 | exact H2 | apply ctx_types_agree_refl ]
            end ]
    end
  ].
  (* 12 cases remain. Each requires per-case adjustment beyond the
     mass clone-out:
       - S_Pair_Step1/2, S_App_Step2: need IH on stepping child +
         type_determinacy on unchanged sibling to align BOTH outer
         type components.
       - S_StringConcat_Step2: similar to App_Step2.
       - S_Let_Step, S_LetLin_Step, S_Case_Step: ctx_extend-with-
         unfixed-T1 inversion needs explicit binder names that don't
         match Coq's auto-renaming consistently.
       - S_If_Step: inner step on cond e1 (TBase TBool); the e2/e3
         branches need ctx_types_agree composition.
       - S_Copy atomic (EPair v v from ECopy v): need extra
         is_linear_ty premise discharge.
       - S_Fst, S_Snd atomic: pattern var bind to outer goal's T
         doesn't propagate through nested match cleanly.
       - S_Region_Exit, S_Region_Step: as documented. *)
  (* Remaining 8 cases: S_StringConcat_Step2, S_Let_Step, S_LetLin_Step,
     S_App_Step2, S_If_Step, S_Pair_Step1, S_Pair_Step2, S_Case_Step.
     These are the per-goal cases that step_preserves_type also needed
     specific tactic blocks for (lines 4389+ of the original proof).
     Pending: copy & adapt those blocks. Each ~30 LOC. *)
  (* ===== Per-case closers for the 8 remaining at-pre cases =====
     In at-pre framing both [Hte] and [Hte'] are at the same R0
     (the pre-step region env). After [inversion Hte; subst;
     inversion Hte'; subst], all child typings live at R0 too, so
     we don't need [step_R_change_shape] dispatch — only the
     LEFT-branch logic from [step_preserves_type]'s per-goal blocks
     applies. We invoke [IHHstep] (at-pre IH) by name rather than
     pattern-matching on its type, since the at-pre IH has a
     different shape from [step_preserves_type]'s. *)

  (* Case 1: S_StringConcat_Step2 — EStringConcat v1 e2 -> EStringConcat v1 e2'. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte  : has_type _ _ (EStringConcat ?v1 _) _ _,
        Hte' : has_type _ _ (EStringConcat ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H2  : has_type ?R ?Gmid  ?e2  (TString _) _,
            H2' : has_type ?R ?Gmid' ?e2' (TString _) _ |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].

  (* Case 2: S_Let_Step — ELet e1 e2 -> ELet e1' e2. IH aligns T1,
     then type_determinacy on body under agreeing extended contexts. *)
  all: try solve [
    match goal with
    | [ Hte  : has_type _ _ (ELet _ _) _ _,
        Hte' : has_type _ _ (ELet _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R ?G ?e1  ?T1a ?Gmid,
            H1' : has_type ?R ?G ?e1' ?T1b ?Gmid',
            H2  : has_type ?R (ctx_extend ?Gmid  ?T1a) ?e2 _ _,
            H2' : has_type ?R (ctx_extend ?Gmid' ?T1b) ?e2 _ _ |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (eapply ctx_types_agree_trans;
                  [ eapply typing_types_agree; exact H1
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; exact H1' ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy; [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].

  (* Case 3: S_LetLin_Step — same structure as S_Let_Step. *)
  all: try solve [
    match goal with
    | [ Hte  : has_type _ _ (ELetLin _ _) _ _,
        Hte' : has_type _ _ (ELetLin _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R ?G ?e1  ?T1a ?Gmid,
            H1' : has_type ?R ?G ?e1' ?T1b ?Gmid',
            H2  : has_type ?R (ctx_extend ?Gmid  ?T1a) ?e2 _ _,
            H2' : has_type ?R (ctx_extend ?Gmid' ?T1b) ?e2 _ _ |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (eapply ctx_types_agree_trans;
                  [ eapply typing_types_agree; exact H1
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; exact H1' ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy; [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].

  (* Case 4: S_App_Step2 — EApp v1 e2 -> EApp v1 e2'. v1's TFun
     typings align via type_determinacy under shared R; then IH on
     (e2, e2') closes. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte  : has_type _ _ (EApp ?v1 _) _ _,
        Hte' : has_type _ _ (EApp ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ Hv1  : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
            H2   : has_type ?R ?Gmid  ?e2  ?T1a _,
            Hv1' : has_type ?R ?G ?v1 (TFun ?T1b ?T2b) ?Gmid',
            H2'  : has_type ?R ?Gmid' ?e2' ?T1b _ |- _ ] =>
            assert (Gmid = G) by
              (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
            assert (Gmid' = G) by
              (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
            subst Gmid Gmid';
            assert (HTfun : TFun T1a T2a = TFun T1b T2b)
              by (eapply type_determinacy;
                  [ exact Hv1 | exact Hv1' | apply ctx_types_agree_refl ]);
            inversion HTfun; subst;
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            exact Hteq
        end
    end
  ].

  (* Case 5: S_If_Step — EIf e1 e2 e3 -> EIf e1' e2 e3. Branches
     are at outer T; align Gmid via cond's typings then
     type_determinacy on branch e2. *)
  all: try solve [
    match goal with
    | [ Hte  : has_type _ _ (EIf _ _ _) _ _,
        Hte' : has_type _ _ (EIf _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R ?G ?e1  (TBase TBool) ?Gmid,
            H1' : has_type ?R ?G ?e1' (TBase TBool) ?Gmid',
            H2  : has_type ?R ?Gmid  ?e2 _ _,
            H2' : has_type ?R ?Gmid' ?e2 _ _ |- _ ] =>
            assert (Hagr : ctx_types_agree Gmid Gmid')
              by (eapply ctx_types_agree_trans;
                  [ eapply typing_types_agree; exact H1
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; exact H1' ]);
            eapply type_determinacy; [ exact H2 | exact H2' | exact Hagr ]
        end
    end
  ].

  (* Case 6: S_Pair_Step1 — EPair e1 e2 -> EPair e1' e2.
     IH aligns T1; align Gmid via e1 typings; type_determinacy on
     unchanged sibling e2 aligns T2. *)
  all: try solve [
    match goal with
    | [ Hte  : has_type _ _ (EPair _ _) _ _,
        Hte' : has_type _ _ (EPair _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R ?G ?e1  ?T1a ?Gmid,
            H1' : has_type ?R ?G ?e1' ?T1b ?Gmid',
            H2  : has_type ?R ?Gmid  ?e2 ?T2a _,
            H2' : has_type ?R ?Gmid' ?e2 ?T2b _ |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            assert (Hagr : ctx_types_agree Gmid Gmid')
              by (eapply ctx_types_agree_trans;
                  [ eapply typing_types_agree; exact H1
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; exact H1' ]);
            assert (HT2 : T2a = T2b)
              by (eapply type_determinacy; [ exact H2 | exact H2' | exact Hagr ]);
            subst T2b; reflexivity
        end
    end
  ].

  (* Case 7: S_Pair_Step2 — EPair v1 e2 -> EPair v1 e2'. v1 value;
     T1 aligns via type_determinacy on v1; T2 via IH on (e2, e2'). *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte  : has_type _ _ (EPair ?v1 _) _ _,
        Hte' : has_type _ _ (EPair ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ Hv1  : has_type ?R ?G ?v1 ?T1a ?Gmid,
            H2   : has_type ?R ?Gmid  ?e2  _ _,
            Hv1' : has_type ?R ?G ?v1 ?T1b ?Gmid',
            H2'  : has_type ?R ?Gmid' ?e2' _ _ |- _ ] =>
            assert (Gmid = G) by
              (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
            assert (Gmid' = G) by
              (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
            subst Gmid Gmid';
            assert (HT1 : T1a = T1b)
              by (eapply type_determinacy;
                  [ exact Hv1 | exact Hv1' | apply ctx_types_agree_refl ]);
            subst T1b;
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as HT2;
            subst; reflexivity
        end
    end
  ].

  (* Case 8: S_Case_Step — ECase e e1 e2 -> ECase e' e1 e2.
     IH on scrutinee aligns TSum components; branches at outer T
     under ctx_extend Gmid T1; align via type_determinacy. *)
  all: try solve [
    match goal with
    | [ Hte  : has_type _ _ (ECase _ _ _) _ _,
        Hte' : has_type _ _ (ECase _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ Hs   : has_type ?R ?G ?e  (TSum ?Ta1 ?Ta2) ?Gmid,
            Hb1  : has_type ?R (ctx_extend ?Gmid  ?Ta1) ?eb1 _ _,
            Hs'  : has_type ?R ?G ?e' (TSum ?Tb1 ?Tb2) ?Gmid',
            Hb1' : has_type ?R (ctx_extend ?Gmid' ?Tb1) ?eb1 _ _ |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hs _ _ Hs') as Hsum;
            inversion Hsum; subst;
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (eapply ctx_types_agree_trans;
                  [ eapply typing_types_agree; exact Hs
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; exact Hs' ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid Ta1) (ctx_extend Gmid' Ta1))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy; [ exact Hb1 | exact Hb1' | exact HagrExt ]
        end
    end
  ].
  (* 5 cases remain after the [all: try solve [...]] chain:
     S_StringConcat_Step2, S_App_Step2, S_Snd atomic, S_Case_Step,
     S_Copy. Each closed via an explicit [1: { ... }] block — port
     of the corresponding upstream [step_preserves_type] tactic.
     Order from [Show Existentials] confirmed empirically. *)

  (* Goal 1: S_StringConcat_Step2 — EStringConcat v1 e2 → EStringConcat v1 e2'.
     Both typings give TString r; IH on (e2, e2') yields TString r =
     TString r'; inversion + reflexivity. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hv : is_value ?v1,
        Hv1 : has_type _ _ ?v1 _ ?G',
        Hv1' : has_type _ _ ?v1 _ ?G'0 |- _ ] =>
        assert (G' = G0) by
          (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
        assert (G'0 = G0) by
          (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
        subst G' G'0
    end.
    match goal with
    | [ H2 : has_type _ _ ?e2 (TString _) _,
        H2' : has_type _ _ ?e2' (TString _) _ |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
        inversion Hteq; reflexivity
    end.
  }

  (* Goal 2: S_App_Step2 — EApp v1 e2 → EApp v1 e2'. Both typings at R0
     (at-pre invariant); v1's two TFun typings align via type_determinacy. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hv : is_value ?v1,
        Hv1 : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
        Hv1' : has_type ?R ?G ?v1 (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
        assert (Gmid' = G) by
          (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
        subst Gmid Gmid';
        assert (HTfun : TFun T1a T2a = TFun T1b T2b)
          by (eapply type_determinacy;
              [exact Hv1 | exact Hv1' | apply ctx_types_agree_refl]);
        inversion HTfun; subst; reflexivity
    end.
  }

  (* Goal 3: S_Snd atomic — ESnd (EPair v1 v2) → v2. No R change.
     T_Snd inversion → T_Pair on EPair v1 v2 → gives v2's typing
     with type matching outer T. type_determinacy on v2 closes. *)
  1: {
    inversion Hte; subst.
    match goal with
    | [ Hp : has_type _ _ (EPair ?v1 ?v2) (TProd _ _) _ |- _ ] =>
        inversion Hp; subst
    end.
    match goal with
    | [ Hv1 : is_value ?v1,
        Hv1t : has_type ?R ?G ?v1 ?T1 ?Gmid,
        Hv2t : has_type ?R ?Gmid ?v2 ?T2 _,
        Hte' : has_type ?R ?G ?v2 ?T' _
        |- ?T2 = ?T' ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1t | exact Hv1]);
        subst Gmid;
        eapply type_determinacy;
          [ exact Hv2t | exact Hte' | apply ctx_types_agree_refl ]
    end.
  }

  (* Goal 4: S_Case_Step — ECase e e1 e2 → ECase e' e1 e2. Both typings
     at R0 (at-pre invariant). IH on scrutinee gives TSum alignment;
     branch e1 closes via type_determinacy under ctx_extend with shared T1. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        Hsc : has_type _ _ ?es (TSum _ _) _,
        Hsc' : has_type _ _ ?es' (TSum _ _) _ |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hsc _ _ Hsc') as Hsum;
        inversion Hsum; subst
    end.
    match goal with
    | [ Hsc : has_type ?R ?G ?es (TSum ?T1 _) ?Gmid,
        Hsc' : has_type ?R ?G ?es' (TSum ?T1 _) ?Gmid' |- _ ] =>
        assert (HagrMid : ctx_types_agree Gmid Gmid')
          by (eapply ctx_types_agree_trans;
              [ eapply typing_types_agree; exact Hsc
              | apply ctx_types_agree_sym; eapply typing_types_agree; exact Hsc' ]);
        assert (HagrExt : ctx_types_agree (ctx_extend Gmid T1) (ctx_extend Gmid' T1))
          by (apply ctx_extend_types_agree; assumption)
    end.
    match goal with
    | [ Hb1 : has_type ?R (ctx_extend ?Gmid ?T1) ?eb1 ?Ta _,
        Hb1' : has_type ?R (ctx_extend ?Gmid' ?T1) ?eb1 ?Tb _,
        Hag : ctx_types_agree (ctx_extend ?Gmid ?T1) (ctx_extend ?Gmid' ?T1)
        |- ?Ta = ?Tb ] =>
        eapply type_determinacy; [ exact Hb1 | exact Hb1' | exact Hag ]
    end.
  }

  (* Goal 5: S_Copy atomic — ECopy v → EPair v v. No R change.
     T_Copy outer = TProd T T (v : T). T_Pair outer = TProd T1' T2'.
     type_determinacy on v aligns T1' = T2' = T. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hv : is_value ?v,
        Hvt : has_type ?R ?G ?v ?T _,
        Hv1t : has_type ?R ?G ?v ?T1' ?Gmid,
        Hv2t : has_type ?R ?Gmid ?v ?T2' _
        |- TProd ?T ?T = TProd ?T1' ?T2' ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1t | exact Hv]);
        subst Gmid;
        assert (HT1 : T = T1')
          by (eapply type_determinacy;
              [exact Hvt | exact Hv1t | apply ctx_types_agree_refl]);
        assert (HT2 : T = T2')
          by (eapply type_determinacy;
              [exact Hvt | exact Hv2t | apply ctx_types_agree_refl]);
        subst T1' T2'; reflexivity
    end.
  }
Qed.

(** ** Step preserves type

    If [e] steps to [e'] and BOTH have typings, then they're at the
    SAME type. The conclusion's [T = T'] equality is what unblocks
    the "type-alignment-circular" Cluster B cases of
    [step_output_context_eq] (Lemma B) — for cases like S_Let_Step
    where the inner step's type isn't fixed by the outer compound's
    type.

    The lemma's own induction handles the circularity because, at
    each congruence case, the IH for the inner step provides
    type-alignment for the inner sub-expressions (which then forces
    the outer T = T' via the typing rule's structure).

    Proof structure mirrors [step_output_context_eq] but produces a
    type-equality instead of an output-context-equality. *)
Lemma step_preserves_type :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G_a,
      R; G |- e : T -| G_a ->
      forall T' G_b,
        R'; G |- e' : T' -| G_b ->
        T = T'.
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    intros G0 T0 Ga Hte T' Gb Hte'.
  (* Atomic axiom cases that close by inversion-chain + reflexivity
     (the same 4 that closed in Lemma B atomic-axiom block). *)
  all: try (
    inversion Hte; subst;
    inversion Hte'; subst;
    repeat match goal with
    | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EI32 _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ EUnit _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EBool _) _ _ |- _ ] =>
        inversion H; subst; clear H
    end;
    reflexivity).
  (* Cluster A — beta-reduction. For each: invert Hte, value_context_
     unchanged, subst_preserves_typing_strong to construct a typing
     of the post-step expression at the SAME T as the original, then
     type_determinacy aligns it with Hte''s T'. *)
  (* S_Let_Val *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELet ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply type_determinacy;
              [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_LetLin_Val *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELetLin ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply type_determinacy;
              [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_App_Fun: use Tann (ELam annotation) and Tfa (TFun arg) as
     separate pattern vars; inversion Hlam forces them equal. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v2,
        Hte : has_type ?R ?G (EApp (ELam ?T1 ?ebody) ?v2) ?T2 ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v2 ?ebody) ?T' ?Gb |- ?T2 = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hlam : has_type ?Rx ?Gx (ELam ?Tann ?ebody2)
                                    (TFun ?Tfa ?Tfr) ?Gmidx,
            Harg : has_type ?Rx ?Gmidx ?v2 ?Tfa ?Ga2 |- _ ] =>
            assert (HGlam : Gmidx = Gx) by
              (eapply value_context_unchanged;
               [exact Hlam | constructor]);
            subst Gmidx;
            assert (HGv : Ga2 = Gx) by
              (eapply value_context_unchanged; eassumption);
            subst Ga2;
            inversion Hlam; subst;
            match goal with
            | [ Hbody : has_type ?Rx (ctx_extend ?Gx ?Tfa) ?ebody2 ?Tfr
                                  ((?Tfa, true) :: ?Gx) |- _ ] =>
                destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                            Hbody Harg Hv) as [_ Hsub];
                eapply type_determinacy;
                  [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
            end
        end
    end
  ].
  (* S_If_True *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool true) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e2x ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool true) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e2x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply type_determinacy;
              [exact Hbranch | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_If_False *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool false) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e3x ?T' ?Gb |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool false) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e3x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply type_determinacy;
              [exact Hbranch | exact Hte' | apply ctx_types_agree_refl]
        end
    end
  ].
  (* S_Case_Inl *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInl _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInl _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T1 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T1) ?ebody ?T
                                              ((?T1, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T' ?Gb
        |- ?T = ?T' ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply type_determinacy;
          [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
    end
  ].
  (* S_Case_Inr *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInr _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInr _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T2 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T2) ?ebody ?T
                                              ((?T2, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T' ?Gb
        |- ?T = ?T' ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply type_determinacy;
          [exact Hsub | exact Hte' | apply ctx_types_agree_refl]
    end
  ].
  (* Cluster B — congruence cases close via the IH's type-equality.
     The IH for [step_preserves_type] handles the inner step
     directly: given e1 → e1' and typings of e1 / e1' at any types
     (each under its respective R / R'), the IH yields type-equality.
     No need to dispatch on R = R' first — the IH is universal in
     the typings' region envs. *)
  (* S_StringConcat_Step1 — inner step on e1. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EStringConcat _ _) _ _,
        Hte' : has_type _ _ (EStringConcat _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TString ?r) ?Gmid,
            H1' : has_type ?R' ?G ?e1' (TString ?r') ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_App_Step1, S_App_Step2 — TFun T1 T2; IH gives T1 = T1' AND T2 = T2'. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EApp _ _) _ _,
        Hte' : has_type _ _ (EApp _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TFun ?T1a ?T2a) ?Gmid,
            H1' : has_type ?R' ?G ?e1' (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Let_Step, S_LetLin_Step — IH on e1 → e1' aligns T1, then need
     T = T' from the body. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ELet _ _) _ _,
        Hte' : has_type _ _ (ELet _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1a ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1b ?Gmid',
            H2 : has_type ?R (ctx_extend ?Gmid ?T1a) ?e2 ?T ((?T1a, true) :: ?Ga),
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1b) ?e2 ?T' ((?T1b, true) :: ?Gb) |- _ ] =>
            (* IH aligns T1a = T1b *)
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            (* Now H2 and H2' both have body context ctx_extend ?_ T1a.
               typing_types_agree composed via G aligns Gmid and Gmid'. *)
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ G _);
                  [ exact (typing_types_agree _ _ _ _ _ H1)
                  | apply ctx_types_agree_sym;
                    exact (typing_types_agree _ _ _ _ _ H1') ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].
  (* S_LetLin_Step — same as S_Let_Step. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ELetLin _ _) _ _,
        Hte' : has_type _ _ (ELetLin _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1a ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1b ?Gmid',
            H2 : has_type ?R (ctx_extend ?Gmid ?T1a) ?e2 ?T ((?T1a, true) :: ?Ga),
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1b) ?e2 ?T' ((?T1b, true) :: ?Gb) |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as HT1;
            subst T1b;
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ G _);
                  [ exact (typing_types_agree _ _ _ _ _ H1)
                  | apply ctx_types_agree_sym;
                    exact (typing_types_agree _ _ _ _ _ H1') ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid T1a) (ctx_extend Gmid' T1a))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrExt ]
        end
    end
  ].
  (* ===== Second-child congruences (inner step on e2, v1 value) ===== *)
  (* S_StringConcat_Step2 *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hv : is_value ?v1,
        Hte : has_type _ _ (EStringConcat ?v1 _) _ _,
        Hte' : has_type _ _ (EStringConcat ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H2' : has_type ?R' ?Gmid' ?e2' (TString ?r') ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_App_Step2 *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hv : is_value ?v1,
        Hte : has_type _ _ (EApp ?v1 _) _ _,
        Hte' : has_type _ _ (EApp ?v1 _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T1a ?Ga,
            H1' : has_type ?R' ?G ?v1 (TFun ?T1b ?T2b) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' ?T1b ?Gb |- _ ] =>
            (* Align v1's TFun types via type_determinacy. *)
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            assert (HTfun : TFun T1a T2a = TFun T1b T2b)
              by (eapply type_determinacy;
                  [exact H1 | exact H1' | apply ctx_types_agree_refl]);
            inversion HTfun; subst;
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
            exact Hteq
        end
    end
  ].
  (* S_Pair_Step1, S_Pair_Step2: TProd T1 T2 outer constraints both children. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EPair _ _) _ _,
        Hte' : has_type _ _ (EPair _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 ?T1 ?Gmid,
            H1' : has_type ?R' ?G ?e1' ?T1' ?Gmid' |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T1'; reflexivity
        end
    end
  ].
  (* ===== Unary congruences (single child) ===== *)
  (* S_Inl_Step: TSum T1 T2; outer T = TSum T1 T2 constrains T1. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EInl _ _) _ _,
        Hte' : has_type _ _ (EInl _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T1 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T1' ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T1'; reflexivity
        end
    end
  ].
  (* S_Inr_Step: symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EInr _ _) _ _,
        Hte' : has_type _ _ (EInr _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T2' ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst T2'; reflexivity
        end
    end
  ].
  (* S_Borrow_Step: T_Borrow forces e = EVar (no step), T_Borrow_Val
     forces e is value (no step). Vacuous. *)
  all: try solve [
    match goal with
    | [ Hin : (_, _, _) -->> (_, _, _),
        Hte : has_type _ _ (EBorrow _) _ _ |- _ ] =>
        inversion Hte; subst;
        [ inversion Hin
        | exfalso;
          match goal with
          | [ Hv : is_value ?v |- _ ] =>
              eapply values_dont_step; [exact Hv | exact Hin]
          end
        ]
    end
  ].
  (* S_Drop_Step: T_Drop's inner type is independent; use sibling-
     less approach via IH directly (the inner step's IH provides
     type-equality even though outer T is fixed at TBase TUnit). *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EDrop _) _ _,
        Hte' : has_type _ _ (EDrop _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        reflexivity
    end
  ].
  (* S_Copy_Step: T_Copy outputs TProd T T — symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ECopy _) _ _,
        Hte' : has_type _ _ (ECopy _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?Ta ?Ga,
            H1' : has_type ?R' ?G ?e' ?Tb ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            subst Tb; reflexivity
        end
    end
  ].
  (* S_If_Step: cond at TBase TBool, branches at outer T. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EIf _ _ _) _ _,
        Hte' : has_type _ _ (EIf _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H2 : has_type ?R ?Gmid ?e2 ?T ?Ga,
            H2' : has_type ?R' ?Gmid' ?e2 ?T' ?Gb |- _ ] =>
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ _ _);
                  [ eapply typing_types_agree; eassumption
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; eassumption ]);
            eapply type_determinacy;
              [ exact H2 | exact H2' | exact HagrMid ]
        end
    end
  ].
  (* S_Fst_Step: T_Fst's T2 independent. Use IH directly — IH on
     the inner step preserves type, so e and e' have same TProd type.
     Output's T1 component (= outer T) follows. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (EFst _) _ _,
        Hte' : has_type _ _ (EFst _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e (TProd ?Ta1 ?Ta2) ?Ga,
            H1' : has_type ?R' ?G ?e' (TProd ?Tb1 ?Tb2) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Snd_Step: T_Snd's T1 independent. Symmetric. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ESnd _) _ _,
        Hte' : has_type _ _ (ESnd _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e (TProd ?Ta1 ?Ta2) ?Ga,
            H1' : has_type ?R' ?G ?e' (TProd ?Tb1 ?Tb2) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1 _ _ H1') as Hteq;
            inversion Hteq; reflexivity
        end
    end
  ].
  (* S_Case_Step: scrutinee steps. Outer T comes from branches; IH
     gives TSum T1 T2 alignment. *)
  all: try solve [
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx),
              _ -> forall (_:ty) (_:ctx), _ -> _ = _,
        Hte : has_type _ _ (ECase _ _ _) _ _,
        Hte' : has_type _ _ (ECase _ _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ Hs : has_type ?R ?G ?e (TSum ?Ta1 ?Ta2) ?Gmid,
            Hb1 : has_type ?R (ctx_extend ?Gmid ?Ta1) ?eb1 ?T
                              ((?Ta1, true) :: ?Gfin),
            Hs' : has_type ?R' ?G ?e' (TSum ?Tb1 ?Tb2) ?Gmid',
            Hb1' : has_type ?R' (ctx_extend ?Gmid' ?Tb1) ?eb1 ?T'
                              ((?Tb1, true) :: ?Gfin') |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hs _ _ Hs') as Hsum;
            inversion Hsum; subst;
            (* Now Ta1 = Tb1 and Ta2 = Tb2. Apply type_determinacy on
               branch eb1 (same expression in agreeing contexts). *)
            assert (HagrMid : ctx_types_agree Gmid Gmid')
              by (apply (ctx_types_agree_trans _ _ _);
                  [ eapply typing_types_agree; eassumption
                  | apply ctx_types_agree_sym;
                    eapply typing_types_agree; eassumption ]);
            assert (HagrExt : ctx_types_agree
                              (ctx_extend Gmid Ta1) (ctx_extend Gmid' Ta1))
              by (apply ctx_extend_types_agree; assumption);
            eapply type_determinacy;
              [ exact Hb1 | exact Hb1' | exact HagrExt ]
        end
    end
  ].
  (* ===== Atomic compound-value cases (post = some value form) ===== *)
  (* S_Copy: ECopy v -> EPair v v. Hte (T_Copy) gives outer TProd T T;
     Hte' (T_Pair) gives outer TProd Ta1 Ta2. By T_Copy structure,
     Ta1 = Ta2 = v's type. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type _ _ (ECopy _) _ _,
        Hte' : has_type _ _ (EPair _ _) _ _ |- _ ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v ?Ta ?Ga,
            H1' : has_type ?R ?G ?v ?Tb ?Gmid |- _ ] =>
            assert (HTeq : Ta = Tb)
              by (eapply type_determinacy;
                  [ exact H1 | exact H1' | apply ctx_types_agree_refl ]);
            subst Tb; reflexivity
        end
    end
  ].
  (* S_Fst: EFst (EPair v1 v2) -> v1. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type _ _ (EFst (EPair ?v1 ?v2)) _ _,
        Hte' : has_type _ _ ?v1 _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T2) ?Gpost |- _ ] =>
            inversion Hp; subst;
            match goal with
            | [ Hv1t : has_type ?R ?G ?v1 ?T1 ?Gmid |- _ ] =>
                assert (HTeq : T1 = _)
                  by (eapply type_determinacy;
                      [ exact Hv1t | exact Hte' | apply ctx_types_agree_refl ]);
                exact HTeq
            end
        end
    end
  ].
  (* S_Snd: ESnd (EPair v1 v2) -> v2. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type _ _ (ESnd (EPair ?v1 ?v2)) _ _,
        Hte' : has_type _ _ ?v2 _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T2) ?Gpost |- _ ] =>
            inversion Hp; subst;
            match goal with
            | [ Hv2t : has_type _ _ ?v2 ?T2 _ |- _ ] =>
                assert (HTeq : T2 = _)
                  by (eapply type_determinacy;
                      [ exact Hv2t | exact Hte' | apply ctx_types_agree_refl ]);
                exact HTeq
            end
        end
    end
  ].
  (* S_Region_Exit: ERegion r v -> v (R becomes remove_first r R).
     Hte is T_Region_Active; Hte' types v at T'. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type _ _ (ERegion _ _) ?T _,
        Hte' : has_type _ _ ?v ?T' _ |- ?T = ?T' ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?T ?Gmid |- _ ] =>
            eapply type_determinacy;
              [ exact Hvt | exact Hte' | apply ctx_types_agree_refl ]
        end
    end
  ].
  (* S_Region_Enter: ERegion r e (under R) -> ERegion r e (under r::R).
     Both Hte and Hte' invert to give inner e's typing under (r :: R).
     The 4 inversion sub-goals split by T_Region / T_Region_Active. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T _,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T' _ |- ?T = ?T' ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first
          [ exfalso; tauto
          | exfalso;
            match goal with
            | [ H : ~ In ?r (?r :: _) |- _ ] =>
                apply H; left; reflexivity
            end
          | match goal with
            | [ H1 : has_type ?R ?G ?e ?T ?Ga,
                H2 : has_type ?R ?G ?e ?T' ?Gb |- ?T = ?T' ] =>
                eapply type_determinacy;
                  [ exact H1 | exact H2 | apply ctx_types_agree_refl ]
            end ]
    end
  ].
  (* 12 cases remain. Each requires per-case adjustment beyond the
     mass clone-out:
       - S_Pair_Step1/2, S_App_Step2: need IH on stepping child +
         type_determinacy on unchanged sibling to align BOTH outer
         type components.
       - S_StringConcat_Step2: similar to App_Step2.
       - S_Let_Step, S_LetLin_Step, S_Case_Step: ctx_extend-with-
         unfixed-T1 inversion needs explicit binder names that don't
         match Coq's auto-renaming consistently.
       - S_If_Step: inner step on cond e1 (TBase TBool); the e2/e3
         branches need ctx_types_agree composition.
       - S_Copy atomic (EPair v v from ECopy v): need extra
         is_linear_ty premise discharge.
       - S_Fst, S_Snd atomic: pattern var bind to outer goal's T
         doesn't propagate through nested match cleanly.
       - S_Region_Exit, S_Region_Step: as documented. *)
  (* ===== Per-goal proofs for the 12 remaining cases =====
     Goal order at this point (after the cascading [try solve] blocks):
       1.  S_StringConcat_Step2 (v1 value, e2 → e2')
       2.  S_Let_Step
       3.  S_LetLin_Step
       4.  S_App_Step2 (v1 value, e2 → e2')
       5.  S_If_Step
       6.  S_Pair_Step1
       7.  S_Pair_Step2 (v1 value)
       8.  S_Snd atomic (ESnd (EPair v1 v2) → v2)
       9.  S_Case_Step
       10. S_Region_Exit (ERegion r v → v, value)
       11. S_Region_Step (ERegion r e → ERegion r e')
       12. S_Copy atomic (ECopy v → EPair v v) *)

  (* Goal 1: S_StringConcat_Step2. Outer T = TString r is structurally
     constrained by T_StringConcat. IH on e2 → e2' gives TString r =
     TString r', so r = r'. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hv : is_value ?v1,
        Hv1 : has_type _ _ ?v1 _ ?G',
        Hv1' : has_type _ _ ?v1 _ ?G'0 |- _ ] =>
        assert (G' = G0) by
          (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
        assert (G'0 = G0) by
          (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
        subst G' G'0
    end.
    match goal with
    | [ H2 : has_type _ _ ?e2 (TString _) _,
        H2' : has_type _ _ ?e2' (TString _) _ |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2 _ _ H2') as Hteq;
        inversion Hteq; reflexivity
    end.
  }

  (* Goal 2: S_Let_Step. Outer T = body's type. Dispatch on
     step_R_change_shape (3-way: R = R', or R' = r :: R, or
     R' = remove_first r R). LEFT closes via type_determinacy on body.
     MIDDLE: lift H6 via region_add_typing. RIGHT: lift H8 via
     region_add_typing + region_env_perm_typing (using
     remove_first_then_cons_membership_eq), then type_determinacy. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    (* H3: e1 typed at T1 under R0; H4: e1' typed at T2 under R0';
       H6: e2 typed at T0 under R0; H8: e2 typed at T' under R0'. *)
    match goal with
    | [ He1 : has_type _ _ ?e1s _ _,
        He1' : has_type _ _ ?e1s' _ _,
        Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He1 _ _ He1') as HT12
    end.
    subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT: R = R'. *)
      subst.
      match goal with
      | [ He1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
          He1' : has_type ?R ?G ?e1s' ?T1 ?Gmid' |- _ ] =>
          assert (HagrMid : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact He1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact He1' ]);
          assert (HagrExt : ctx_types_agree (ctx_extend Gmid T1) (ctx_extend Gmid' T1))
            by (apply ctx_extend_types_agree; assumption)
      end.
      match goal with
      | [ He2 : has_type ?R (ctx_extend _ _) ?e2x ?Ta _,
          He2' : has_type ?R (ctx_extend _ _) ?e2x ?Tb _,
          HagrExt : ctx_types_agree (ctx_extend _ _) (ctx_extend _ _)
          |- ?Ta = ?Tb ] =>
          eapply type_determinacy; [ exact He2 | exact He2' | exact HagrExt ]
      end.
    - (* MIDDLE: R0' = r :: R0. Lift the body's R0 typing to r :: R0
         via region_add_typing; align contexts via typing_types_agree
         composition; close via type_determinacy under shared r :: R0. *)
      subst R0'.
      (* Identify the four typings by the position-pattern of their R:
         body-pre under R0 (H6 by current naming) and body-post under
         r :: R0 (H8 by current naming). Use multimatch for backtracking. *)
      pose proof (region_add_typing _ _ _ _ _ r H6) as He2lifted.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H3
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H4 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T2) (ctx_extend G'0 T2))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact He2lifted | exact H8 | exact HagrExt ].
    - (* RIGHT: R0' = remove_first r R0 (with In r R0). Lift the body's
         shrunk-R typing back to R0 via region_add_typing + permutation
         (r :: remove_first r R0 and R0 have same membership when In r R0). *)
      subst R0'.
      pose proof (region_add_typing _ _ _ _ _ r H8) as H8lift.
      pose proof (region_env_perm_typing _ _ _ _ _ H8lift R0
                    (remove_first_then_cons_membership_eq r R0 HinR)) as H8underR0.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H3
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H4 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T2) (ctx_extend G'0 T2))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact H6 | exact H8underR0 | exact HagrExt ].
  }

  (* Goal 3: S_LetLin_Step. Identical structure to Goal 2 (T_LetLin
     differs from T_Let only in an extra is_linear_ty premise, which
     doesn't affect type-equality reasoning). *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ He1 : has_type _ _ ?e1s _ _,
        He1' : has_type _ _ ?e1s' _ _,
        Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He1 _ _ He1') as HT12
    end.
    subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ He1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
          He1' : has_type ?R ?G ?e1s' ?T1 ?Gmid' |- _ ] =>
          assert (HagrMid : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact He1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact He1' ]);
          assert (HagrExt : ctx_types_agree (ctx_extend Gmid T1) (ctx_extend Gmid' T1))
            by (apply ctx_extend_types_agree; assumption)
      end.
      match goal with
      | [ He2 : has_type ?R (ctx_extend _ _) ?e2x ?Ta _,
          He2' : has_type ?R (ctx_extend _ _) ?e2x ?Tb _,
          HagrExt : ctx_types_agree (ctx_extend _ _) (ctx_extend _ _)
          |- ?Ta = ?Tb ] =>
          eapply type_determinacy; [ exact He2 | exact He2' | exact HagrExt ]
      end.
    - (* MIDDLE: R0' = r :: R0; lift body via region_add_typing. *)
      subst R0'.
      pose proof (region_add_typing _ _ _ _ _ r H7) as Hlift.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H4
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H6 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T2) (ctx_extend G'0 T2))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact Hlift | exact H10 | exact HagrExt ].
    - (* RIGHT: R0' = remove_first r R0 (with In r R0). Bridge via
         region_add_typing + region_env_perm_typing. *)
      subst R0'.
      pose proof (region_add_typing _ _ _ _ _ r H10) as H10lift.
      pose proof (region_env_perm_typing _ _ _ _ _ H10lift R0
                    (remove_first_then_cons_membership_eq r R0 HinR)) as H10underR0.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H4
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H6 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T2) (ctx_extend G'0 T2))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact H7 | exact H10underR0 | exact HagrExt ].
  }

  (* Goal 4: S_App_Step2 — EApp v1 e2 → EApp v1 e2'. Outer T = T2.
     Dispatch on R via step_R_change_shape. LEFT: v1's two TFun
     typings align via type_determinacy. MIDDLE: lift the R0 typing
     to r :: R0 via region_add_typing, then align. RIGHT: Phase 3. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
          Hv1' : has_type ?R ?G ?v1 (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          assert (HTfun : TFun T1a T2a = TFun T1b T2b)
            by (eapply type_determinacy;
                [exact Hv1 | exact Hv1' | apply ctx_types_agree_refl]);
          inversion HTfun; subst; reflexivity
      end.
    - (* MIDDLE: R0' = r :: R0. Lift v1's R0 typing to r :: R0,
         then type_determinacy on the two TFun typings. *)
      subst R0'.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type R0 ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
          Hv1' : has_type (r :: R0) ?G ?v1 (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          pose proof (region_add_typing _ _ _ _ _ r Hv1) as Hv1lifted;
          assert (HTfun : TFun T1a T2a = TFun T1b T2b)
            by (eapply type_determinacy;
                [exact Hv1lifted | exact Hv1' | apply ctx_types_agree_refl]);
          inversion HTfun; subst; reflexivity
      end.
    - (* RIGHT: R0' = remove_first r R0. Lift v1's shrunk-R typing
         back to R0 via region_add_typing + permutation. *)
      subst R0'.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type R0 ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
          Hv1' : has_type (remove_first r R0) ?G ?v1 (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          pose proof (region_add_typing _ _ _ _ _ r Hv1') as Hv1lift;
          pose proof (region_env_perm_typing _ _ _ _ _ Hv1lift R0
                        (remove_first_then_cons_membership_eq r R0 HinR))
            as Hv1underR0;
          assert (HTfun : TFun T1a T2a = TFun T1b T2b)
            by (eapply type_determinacy;
                [exact Hv1 | exact Hv1underR0 | apply ctx_types_agree_refl]);
          inversion HTfun; subst; reflexivity
      end.
  }

  (* Goal 5: S_If_Step — EIf e1 e2 e3 → EIf e1' e2 e3. Dispatch on R:
     LEFT: type_determinacy on branch e2 under shared R after
     ctx_types_agree on post-cond contexts. MIDDLE: region_add_typing
     on H_e2 (branch under R0) lifts to r :: R0. RIGHT: Phase 3. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ H1 : has_type ?R ?G ?e1s (TBase TBool) ?Gmid,
          H1' : has_type ?R ?G ?e1s' (TBase TBool) ?Gmid' |- _ ] =>
          assert (Hagr : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact H1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact H1' ])
      end.
      match goal with
      | [ H2 : has_type ?R ?Gmid ?e2x ?Ta _,
          H2' : has_type ?R ?Gmid' ?e2x ?Tb _,
          Hagr : ctx_types_agree ?Gmid ?Gmid' |- ?Ta = ?Tb ] =>
          eapply type_determinacy; [ exact H2 | exact H2' | exact Hagr ]
      end.
    - (* MIDDLE: R0' = r :: R0. Lift a branch typing from R0 to r :: R0. *)
      subst R0'.
      match goal with
      | [ H1 : has_type R0 ?G ?e1s (TBase TBool) ?Gmid,
          H1' : has_type (r :: R0) ?G ?e1s' (TBase TBool) ?Gmid' |- _ ] =>
          assert (HagrMid : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact H1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact H1' ])
      end.
      match goal with
      | [ H2 : has_type R0 ?Gmid ?e2x _ _ |- _ ] =>
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift
      end.
      match goal with
      | [ Hlift : has_type (r :: R0) ?Gmid ?e2x ?Ta _,
          H2'   : has_type (r :: R0) ?Gmid' ?e2x ?Tb _,
          HagrMid : ctx_types_agree ?Gmid ?Gmid' |- ?Ta = ?Tb ] =>
          eapply type_determinacy; [ exact Hlift | exact H2' | exact HagrMid ]
      end.
    - (* RIGHT: R0' = remove_first r R0. Lift post-step branch e2 typing
         back to R0 via region_add_typing + permutation. *)
      subst R0'.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H4
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H5 ]).
      pose proof (region_add_typing _ _ _ _ _ r H10) as H10lift.
      pose proof (region_env_perm_typing _ _ _ _ _ H10lift R0
                    (remove_first_then_cons_membership_eq r R0 HinR))
        as H10underR0.
      eapply type_determinacy; [ exact H7 | exact H10underR0 | exact HagrMid ].
  }

  (* Goal 6: S_Pair_Step1 — EPair e1 e2 → EPair e1' e2. Outer T =
     TProd T1 T2. IH on e1 gives T1=T1'. T2 from e2 typings. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ He1 : has_type _ _ ?e1s _ _,
        He1' : has_type _ _ ?e1s' _ _,
        Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He1 _ _ He1') as HT12
    end.
    subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ He1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
          He1' : has_type ?R ?G ?e1s' ?T1 ?Gmid' |- _ ] =>
          assert (Hagr : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact He1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact He1' ])
      end.
      match goal with
      | [ H2 : has_type ?R ?Gmid ?e2x ?T2a _,
          H2' : has_type ?R ?Gmid' ?e2x ?T2b _,
          Hagr : ctx_types_agree ?Gmid ?Gmid' |- _ ] =>
          assert (HT2 : T2a = T2b)
            by (eapply type_determinacy; [ exact H2 | exact H2' | exact Hagr ]);
          subst T2b; reflexivity
      end.
    - (* MIDDLE: R0' = r :: R0; lift e2 typing from R0 to r :: R0. *)
      subst R0'.
      match goal with
      | [ He1 : has_type R0 ?G ?e1s ?T1 ?Gmid,
          He1' : has_type (r :: R0) ?G ?e1s' ?T1 ?Gmid' |- _ ] =>
          assert (Hagr : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact He1
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact He1' ])
      end.
      match goal with
      | [ H2 : has_type R0 ?Gmid ?e2x _ _ |- _ ] =>
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift
      end.
      match goal with
      | [ Hlift : has_type (r :: R0) ?Gmid ?e2x ?T2a _,
          H2'   : has_type (r :: R0) ?Gmid' ?e2x ?T2b _,
          Hagr  : ctx_types_agree ?Gmid ?Gmid' |- _ ] =>
          assert (HT2 : T2a = T2b)
            by (eapply type_determinacy; [ exact Hlift | exact H2' | exact Hagr ]);
          subst T2b; reflexivity
      end.
    - (* RIGHT: R0' = remove_first r R0. Lift post-step e2 typing back
         to R0 via region_add_typing + permutation. Use direct names
         (H3/H4 = e1/e1', H6/H8 = e2 pre/post). *)
      subst R0'.
      assert (Hagr : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H3
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H4 ]).
      pose proof (region_add_typing _ _ _ _ _ r H8) as H8lift.
      pose proof (region_env_perm_typing _ _ _ _ _ H8lift R0
                    (remove_first_then_cons_membership_eq r R0 HinR))
        as H8underR0.
      assert (HT2 : T2 = T3)
        by (eapply type_determinacy; [ exact H6 | exact H8underR0 | exact Hagr ]).
      subst T3; reflexivity.
  }

  (* Goal 7: S_Pair_Step2 — EPair v1 e2 → EPair v1 e2'. v1 value;
     T1 (first component) aligns via type_determinacy on v1; T2 via
     IH on (e2, e2'). *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type ?R ?G ?v1 ?T1a ?Gmid,
          Hv1' : has_type ?R ?G ?v1 ?T1b ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          assert (HT1 : T1a = T1b)
            by (eapply type_determinacy;
                [exact Hv1 | exact Hv1' | apply ctx_types_agree_refl]);
          subst T1b
      end.
      match goal with
      | [ He2 : has_type ?R ?G ?e2s _ _,
          He2' : has_type ?R ?G ?e2s' _ _,
          Hs : (_, _, ?e2s) -->> (_, _, ?e2s') |- _ ] =>
          pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He2 _ _ He2') as HT2;
          subst; reflexivity
      end.
    - (* MIDDLE: R0' = r :: R0. v1's T1 aligned via region_add_typing
         on v1's R0 typing; e2-side via IH (universal in R). *)
      subst R0'.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type R0 ?G ?v1 ?T1a ?Gmid,
          Hv1' : has_type (r :: R0) ?G ?v1 ?T1b ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          pose proof (region_add_typing _ _ _ _ _ r Hv1) as Hv1lift;
          assert (HT1 : T1a = T1b)
            by (eapply type_determinacy;
                [exact Hv1lift | exact Hv1' | apply ctx_types_agree_refl]);
          subst T1b
      end.
      match goal with
      | [ He2 : has_type R0 ?G ?e2s _ _,
          He2' : has_type (r :: R0) ?G ?e2s' _ _,
          Hs : (_, R0, ?e2s) -->> (_, r :: R0, ?e2s') |- _ ] =>
          pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He2 _ _ He2') as HT2;
          subst; reflexivity
      end.
    - (* RIGHT: R0' = remove_first r R0. v1 aligned via lift+perm
         from post-step typing back to R0; e2-side closes via IH. *)
      subst R0'.
      match goal with
      | [ Hv : is_value ?v1,
          Hv1 : has_type R0 ?G ?v1 ?T1a ?Gmid,
          Hv1' : has_type (remove_first r R0) ?G ?v1 ?T1b ?Gmid' |- _ ] =>
          assert (Gmid = G) by
            (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
          assert (Gmid' = G) by
            (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
          subst Gmid Gmid';
          pose proof (region_add_typing _ _ _ _ _ r Hv1') as Hv1lift;
          pose proof (region_env_perm_typing _ _ _ _ _ Hv1lift R0
                        (remove_first_then_cons_membership_eq r R0 HinR))
            as Hv1underR0;
          assert (HT1 : T1a = T1b)
            by (eapply type_determinacy;
                [exact Hv1 | exact Hv1underR0 | apply ctx_types_agree_refl]);
          subst T1b
      end.
      match goal with
      | [ He2 : has_type R0 ?G ?e2s _ _,
          He2' : has_type (remove_first r R0) ?G ?e2s' _ _,
          Hs : (_, R0, ?e2s) -->> (_, remove_first r R0, ?e2s') |- _ ] =>
          pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ He2 _ _ He2') as HT2;
          subst; reflexivity
      end.
  }

  (* Goal 8: S_Snd atomic — ESnd (EPair v1 v2) → v2. No R change.
     T_Snd inversion → T_Pair (on EPair v1 v2) → gives v2's typing
     with type matching outer T. type_determinacy on v2 closes. *)
  1: {
    inversion Hte; subst.
    match goal with
    | [ Hp : has_type _ _ (EPair ?v1 ?v2) (TProd _ _) _ |- _ ] =>
        inversion Hp; subst
    end.
    match goal with
    | [ Hv1 : is_value ?v1,
        Hv1t : has_type ?R ?G ?v1 ?T1 ?Gmid,
        Hv2t : has_type ?R ?Gmid ?v2 ?T2 _,
        Hte' : has_type ?R ?G ?v2 ?T' _
        |- ?T2 = ?T' ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1t | exact Hv1]);
        subst Gmid;
        eapply type_determinacy;
          [ exact Hv2t | exact Hte' | apply ctx_types_agree_refl ]
    end.
  }

  (* Goal 9: S_Case_Step — ECase e e1 e2 → ECase e' e1 e2. Outer T =
     branches' type. IH on scrutinee gives TSum alignment. Dispatch
     on R for branch typings via step_R_change_shape; LEFT closes via
     type_determinacy on branch, MIDDLE via region_add_typing on
     branch + type_determinacy. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        Hsc : has_type _ _ ?es (TSum _ _) _,
        Hsc' : has_type _ _ ?es' (TSum _ _) _ |- _ ] =>
        pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hsc _ _ Hsc') as Hsum;
        inversion Hsum; subst
    end.
    pose proof (step_R_change_shape _ _ _ _ _ _ Hstep) as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]].
    - (* LEFT *)
      subst.
      match goal with
      | [ Hsc : has_type ?R ?G ?es (TSum ?T1 _) ?Gmid,
          Hsc' : has_type ?R ?G ?es' (TSum ?T1 _) ?Gmid' |- _ ] =>
          assert (HagrMid : ctx_types_agree Gmid Gmid')
            by (eapply ctx_types_agree_trans;
                [ eapply typing_types_agree; exact Hsc
                | apply ctx_types_agree_sym; eapply typing_types_agree; exact Hsc' ]);
          assert (HagrExt : ctx_types_agree (ctx_extend Gmid T1) (ctx_extend Gmid' T1))
            by (apply ctx_extend_types_agree; assumption)
      end.
      match goal with
      | [ Hb1 : has_type ?R (ctx_extend ?Gmid ?T1) ?eb1 ?Ta _,
          Hb1' : has_type ?R (ctx_extend ?Gmid' ?T1) ?eb1 ?Tb _,
          Hag : ctx_types_agree (ctx_extend ?Gmid ?T1) (ctx_extend ?Gmid' ?T1)
          |- ?Ta = ?Tb ] =>
          eapply type_determinacy; [ exact Hb1 | exact Hb1' | exact Hag ]
      end.
    - (* MIDDLE: R0' = r :: R0. Use H4/H5 (scrutinee typings) to align
         branch contexts, lift H7 (first branch under R0) to r :: R0,
         then type_determinacy with H10 under shared r :: R0. *)
      subst R0'.
      pose proof (region_add_typing _ _ _ _ _ r H7) as Hb1lift.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H4
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H5 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T3) (ctx_extend G'0 T3))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact Hb1lift | exact H10 | exact HagrExt ].
    - (* RIGHT: R0' = remove_first r R0. Lift post-step branch e1 typing
         back to R0 via region_add_typing + permutation. *)
      subst R0'.
      pose proof (region_add_typing _ _ _ _ _ r H10) as H10lift.
      pose proof (region_env_perm_typing _ _ _ _ _ H10lift R0
                    (remove_first_then_cons_membership_eq r R0 HinR))
        as H10underR0.
      assert (HagrMid : ctx_types_agree G' G'0)
        by (eapply ctx_types_agree_trans;
            [ eapply typing_types_agree; exact H4
            | apply ctx_types_agree_sym; eapply typing_types_agree; exact H5 ]).
      assert (HagrExt : ctx_types_agree (ctx_extend G' T3) (ctx_extend G'0 T3))
        by (apply ctx_extend_types_agree; assumption).
      eapply type_determinacy; [ exact H7 | exact H10underR0 | exact HagrExt ].
  }

  (* Goal 10: S_Region_Exit — ERegion r v → v. R0 → remove_first r R0.
     Hte: T_Region (~ In r R0) contradicts H0 : In r R0; or
     T_Region_Active (In r R0): inner v typed under R0 at T0.
     Hte': v typed under remove_first r R0 at T'. Bridge via
     region_shrink_preserves_typing (requires expr_free_of_region r v
     which is the S_Region_Exit premise H1). *)
  1: {
    inversion Hte; subst.
    - (* T_Region: ~ In r R0 contradicts S_Region_Exit's In r R0 (H0). *)
      exfalso; auto.
    - (* T_Region_Active *)
      match goal with
      | [ Hfree : expr_free_of_region ?r _,
          Hvt : has_type ?R ?G ?v ?T0 ?Ga,
          Hte' : has_type (remove_first ?r ?R) ?G ?v ?T' ?Gb |- ?T0 = ?T' ] =>
          pose proof (region_shrink_preserves_typing _ _ _ _ _ _ Hvt Hfree) as Hshrink;
          eapply type_determinacy;
            [ exact Hshrink | exact Hte' | apply ctx_types_agree_refl ]
      end.
  }

  (* Goal 11: S_Region_Step — ERegion r e → ERegion r e' (In r R0).
     Both Hte and Hte' invert into T_Region (~In r R) or T_Region_Active
     (In r R), giving four sub-cases:
       (a) Hte=T_Region: ~In r R0 contradicts S_Region_Step's H : In r R0.
       (b) Hte=Active, Hte'=T_Region: ~In r R0' — possibly inconsistent
           with H : In r R0 depending on step's R-change. Cases:
              - R0=R0': direct contradiction.
              - R0' = r1::R0 or remove_first r1 R0 with r≠r1: contradiction
                via region_shrink_in_preserves / In propagation.
              - R0' = remove_first r R0 (r=r1, r exited from inside):
                CONSISTENT. Use membership-eq to bridge Hte's e (under R0)
                and Hte's e' (under r :: R0' = same membership as R0)
                via region_env_perm_typing, then IH.
       (c) Hte=Active, Hte'=Active: IH applies directly. *)
  1: {
    inversion Hte; subst.
    - (* (a) T_Region: ~ In r R0 contradicts H : In r R0. *)
      exfalso; auto.
    - inversion Hte'; subst.
      + (* (b) Hte'=T_Region with ~In r R0'. Use direct hypothesis names:
           H : In r R0 (S_Region_Step premise),
           H8 : R0; G0 |- e : T0 -| Ga (Hte inner),
           H3 : ~ In r R0' (Hte' T_Region's ~In),
           H11 : r :: R0'; G0 |- e' : T' -| Gb (Hte' inner). *)
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r1 [Hadd Hnotin]] | [r1 [Hrem HinR1]]]].
        * (* R0 = R0' *) subst R0'. exfalso. apply H3. exact H.
        * (* R0' = r1 :: R0 *) subst R0'. exfalso. apply H3. right. exact H.
        * (* R0' = remove_first r1 R0 *)
          subst R0'.
          destruct (String.eqb r r1) eqn:Heqrr1.
          -- (* r = r1: r exited from inside. The expr_free approach
                was BLOCKED (PRESERVATION-HANDOFF.md § "Genuinely-
                closing options"): sibling references to r survive
                across the exit, so expr_free_of_region r e' is FALSE
                in general (counterexample: ELet (ERegion r v) (ELoc l r)).
                Path 3 plug-in (2026-05-26): use region_env_perm_typing
                to transport H11 from r :: remove_first r R0 to R0
                (same membership when In r R0), then apply the at-pre
                helper [step_preserves_type_at_pre] for type-equality
                across the inner step. *)
             apply String.eqb_eq in Heqrr1. subst r1.
             pose proof (region_env_perm_typing _ _ _ _ _ H11 R0
                           (remove_first_then_cons_membership_eq r R0 H))
               as H11_R0.
             eapply step_preserves_type_at_pre;
               [ exact Hstep | exact H8 | exact H11_R0 ].
          -- (* r ≠ r1: In r R0 → In r R0' contradicts ~In r R0'. *)
             apply String.eqb_neq in Heqrr1. exfalso. apply H3.
             apply (region_shrink_in_preserves r1 r R0 (fun H' => Heqrr1 (eq_sym H'))).
             exact H.
      + (* (c) Both T_Region_Active. IH on the inner step. *)
        match goal with
        | [ Hvt : has_type ?R0 ?G ?e _ _,
            Hvt' : has_type ?R0' ?G ?e' _ _,
            Hs : (_, ?R0, ?e) -->> (_, ?R0', ?e') |- _ ] =>
            pose proof (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hvt _ _ Hvt') as Hteq;
            exact Hteq
        end.
  }

  (* Goal 12: S_Copy atomic — ECopy v → EPair v v. No R change.
     T_Copy outer = TProd T T (v : T). T_Pair outer = TProd T1' T2'.
     type_determinacy on v aligns T1' = T2' = T. *)
  1: {
    inversion Hte; subst.
    inversion Hte'; subst.
    match goal with
    | [ Hv : is_value ?v,
        Hvt : has_type ?R ?G ?v ?T _,
        Hv1t : has_type ?R ?G ?v ?T1' ?Gmid,
        Hv2t : has_type ?R ?Gmid ?v ?T2' _
        |- TProd ?T ?T = TProd ?T1' ?T2' ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1t | exact Hv]);
        subst Gmid;
        assert (HT1 : T = T1')
          by (eapply type_determinacy;
              [exact Hvt | exact Hv1t | apply ctx_types_agree_refl]);
        assert (HT2 : T = T2')
          by (eapply type_determinacy;
              [exact Hvt | exact Hv2t | apply ctx_types_agree_refl]);
        subst T1' T2'; reflexivity
    end.
  }
Qed.

(** ** Lemma B — Linearity-context invariance for siblings under step.

    For `preservation`'s congruence cases (`S_StringConcat_Step1`,
    `S_Let_Step`, `S_App_Step1`, ...), the IH yields the stepped
    subexpression's typing at the post-step region but with an output
    linearity context [G_out] that's a fresh metavariable. The
    sibling-typing premise still references the PRE-step output
    context [G_end]. To reconstruct the compound typing, the two
    must coincide.

    [step_output_context_eq] establishes that: any two typings of
    [e] and [e'] starting from the same input context [G] end at the
    same context, when [e] steps to [e']. This is the linearity-
    tracking analogue of the existing [type_determinacy] (which
    handles the type).

    Phase 1 of the closure plan in ROADMAP §"Preservation closure plan". *)

(** ** Step output context equality at pre-step env (Path 3 helper, 2026-05-26)

    Companion to [step_output_context_eq], mirroring the relationship
    between [step_preserves_type_at_pre] and [step_preserves_type].
    Both typings are at the SAME pre-step env R (not R/R').

    Plugs into [step_output_context_eq]'s line 6016 admit (S_Region_Step
    case (b) sub-case r=r1) after the region_env_perm_typing transport.
    Pending: per-case work (~6-10h), all cases admitted as scaffold. *)
Lemma step_output_context_eq_at_pre :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G_a G_b,
      R; G |- e  : T -| G_a ->
      R; G |- e' : T -| G_b ->
      G_a = G_b.
Proof.
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    intros G0 T0 Ga Gb Htype_e Htype_e'.
  (* Scaffolded 2026-05-26. Per-case closures pending. *)
  (* Atomic + Cluster A/B/C tactic blocks copied verbatim from
     step_output_context_eq's body — patterns use ?R/?R' polymorphically
     so they match at-pre framing (both at R). Closes ~24 of 35 cases. *)
  all: try (
    inversion Htype_e; subst;
    inversion Htype_e'; subst;
    repeat match goal with
    | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EI32 _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ EUnit _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EBool _) _ _ |- _ ] =>
        inversion H; subst; clear H
    end;
    reflexivity).
  (* 31 cases remain. Per-case map: PRESERVATION-HANDOFF.md
     section "Lemma B per-case status". Three clusters:
       - beta-reduction (~7): S_Let_Val, S_LetLin_Val, S_App_Fun,
         S_If_True/False, S_Case_Inl/Inr. Need a strengthened
         subst-output-context lemma (subst_typing_gen already has
         the [remove_at k Gout] shape; subst_preserves_typing hides
         it behind an existential).
       - congruence (~18, every S_*_Step except S_Borrow_Step):
         apply [step_R_eq_or_touches_region] to dispatch [R = R'];
         in the R-eq branch, apply IH for the inner step + recursive
         Lemma B for siblings. RIGHT branch (touches_region) is
         blocked on the same region-env weakening lemma as
         preservation Phase 3.
       - region / compound-value (~6): S_Region_Enter/Exit/Step,
         S_StringLen (atomic, blocked on TBorrow/EStringLen
         inversion shape — does NOT close trivially despite being
         atomic), S_Copy, S_Fst, S_Snd. S_Region_Step blocks on
         Phase 3. *)
  (* === Cluster A — beta-reduction cases (S_Let_Val, S_LetLin_Val,
     S_App_Fun, S_Case_Inl, S_Case_Inr): combine
     [subst_preserves_typing_strong] (which gives one typing of the
     substituted form at the original output context) with
     [output_ctx_det] applied against [Htype_e'] (the post-step
     typing at [Gb]) to conclude [Ga = Gb]. *)
  (* S_Let_Val: e = ELet v1 e2 -> subst 0 v1 e2 *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELet ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply output_ctx_det; [exact Hsub | exact Hte']
        end
    end
  ].
  (* S_LetLin_Val: same shape as S_Let_Val with an extra is_linear
     premise. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELetLin ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply output_ctx_det; [exact Hsub | exact Hte']
        end
    end
  ].
  (* S_App_Fun: e = EApp (ELam T ebody) v2 -> subst 0 v2 ebody. The
     lambda is a value (post-context = pre-context); v2 is a value
     (post-context = pre-context). *)

  all: try solve [
    match goal with
    | [ Hv : is_value ?v2,
        Hte : has_type ?R ?G (EApp (ELam ?T1 ?ebody) ?v2) ?T2 ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v2 ?ebody) ?T2 ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hlam : has_type ?Rx ?Gx (ELam ?Tann ?ebody2)
                                    (TFun ?Tfa ?Tfr) ?Gmidx,
            Harg : has_type ?Rx ?Gmidx ?v2 ?Tfa ?Ga2 |- _ ] =>
            (* Lambda is a value -> Gmidx = Gx. *)
            assert (HGlam : Gmidx = Gx) by
              (eapply value_context_unchanged;
               [exact Hlam | constructor]);
            subst Gmidx;
            (* Arg is a value -> Ga2 = Gx. *)
            assert (HGv : Ga2 = Gx) by
              (eapply value_context_unchanged; eassumption);
            subst Ga2;
            (* Invert lambda to expose body typing + force Tann = Tfa. *)
            inversion Hlam; subst;
            match goal with
            | [ Hbody : has_type ?Rx (ctx_extend ?Gx ?Tfa) ?ebody2 ?Tfr
                                  ((?Tfa, true) :: ?Gx) |- _ ] =>
                destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                            Hbody Harg Hv) as [_ Hsub];
                eapply output_ctx_det; [exact Hsub | exact Hte']
            end
        end
    end
  ].
  (* S_If_True: e = EIf (EBool true) e2 e3 -> e2. After T_If inversion,
     the bool typing is a value so its post-context equals its pre-context;
     the true-branch typing is then at the input context and matches Hte'
     for output_ctx_det. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool true) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e2x ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool true) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e2x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply output_ctx_det; [exact Hbranch | exact Hte']
        end
    end
  ].
  (* S_If_False: symmetric for the false branch e3. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool false) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e3x ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool false) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e3x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply output_ctx_det; [exact Hbranch | exact Hte']
        end
    end
  ].
  (* S_Case_Inl: e = ECase (EInl Tann v) e1 e2 -> subst 0 v e1.
     Three-step inversion chain (T_Case, value_context_unchanged on
     EInl, T_Inl). After this, the v-typing's output equals the
     input context G, ready for the closing pattern. *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInl _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInl _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T1 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T1) ?ebody ?T
                                              ((?T1, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply output_ctx_det; [exact Hsub | exact Hte']
    end
  ].
  (* S_Case_Inr: symmetric — same recipe with EInr / VInr. *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInr _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInr _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T2 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T2) ?ebody ?T
                                              ((?T2, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply output_ctx_det; [exact Hsub | exact Hte']
    end
  ].
  (* === Cluster C — atomic compound-value rules ===
     S_Fst, S_Snd: extract first/second of a pair value.
     Recipe: invert T_Fst/T_Snd to get the pair typing, invert
     T_Pair to get both component typings, apply
     value_context_unchanged twice to align all contexts, then
     value_context_unchanged on Hte' to align Gb. *)
  (* S_Fst: e = EFst (EPair v1 v2) -> v1. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type ?R ?G (EFst (EPair ?v1 ?v2)) ?T ?Ga,
        Hte' : has_type ?R ?G ?v1 ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hpair : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T ?T2) ?Gpost
            |- _ ] =>
            assert (HGp : Gpost = G) by
              (eapply value_context_unchanged;
               [exact Hpair | apply VPair; assumption]);
            subst Gpost;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* S_Snd: e = ESnd (EPair v1 v2) -> v2. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type ?R ?G (ESnd (EPair ?v1 ?v2)) ?T ?Ga,
        Hte' : has_type ?R ?G ?v2 ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hpair : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T) ?Gpost
            |- _ ] =>
            assert (HGp : Gpost = G) by
              (eapply value_context_unchanged;
               [exact Hpair | apply VPair; assumption]);
            subst Gpost;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* S_Copy: e = ECopy v -> EPair v v. T_Copy on Hte gives v's
     typing; T_Pair inversion on Hte' gives two v-typings. All have
     identical inputs (G) so value_context_unchanged aligns
     everything to G. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type ?R ?G (ECopy ?v) ?T ?Ga,
        Hte' : has_type ?R ?G (EPair ?v ?v) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?Tv ?Ga |- _ ] =>
            assert (HGa : Ga = G) by
              (eapply value_context_unchanged; eassumption);
            subst Ga
        end;
        inversion Hte'; subst;
        match goal with
        | [ Hv1t : has_type ?R ?G ?v ?Tv ?Gmid,
            Hv2t : has_type ?R ?Gmid ?v ?Tv ?Gb' |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGb' : Gb' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb';
            reflexivity
        end
    end
  ].
  (* S_StringLen: EStringLen (EBorrow (ELoc l r)) -> EI32 n.
     Original was missed by the atomic-axiom tactic because the
     EBorrow (ELoc _ _) inversion needs two passes (T_StringLen
     wraps T_Borrow_Val wraps T_Loc). Explicit chain here. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EStringLen (EBorrow (ELoc ?l ?r))) ?T ?Ga,
        Hte' : has_type ?R ?G (EI32 _) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbor : has_type ?R ?G (EBorrow (ELoc ?l ?r))
                                  (TBorrow (TString _)) ?Ga |- _ ] =>
            inversion Hbor; subst;
            inversion Hte'; subst;
            try reflexivity;
            match goal with
            | [ Hloc : has_type ?R ?G (ELoc ?l ?r) _ ?Gloc |- _ ] =>
                inversion Hloc; subst; reflexivity
            end
        end
    end
  ].
  (* === Cluster B — congruence cases (S_*_Step) ===
     Recipe for the canonical two-child congruence (e.g.,
     S_StringConcat_Step1):
       1. Invert both Hte and Hte' (the outer compound typings).
       2. Apply step_R_eq_or_touches_region to dispatch [R = R'].
       3. In LEFT branch (R = R'): apply IH on the inner step's two
          typings to get [Gmid = Gmid']; then output_ctx_det on the
          unchanged sibling [e2]'s two typings closes.
       4. RIGHT branch (touches_region) is blocked on Phase 3 region-
          env weakening — admitted per-case here, lifted out by the
          final [all: admit] below.
     The shared [T] in Lemma B's signature forces type-equality
     between the two T_StringConcat inversions (both give
     [T = TString r] for the SAME [r]), sidestepping the circularity
     concern flagged in ROADMAP. *)
  (* S_StringConcat_Step1: unified via output_ctx_det_across_step.
     Outer T = TString r is structurally constrained (T_StringConcat
     forces both inversions to give the same TString r). IH on the
     stepping inner aligns Gmid; the unchanged sibling e2's output
     context equality follows from output_ctx_det_across_step. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EStringConcat ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EStringConcat ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TString ?r) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H1' : has_type ?R' ?G ?e1' (TString ?r) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 (TString ?r) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_Let_Step: previously blocked by circular T1-alignment in the
     inner match (T_Let's binding type T1 isn't pinned by outer T).
     Resolution via step_preserves_type: align T1a = T1b first, then
     IH on (e1, e1') gives Gmid = Gmid', then output_ctx_det_across_step
     on (e2, e2) closes — handling all three R-shapes uniformly. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ELet ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (ELet ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        (* Align T1a = T1b via step_preserves_type on inner step. *)
        match goal with
        | [ H1 : has_type ?R0 ?G0 ?e1s ?T1a ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' ?T1b ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HT12;
            subst T1b
        end;
        (* Now T1 unified. Apply IH on (e1, e1') for Gmid alignment,
           then output_ctx_det_across_step on the unchanged body e2. *)
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 _,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e2 ?T0 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hin _ _ _ _ _ H2 H2')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* S_LetLin_Step: same as S_Let_Step. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ELetLin ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (ELetLin ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R0 ?G0 ?e1s ?T1a ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' ?T1b ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HT12;
            subst T1b
        end;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 _,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e2 ?T0 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hin _ _ _ _ _ H2 H2')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* S_App_Step1: e1 steps, e2 unchanged. T_App's TFun T1 T2 has
     outer T = T2 fixed, but T1 (function domain) is unpinned by
     outer T, so the two inversions can have different T1a / T1b.
     Use step_preserves_type on inner (e1, e1') to align T1, then
     IH on (e1, e1') + output_ctx_det_across_step on unchanged e2. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EApp ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?e1s  (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' (TFun ?T1b ?T2') ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ H1  : has_type ?R  ?G ?e1s  (TFun ?T1 ?T2) ?Gmid,
            H2  : has_type ?R  ?Gmid ?e2 ?T1 _,
            H1' : has_type ?R' ?G ?e1s' (TFun ?T1 ?T2) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T1 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_Pair_Step1: e1 steps. Pair has type TProd T1 T2. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EPair ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EPair ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T2 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_StringConcat_Step2: inner step on e2, v1 value. Lemma B's IH
     on (e2, e2') applies directly with the universal R/R' — no
     R-dispatch needed. value_context_unchanged on v1 aligns Gmid = G
     in both derivations, then IH closes. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EStringConcat ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EStringConcat ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 (TString ?r) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H1' : has_type ?R' ?G ?v1 (TString ?r) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' (TString ?r) ?Gb |- _ ] =>
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Pair_Step2: inner step on e2, v1 is value. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EPair ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EPair ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 ?T1 ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T2 ?Ga,
            H1' : has_type ?R' ?G ?v1 ?T1 ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' ?T2 ?Gb |- _ ] =>
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Inl_Step: single-child congruence; outer TSum T1 T2 pins inner T1. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EInl ?Tann ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (EInl ?Tann ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T1 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T1 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Inr_Step: symmetric. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EInr ?Tann ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (EInr ?Tann ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T2 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Copy_Step: single-child congruence; outer TProd T T pins inner T. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ECopy ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (ECopy ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?Tx ?Ga,
            H1' : has_type ?R' ?G ?e' ?Tx ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_App_Step1: inner step on e1. T_App's T1 (arg type) is NOT
     fixed by outer T — so direct IH application would need
     T1_a = T1_b across the two inversions. Resolution: apply
     type_determinacy on the sibling e2 (same expression!) with
     ctx_types_agree on its input contexts (which agree by
     typing_types_agree + sym + trans through G). *)
  (* Second S_App_Step1 attempt — duplicate of earlier block; unified
     via step_preserves_type for T1 alignment. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EApp ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?e1s  (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' (TFun ?T1b ?T2') ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ H1  : has_type ?R  ?G ?e1s  (TFun ?T1 ?T2) ?Gmid,
            H2  : has_type ?R  ?Gmid ?e2 ?T1 _,
            H1' : has_type ?R' ?G ?e1s' (TFun ?T1 ?T2) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T1 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_App_Step2: v1 value, e2 steps. Outer T = T2 (function range).
     v1's TFun typings align via type_determinacy (same R needed —
     but with v1 a value, region invariance via region_env_perm_typing
     would bridge; here we use Lemma B's IH on stepping e2 directly,
     since it's universal in R/R'). *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EApp ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        (* Use step_preserves_type to align v1's TFun types across
           Hte/Hte''s different R-derivations. *)
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?v1 (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?v1 (TFun ?T1b ?T2') ?Gmid' |- _ ] =>
            (* v1 is a value so it doesn't step; but step_preserves_type
               applies to the (e2, e2') pair, not v1. Instead use
               value_context_unchanged for context, then IH on e2. *)
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid'
        end;
        (* For the stepping e2: step_preserves_type aligns its type. *)
        match goal with
        | [ H2  : has_type ?R0  ?G  ?e2s  ?T1a _,
            H2' : has_type ?R0' ?G  ?e2s' ?T1b _,
            Hs : (_, _, ?e2s) -->> (_, _, ?e2s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H2 _ _ H2') as HT12;
            subst T1b
        end;
        match goal with
        | [ H2  : has_type ?R  ?G ?e2s  ?T1 ?Ga,
            H2' : has_type ?R' ?G ?e2s' ?T1 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_If_Step: cond steps, branches unchanged. Outer T pinned. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EIf ?e1 ?e2 ?e3) ?T ?Ga,
        Hte' : has_type ?R' ?G (EIf ?e1' ?e2 ?e3) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s (TBase TBool) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T ?Ga,
            H1' : has_type ?R' ?G ?e1s' (TBase TBool) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_StringLen_Step: T_StringLen wraps EBorrow e. Inversion of
     EBorrow's typing forces e to be EVar or a value — neither
     steps. Vacuous closure (like S_Borrow_Step). *)
  all: try solve [
    match goal with
    | [ Hin : step _ _,
        Hte : has_type _ _ (EStringLen _) _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbor : has_type _ _ (EBorrow _) _ _ |- _ ] =>
            inversion Hbor; subst;
            [ inversion Hin
            | exfalso;
              match goal with
              | [ Hv : is_value ?v |- _ ] =>
                  eapply values_dont_step; [exact Hv | exact Hin]
              end
            ]
        end
    end
  ].
  (* S_StringLen (atomic): EStringLen (ELoc l r) -> EI32 n. The step
     rule's input is EStringLen on a raw ELoc (NOT EBorrow-wrapped);
     T_StringLen's typing wraps it as EBorrow (ELoc l r) at type
     TBorrow (TString r). Inversion chain: T_StringLen ->
     T_Borrow_Val (since ELoc is a value, T_Borrow's EVar form is
     impossible) -> T_Loc. Each preserves the context unchanged,
     so Ga = G. Hte' (T_I32) gives Gb = G. Reflexivity. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EStringLen (ELoc _ _)) ?T ?Ga,
        Hte' : has_type ?R ?G (EI32 _) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hb : has_type _ _ (EBorrow (ELoc _ _)) _ _ |- _ ] =>
            inversion Hb; subst;
            try (match goal with
                 | [ Hev : has_type _ _ (EVar _) _ _ |- _ ] =>
                     inversion Hev
                 end);
            inversion Hte'; subst;
            repeat match goal with
            | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
                inversion H; subst; clear H
            end;
            reflexivity
        end
    end
  ].
  (* S_Region_Enter: 4 inversion sub-goals; handle each contradiction
     branch explicitly + use output_ctx_det on the valid sub-goal. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T ?Ga,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first
          [ (* C, D: Hte was T_Region_Active forcing In r R0, but
               step rule premise Hn : ~ In r R0. tauto closes. *)
            exfalso; tauto
          | (* A: Hte' was T_Region forcing ~ In r (r :: R0); trivially false. *)
            exfalso;
            match goal with
            | [ H : ~ In ?r (?r :: _) |- _ ] =>
                apply H; left; reflexivity
            end
          | (* B (valid): output_ctx_det on the two inner typings of e. *)
            match goal with
            | [ H1 : has_type ?R ?G ?e ?T ?Gax,
                H2 : has_type ?R ?G ?e ?T ?Gbx |- ?Gax = ?Gbx ] =>
                eapply output_ctx_det; [exact H1 | exact H2]
            end ]
    end
  ].
  (* S_Region_Enter: ERegion r e (under R, ~In r R) -> ERegion r e
     (under r :: R). Inversion of Hte branches into T_Region (valid,
     since ~In r R0 from step premise) and T_Region_Active (forces
     In r R0, contradicts step premise). Inversion of Hte' branches
     into T_Region (forces ~In r (r :: R0), trivially false) and
     T_Region_Active (valid, since In r (r :: R0) trivially holds).
     4 sub-goals total; close 3 contradictions with exfalso+tauto,
     close the valid one with output_ctx_det on the two inner
     typings of e. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T ?Ga,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first [ exfalso; tauto
              | (* The valid sub-goal: both inner typings of e at
                   (r :: R0); G with outputs Ga and Gb. *)
                match goal with
                | [ H1 : has_type ?R ?G ?e ?T ?Gax,
                    H2 : has_type ?R ?G ?e ?T ?Gbx |- ?Gax = ?Gbx ] =>
                    eapply output_ctx_det; [exact H1 | exact H2]
                end ]
    end
  ].
  (* Both S_StringLen (atomic) and S_Region_Enter are now closed
     (above) — Cluster C COMPLETE. *)
  (* S_Region_Exit: ERegion r v -> v (R becomes remove_first r R).
     T_Region_Active inversion + value_context_unchanged twice. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type ?R ?G (ERegion ?r ?v) ?T ?Ga,
        Hte' : has_type _ ?G ?v ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?T ?Ga |- _ ] =>
            assert (HGa : Ga = G) by
              (eapply value_context_unchanged; eassumption);
            subst Ga;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* 7 cases remain (80% closed from 35). All blocked on
     **type-alignment circularity WITHOUT independent-context
     sibling** + Phase 3 region-env weakening.
       - 6 type-alignment-circular WITHOUT independent-context sibling:
         S_Let_Step, S_LetLin_Step, S_Case_Step (sibling exists but
         its context depends on the unconstrained type), S_Drop_Step,
         S_Fst_Step, S_Snd_Step (no unchanged sibling at all). Each
         genuinely needs preservation: the outer type doesn't fix
         all inner types, and no auxiliary lemma within Lemma B's
         induction can align them.
       - 1 Phase 3 blocker (S_Region_Step): needs region-env
         weakening for non-values.
       - Implicit: all RIGHT branches (touches_region) of the closed
         Cluster B cases are admitted locally inside each tactic;
         they share preservation's Phase 3 bottleneck.

     S_App_Step1 and S_App_Step2 — once thought circular — closed
     via the "sibling type_determinacy" trick: the unchanged sibling
     [e2] (or [v1]) provides another typing of the SAME expression at
     R, G with input contexts that ctx_types_agree (composed through
     G via typing_types_agree + sym + trans). type_determinacy then
     aligns the unconstrained T1 across Hte and Hte's inversions. *)

  (* S_Fst_Step: EFst e → EFst e'. T_Fst's TProd T1 T2 has T2
     unpinned. step_preserves_type aligns TProd T1 T2 across the two
     inversions; IH then gives Ga = Gb directly (single-child). *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (EFst ?e) _ _,
        Htype_e' : has_type _ _ (EFst ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  (TProd ?T1a ?T2a) _,
            H1' : has_type _  _ ?e' (TProd ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?TP ?Ga,
            H1' : has_type _ _ ?e' ?TP ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Snd_Step: ESnd e → ESnd e'. Same as Fst with T1 unpinned. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (ESnd ?e) _ _,
        Htype_e' : has_type _ _ (ESnd ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  (TProd ?T1a ?T2a) _,
            H1' : has_type _  _ ?e' (TProd ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?TP ?Ga,
            H1' : has_type _ _ ?e' ?TP ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Drop_Step: EDrop e → EDrop e'. T_Drop's inner type T is unpinned
     (outer T = TBase TUnit). step_preserves_type aligns, then IH closes. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (EDrop ?e) _ _,
        Htype_e' : has_type _ _ (EDrop ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  ?Ta _,
            H1' : has_type _  _ ?e' ?Tb _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            subst Tb
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?Tx ?Ga,
            H1' : has_type _ _ ?e' ?Tx ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Case_Step: ECase e e1 e2 → ECase e' e1 e2. Scrutinee at
     TSum T1 T2 with T1, T2 unpinned by outer T. step_preserves_type
     aligns TSum T1 T2 across inversions; IH on scrutinee gives
     Gmid = Gmid'; output_ctx_det_across_step on branch e1 closes. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (ECase ?e ?e1 ?e2) _ _,
        Htype_e' : has_type _ _ (ECase ?e' ?e1 ?e2) _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ Hs  : has_type _ _ ?e  (TSum ?T1a ?T2a) _,
            Hs' : has_type _ _ ?e' (TSum ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ Hs _ _ Hs') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            Hs  : has_type ?R  ?G ?e  (TSum ?T1 ?T2) ?Gmid,
            Hs' : has_type ?R' ?G ?e' (TSum ?T1 ?T2) ?Gmid',
            Hb1 : has_type ?R (ctx_extend ?Gmid ?T1) ?e1 ?T _,
            Hb1' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e1 ?T _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ Hs Hs') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hstep _ _ _ _ _ Hb1 Hb1')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* Remaining cases (S_Region_Step + a few harder per-goal) admitted. *)
  (* S_Region_Step at-pre: ERegion r e -> ERegion r e' with In r R0.
     Both Htype_e and Htype_e' are at the SAME R0. T_Region requires
     ~In r R0, which contradicts the step's In r R0 premise; so BOTH
     inversions force T_Region_Active. Bodies typed under R0 at shared
     T; IHHstep applies directly. *)
  all: try solve [
    match goal with
    | [ Htype_e  : has_type ?R0 ?G0 (ERegion ?r ?e_body)  _ _,
        Htype_e' : has_type ?R0 ?G0 (ERegion ?r ?e_body') _ _,
        Hin : In ?r ?R0 |- _ ] =>
        inversion Htype_e;  subst; [exfalso; auto |];
        inversion Htype_e'; subst; [exfalso; auto |];
        match goal with
        | [ Hvt  : has_type ?R0 ?G0 ?e_body  ?T0 ?Ga0,
            Hvt' : has_type ?R0 ?G0 ?e_body' ?T0 ?Gb0
            |- ?Ga0 = ?Gb0 ] =>
            eapply IHHstep;
              [ reflexivity | reflexivity | exact Hvt | exact Hvt' ]
        end
    end
  ].
  (* 11 cases remaining are all congruence rules (S_*_Step). Each closes
     by: (1) invert both typings; (2) align inner free types via
     [step_preserves_type_at_pre] (now Qed); (3) IHHstep on inner step
     gives inner output contexts equal; (4) [output_ctx_det] or
     [value_context_unchanged] on siblings. Order from [Show Existentials]
     empirically:
       1.  S_StringConcat_Step1  (EStringConcat e1 e2, e1 → e1')
       2.  S_Let_Step            (ELet e1 e2,         e1 → e1')
       3.  S_LetLin_Step         (ELetLin e1 e2,      e1 → e1')
       4.  S_App_Step1           (EApp e1 e2,         e1 → e1')
       5.  S_App_Step2           (EApp v1 e2,         e2 → e2', v1 value)
       6.  S_If_Step             (EIf e1 e2 e3,       e1 → e1')
       7.  S_Pair_Step1          (EPair e1 e2,        e1 → e1')
       8.  S_Fst_Step            (EFst e,             e  → e')
       9.  S_Snd_Step            (ESnd e,             e  → e')
       10. S_Case_Step           (ECase e e1 e2,      e  → e')
       11. S_Drop_Step           (EDrop e,            e  → e') *)

  (* Goal 1: S_StringConcat_Step1. Outer T = TString r pins inner type;
     IHHstep on the stepping child gives Gmid = Gmid'; output_ctx_det on
     the unchanged sibling e2 gives Ga = Gb. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TString ?r) ?Gmid,
        H1' : has_type ?R ?G ?es' (TString ?r) ?Gmid' |- _ ] =>
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep; [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
        H2' : has_type ?R ?Gmid ?e2 (TString ?r) ?Gb |- ?Ga = ?Gb ] =>
        eapply output_ctx_det; [exact H2 | exact H2']
    end.
  }

  (* Goal 2: S_Let_Step. Inner type T1 is free; align via
     step_preserves_type_at_pre, then IHHstep aligns G' (post-e1).
     Body e2 unchanged, output_ctx_det yields cons-eq, injection. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  ?T1  ?Gmid,
        H1' : has_type ?R ?G ?es' ?T1' ?Gmid' |- _ ] =>
        assert (HT1 : T1 = T1') by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        subst T1';
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R (ctx_extend ?Gm ?T1) ?e2 ?T0 ?Gext,
        H2' : has_type ?R (ctx_extend ?Gm ?T1) ?e2 ?T0 ?Gext'
        |- _ ] =>
        assert (Hexteq : Gext = Gext') by
          (eapply output_ctx_det; [exact H2 | exact H2']);
        injection Hexteq; intros HGab; exact HGab
    end.
  }

  (* Goal 3: S_LetLin_Step. Same shape as S_Let_Step. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  ?T1  ?Gmid,
        H1' : has_type ?R ?G ?es' ?T1' ?Gmid' |- _ ] =>
        assert (HT1 : T1 = T1') by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        subst T1';
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R (ctx_extend ?Gm ?T1) ?e2 ?T0 ?Gext,
        H2' : has_type ?R (ctx_extend ?Gm ?T1) ?e2 ?T0 ?Gext'
        |- _ ] =>
        assert (Hexteq : Gext = Gext') by
          (eapply output_ctx_det; [exact H2 | exact H2']);
        injection Hexteq; intros HGab; exact HGab
    end.
  }

  (* Goal 4: S_App_Step1. Outer T = T2 (function return); T1 (arg type)
     free. Align via step_preserves_type_at_pre on (e1, e1')'s TFun
     typings; inversion gives T1 = T1'; IHHstep aligns Gmid;
     output_ctx_det on sibling e2 closes. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TFun ?T1a ?T2a) ?Gmid,
        H1' : has_type ?R ?G ?es' (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
        assert (HT : TFun T1a T2a = TFun T1b T2b) by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        inversion HT; subst;
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R ?Gm ?e2 ?T1 ?Ga,
        H2' : has_type ?R ?Gm ?e2 ?T1 ?Gb |- ?Ga = ?Gb ] =>
        eapply output_ctx_det; [exact H2 | exact H2']
    end.
  }

  (* Goal 5: S_App_Step2. v1 is value; e2 → e2'. Both v1 typings at
     R, G, v1; value_context_unchanged aligns Gmid = G = Gmid';
     type_determinacy aligns TFun T1a = TFun T1b → T1 unique;
     IHHstep on (e2, e2') gives Ga = Gb. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hv : is_value ?v1,
        Hv1 : has_type ?R ?G ?v1 (TFun ?T1a ?T2a) ?Gmid,
        Hv1' : has_type ?R ?G ?v1 (TFun ?T1b ?T2b) ?Gmid' |- _ ] =>
        assert (Gmid = G) by
          (eapply value_context_unchanged; [exact Hv1 | exact Hv]);
        assert (Gmid' = G) by
          (eapply value_context_unchanged; [exact Hv1' | exact Hv]);
        subst Gmid Gmid';
        assert (HTfun : TFun T1a T2a = TFun T1b T2b)
          by (eapply type_determinacy;
              [exact Hv1 | exact Hv1' | apply ctx_types_agree_refl]);
        inversion HTfun; subst
    end.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H2  : has_type ?R ?G ?es  ?T1 ?Ga,
        H2' : has_type ?R ?G ?es' ?T1 ?Gb |- ?Ga = ?Gb ] =>
        eapply IHHstep;
          [reflexivity | reflexivity | exact H2 | exact H2']
    end.
  }

  (* Goal 6: S_If_Step. Inner type fixed at TBase TBool; IHHstep aligns
     Gmid; both branches at same (Gmid, T0); output_ctx_det on either
     branch closes. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TBase TBool) ?Gmid,
        H1' : has_type ?R ?G ?es' (TBase TBool) ?Gmid' |- _ ] =>
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R ?Gm ?e2 ?T0 ?Ga,
        H2' : has_type ?R ?Gm ?e2 ?T0 ?Gb |- ?Ga = ?Gb ] =>
        eapply output_ctx_det; [exact H2 | exact H2']
    end.
  }

  (* Goal 7: S_Pair_Step1. Outer T = TProd T1 T2 pins both inner types.
     IHHstep on (e1, e1') gives Gmid = Gmid'; output_ctx_det on e2 closes. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  ?T1 ?Gmid,
        H1' : has_type ?R ?G ?es' ?T1 ?Gmid' |- _ ] =>
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R ?Gm ?e2 ?T2 ?Ga,
        H2' : has_type ?R ?Gm ?e2 ?T2 ?Gb |- ?Ga = ?Gb ] =>
        eapply output_ctx_det; [exact H2 | exact H2']
    end.
  }

  (* Goal 8: S_Fst_Step. e → e'. Outer T = T1 (first component); T2 free.
     Align inner TProd via step_preserves_type_at_pre; inversion gives
     T2 = T2'; IHHstep gives Ga = Gb. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TProd ?T1a ?T2a) ?Ga,
        H1' : has_type ?R ?G ?es' (TProd ?T1b ?T2b) ?Gb |- _ ] =>
        assert (HT : TProd T1a T2a = TProd T1b T2b) by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        inversion HT; subst;
        eapply IHHstep;
          [reflexivity | reflexivity | exact H1 | exact H1']
    end.
  }

  (* Goal 9: S_Snd_Step. Symmetric to Fst. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TProd ?T1a ?T2a) ?Ga,
        H1' : has_type ?R ?G ?es' (TProd ?T1b ?T2b) ?Gb |- _ ] =>
        assert (HT : TProd T1a T2a = TProd T1b T2b) by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        inversion HT; subst;
        eapply IHHstep;
          [reflexivity | reflexivity | exact H1 | exact H1']
    end.
  }

  (* Goal 10: S_Case_Step. Scrutinee TSum T1 T2 free; align via
     step_preserves_type_at_pre; IHHstep aligns Gmid; both branches
     unchanged at (ctx_extend Gmid T1, T0) → output_ctx_det on cons-eq. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  (TSum ?T1a ?T2a) ?Gmid,
        H1' : has_type ?R ?G ?es' (TSum ?T1b ?T2b) ?Gmid' |- _ ] =>
        assert (HT : TSum T1a T2a = TSum T1b T2b) by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        inversion HT; subst;
        assert (HGmid : Gmid = Gmid')
          by (eapply IHHstep;
              [reflexivity | reflexivity | exact H1 | exact H1']);
        subst Gmid'
    end.
    match goal with
    | [ H2  : has_type ?R (ctx_extend ?Gm ?T1) ?eb ?T0 ?Gext,
        H2' : has_type ?R (ctx_extend ?Gm ?T1) ?eb ?T0 ?Gext'
        |- _ ] =>
        assert (Hexteq : Gext = Gext') by
          (eapply output_ctx_det; [exact H2 | exact H2']);
        injection Hexteq; intros HGab; exact HGab
    end.
  }

  (* Goal 11: S_Drop_Step. Outer T = TBase TUnit; inner T_inner free.
     Align via step_preserves_type_at_pre; IHHstep gives Ga = Gb. *)
  1: {
    inversion Htype_e; subst.
    inversion Htype_e'; subst.
    match goal with
    | [ Hs : (_, _, ?es) -->> (_, _, ?es'),
        H1  : has_type ?R ?G ?es  ?Ti  ?Ga,
        H1' : has_type ?R ?G ?es' ?Ti' ?Gb |- _ ] =>
        assert (HT : Ti = Ti') by
          (eapply step_preserves_type_at_pre;
           [exact Hs | exact H1 | exact H1']);
        subst Ti';
        eapply IHHstep;
          [reflexivity | reflexivity | exact H1 | exact H1']
    end.
  }
Qed.

Lemma step_output_context_eq :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G_a G_b,
      R;  G |- e  : T -| G_a ->
      R'; G |- e' : T -| G_b ->
      G_a = G_b.
Proof.
  (* Phase 1 scaffold (PR #121) + cfg-remember pattern + atomic-axiom
     closure. cfg-remember mirrors [step_R_eq_or_touches_region] and
     [preservation] (PRs #102 / #106): substitutes the outer
     expression slots into each induction case so per-case inversion
     sees concrete syntax. *)
  intros mu R e mu' R' e' Hstep.
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep;
    intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
    intros G0 T0 Ga Gb Htype_e Htype_e'.
  (* Atomic-axiom + accidental-congruence cases that close by full
     inversion of both typings + leaf-value re-inversion +
     reflexivity. Empirically (coqc 8.18.0) closes 4 of 35 step
     rules:
       S_StringNew    ([EStringNew r s]   -> [ELoc l r])
       S_StringConcat ([EStringConcat (ELoc _ _) (ELoc _ _)]
                                           -> [ELoc l' r])
       S_Drop         ([EDrop (ELoc _ _)] -> [EUnit])
       S_Borrow_Step  ([EBorrow e]        -> [EBorrow e'])
         (closes accidentally: both T_Borrow and T_Borrow_Val output
         the input context unchanged, so Ga = G = Gb regardless of
         the inner step's IH.)
     The leaf re-inversion forces inner [has_type _ _ (ELoc _ _) _ _]
     and friends to pin their output to the input (T_Loc /
     T_StringNew / T_I32 / T_Unit all preserve the linearity
     context). *)
  all: try (
    inversion Htype_e; subst;
    inversion Htype_e'; subst;
    repeat match goal with
    | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EI32 _) _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ EUnit _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : has_type _ _ (EBool _) _ _ |- _ ] =>
        inversion H; subst; clear H
    end;
    reflexivity).
  (* 31 cases remain. Per-case map: PRESERVATION-HANDOFF.md
     section "Lemma B per-case status". Three clusters:
       - beta-reduction (~7): S_Let_Val, S_LetLin_Val, S_App_Fun,
         S_If_True/False, S_Case_Inl/Inr. Need a strengthened
         subst-output-context lemma (subst_typing_gen already has
         the [remove_at k Gout] shape; subst_preserves_typing hides
         it behind an existential).
       - congruence (~18, every S_*_Step except S_Borrow_Step):
         apply [step_R_eq_or_touches_region] to dispatch [R = R'];
         in the R-eq branch, apply IH for the inner step + recursive
         Lemma B for siblings. RIGHT branch (touches_region) is
         blocked on the same region-env weakening lemma as
         preservation Phase 3.
       - region / compound-value (~6): S_Region_Enter/Exit/Step,
         S_StringLen (atomic, blocked on TBorrow/EStringLen
         inversion shape — does NOT close trivially despite being
         atomic), S_Copy, S_Fst, S_Snd. S_Region_Step blocks on
         Phase 3. *)
  (* === Cluster A — beta-reduction cases (S_Let_Val, S_LetLin_Val,
     S_App_Fun, S_Case_Inl, S_Case_Inr): combine
     [subst_preserves_typing_strong] (which gives one typing of the
     substituted form at the original output context) with
     [output_ctx_det] applied against [Htype_e'] (the post-step
     typing at [Gb]) to conclude [Ga = Gb]. *)
  (* S_Let_Val: e = ELet v1 e2 -> subst 0 v1 e2 *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELet ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply output_ctx_det; [exact Hsub | exact Hte']
        end
    end
  ].
  (* S_LetLin_Val: same shape as S_Let_Val with an extra is_linear
     premise. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hte : has_type ?R ?G (ELetLin ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v1 ?e2) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hv1 : has_type ?R ?G ?v1 ?T1 ?G',
            He2 : has_type ?R (ctx_extend ?G' ?T1) ?e2 ?T
                                              ((?T1, true) :: ?Ga') |- _ ] =>
            assert (HGv : G' = G) by
              (eapply value_context_unchanged; eassumption);
            subst G';
            destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                        He2 Hv1 Hv) as [_ Hsub];
            eapply output_ctx_det; [exact Hsub | exact Hte']
        end
    end
  ].
  (* S_App_Fun: e = EApp (ELam T ebody) v2 -> subst 0 v2 ebody. The
     lambda is a value (post-context = pre-context); v2 is a value
     (post-context = pre-context). *)

  all: try solve [
    match goal with
    | [ Hv : is_value ?v2,
        Hte : has_type ?R ?G (EApp (ELam ?T1 ?ebody) ?v2) ?T2 ?Ga,
        Hte' : has_type ?R ?G (subst 0 ?v2 ?ebody) ?T2 ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hlam : has_type ?Rx ?Gx (ELam ?Tann ?ebody2)
                                    (TFun ?Tfa ?Tfr) ?Gmidx,
            Harg : has_type ?Rx ?Gmidx ?v2 ?Tfa ?Ga2 |- _ ] =>
            (* Lambda is a value -> Gmidx = Gx. *)
            assert (HGlam : Gmidx = Gx) by
              (eapply value_context_unchanged;
               [exact Hlam | constructor]);
            subst Gmidx;
            (* Arg is a value -> Ga2 = Gx. *)
            assert (HGv : Ga2 = Gx) by
              (eapply value_context_unchanged; eassumption);
            subst Ga2;
            (* Invert lambda to expose body typing + force Tann = Tfa. *)
            inversion Hlam; subst;
            match goal with
            | [ Hbody : has_type ?Rx (ctx_extend ?Gx ?Tfa) ?ebody2 ?Tfr
                                  ((?Tfa, true) :: ?Gx) |- _ ] =>
                destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                            Hbody Harg Hv) as [_ Hsub];
                eapply output_ctx_det; [exact Hsub | exact Hte']
            end
        end
    end
  ].
  (* S_If_True: e = EIf (EBool true) e2 e3 -> e2. After T_If inversion,
     the bool typing is a value so its post-context equals its pre-context;
     the true-branch typing is then at the input context and matches Hte'
     for output_ctx_det. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool true) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e2x ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool true) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e2x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply output_ctx_det; [exact Hbranch | exact Hte']
        end
    end
  ].
  (* S_If_False: symmetric for the false branch e3. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EIf (EBool false) ?e2x ?e3x) ?T ?Ga,
        Hte' : has_type ?R ?G ?e3x ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbool : has_type ?R ?G (EBool false) (TBase TBool) ?Gmid,
            Hbranch : has_type ?R ?Gmid ?e3x ?T ?Ga |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hbool | constructor]);
            subst Gmid;
            eapply output_ctx_det; [exact Hbranch | exact Hte']
        end
    end
  ].
  (* S_Case_Inl: e = ECase (EInl Tann v) e1 e2 -> subst 0 v e1.
     Three-step inversion chain (T_Case, value_context_unchanged on
     EInl, T_Inl). After this, the v-typing's output equals the
     input context G, ready for the closing pattern. *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInl _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInl _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T1 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T1) ?ebody ?T
                                              ((?T1, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply output_ctx_det; [exact Hsub | exact Hte']
    end
  ].
  (* S_Case_Inr: symmetric — same recipe with EInr / VInr. *)
  all: try (match goal with
    | [ Hte : has_type _ _ (ECase (EInr _ ?vv) _ _) _ _,
        Hv : is_value ?vv |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hsum : has_type _ ?G (EInr _ ?vv) (TSum _ _) ?Gmid |- _ ] =>
            assert (HGsum : Gmid = G) by
              (eapply value_context_unchanged;
               [exact Hsum | constructor; assumption]);
            subst Gmid;
            inversion Hsum; subst
        end
    end).
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hvt : has_type ?R ?G ?vv ?T2 ?G,
        Hbr : has_type ?R (ctx_extend ?G ?T2) ?ebody ?T
                                              ((?T2, true) :: ?Ga),
        Hte' : has_type ?R ?G (subst 0 ?vv ?ebody) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        destruct (subst_preserves_typing_strong _ _ _ _ _ _ _ _
                    Hbr Hvt Hv) as [_ Hsub];
        eapply output_ctx_det; [exact Hsub | exact Hte']
    end
  ].
  (* === Cluster C — atomic compound-value rules ===
     S_Fst, S_Snd: extract first/second of a pair value.
     Recipe: invert T_Fst/T_Snd to get the pair typing, invert
     T_Pair to get both component typings, apply
     value_context_unchanged twice to align all contexts, then
     value_context_unchanged on Hte' to align Gb. *)
  (* S_Fst: e = EFst (EPair v1 v2) -> v1. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type ?R ?G (EFst (EPair ?v1 ?v2)) ?T ?Ga,
        Hte' : has_type ?R ?G ?v1 ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hpair : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T ?T2) ?Gpost
            |- _ ] =>
            assert (HGp : Gpost = G) by
              (eapply value_context_unchanged;
               [exact Hpair | apply VPair; assumption]);
            subst Gpost;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* S_Snd: e = ESnd (EPair v1 v2) -> v2. *)
  all: try solve [
    match goal with
    | [ Hv1 : is_value ?v1, Hv2 : is_value ?v2,
        Hte : has_type ?R ?G (ESnd (EPair ?v1 ?v2)) ?T ?Ga,
        Hte' : has_type ?R ?G ?v2 ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hpair : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T) ?Gpost
            |- _ ] =>
            assert (HGp : Gpost = G) by
              (eapply value_context_unchanged;
               [exact Hpair | apply VPair; assumption]);
            subst Gpost;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* S_Copy: e = ECopy v -> EPair v v. T_Copy on Hte gives v's
     typing; T_Pair inversion on Hte' gives two v-typings. All have
     identical inputs (G) so value_context_unchanged aligns
     everything to G. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type ?R ?G (ECopy ?v) ?T ?Ga,
        Hte' : has_type ?R ?G (EPair ?v ?v) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?Tv ?Ga |- _ ] =>
            assert (HGa : Ga = G) by
              (eapply value_context_unchanged; eassumption);
            subst Ga
        end;
        inversion Hte'; subst;
        match goal with
        | [ Hv1t : has_type ?R ?G ?v ?Tv ?Gmid,
            Hv2t : has_type ?R ?Gmid ?v ?Tv ?Gb' |- _ ] =>
            assert (HGmid : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGb' : Gb' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb';
            reflexivity
        end
    end
  ].
  (* S_StringLen: EStringLen (EBorrow (ELoc l r)) -> EI32 n.
     Original was missed by the atomic-axiom tactic because the
     EBorrow (ELoc _ _) inversion needs two passes (T_StringLen
     wraps T_Borrow_Val wraps T_Loc). Explicit chain here. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EStringLen (EBorrow (ELoc ?l ?r))) ?T ?Ga,
        Hte' : has_type ?R ?G (EI32 _) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbor : has_type ?R ?G (EBorrow (ELoc ?l ?r))
                                  (TBorrow (TString _)) ?Ga |- _ ] =>
            inversion Hbor; subst;
            inversion Hte'; subst;
            try reflexivity;
            match goal with
            | [ Hloc : has_type ?R ?G (ELoc ?l ?r) _ ?Gloc |- _ ] =>
                inversion Hloc; subst; reflexivity
            end
        end
    end
  ].
  (* === Cluster B — congruence cases (S_*_Step) ===
     Recipe for the canonical two-child congruence (e.g.,
     S_StringConcat_Step1):
       1. Invert both Hte and Hte' (the outer compound typings).
       2. Apply step_R_eq_or_touches_region to dispatch [R = R'].
       3. In LEFT branch (R = R'): apply IH on the inner step's two
          typings to get [Gmid = Gmid']; then output_ctx_det on the
          unchanged sibling [e2]'s two typings closes.
       4. RIGHT branch (touches_region) is blocked on Phase 3 region-
          env weakening — admitted per-case here, lifted out by the
          final [all: admit] below.
     The shared [T] in Lemma B's signature forces type-equality
     between the two T_StringConcat inversions (both give
     [T = TString r] for the SAME [r]), sidestepping the circularity
     concern flagged in ROADMAP. *)
  (* S_StringConcat_Step1: unified via output_ctx_det_across_step.
     Outer T = TString r is structurally constrained (T_StringConcat
     forces both inversions to give the same TString r). IH on the
     stepping inner aligns Gmid; the unchanged sibling e2's output
     context equality follows from output_ctx_det_across_step. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EStringConcat ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EStringConcat ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1 (TString ?r) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H1' : has_type ?R' ?G ?e1' (TString ?r) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 (TString ?r) ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_Let_Step: previously blocked by circular T1-alignment in the
     inner match (T_Let's binding type T1 isn't pinned by outer T).
     Resolution via step_preserves_type: align T1a = T1b first, then
     IH on (e1, e1') gives Gmid = Gmid', then output_ctx_det_across_step
     on (e2, e2) closes — handling all three R-shapes uniformly. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ELet ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (ELet ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        (* Align T1a = T1b via step_preserves_type on inner step. *)
        match goal with
        | [ H1 : has_type ?R0 ?G0 ?e1s ?T1a ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' ?T1b ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HT12;
            subst T1b
        end;
        (* Now T1 unified. Apply IH on (e1, e1') for Gmid alignment,
           then output_ctx_det_across_step on the unchanged body e2. *)
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 _,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e2 ?T0 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hin _ _ _ _ _ H2 H2')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* S_LetLin_Step: same as S_Let_Step. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ELetLin ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (ELetLin ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R0 ?G0 ?e1s ?T1a ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' ?T1b ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HT12;
            subst T1b
        end;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 _,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e2 ?T0 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hin _ _ _ _ _ H2 H2')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* S_App_Step1: e1 steps, e2 unchanged. T_App's TFun T1 T2 has
     outer T = T2 fixed, but T1 (function domain) is unpinned by
     outer T, so the two inversions can have different T1a / T1b.
     Use step_preserves_type on inner (e1, e1') to align T1, then
     IH on (e1, e1') + output_ctx_det_across_step on unchanged e2. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EApp ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?e1s  (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' (TFun ?T1b ?T2') ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ H1  : has_type ?R  ?G ?e1s  (TFun ?T1 ?T2) ?Gmid,
            H2  : has_type ?R  ?Gmid ?e2 ?T1 _,
            H1' : has_type ?R' ?G ?e1s' (TFun ?T1 ?T2) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T1 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_Pair_Step1: e1 steps. Pair has type TProd T1 T2. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EPair ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EPair ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s ?T1 ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e1s' ?T1 ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T2 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_StringConcat_Step2: inner step on e2, v1 value. Lemma B's IH
     on (e2, e2') applies directly with the universal R/R' — no
     R-dispatch needed. value_context_unchanged on v1 aligns Gmid = G
     in both derivations, then IH closes. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EStringConcat ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EStringConcat ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 (TString ?r) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 (TString ?r) ?Ga,
            H1' : has_type ?R' ?G ?v1 (TString ?r) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' (TString ?r) ?Gb |- _ ] =>
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Pair_Step2: inner step on e2, v1 is value. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EPair ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EPair ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?v1 ?T1 ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T2 ?Ga,
            H1' : has_type ?R' ?G ?v1 ?T1 ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2' ?T2 ?Gb |- _ ] =>
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid';
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Inl_Step: single-child congruence; outer TSum T1 T2 pins inner T1. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EInl ?Tann ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (EInl ?Tann ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T1 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T1 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Inr_Step: symmetric. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EInr ?Tann ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (EInr ?Tann ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?T2 ?Ga,
            H1' : has_type ?R' ?G ?e' ?T2 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Copy_Step: single-child congruence; outer TProd T T pins inner T. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (ECopy ?e) ?T ?Ga,
        Hte' : has_type ?R' ?G (ECopy ?e') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e ?Tx ?Ga,
            H1' : has_type ?R' ?G ?e' ?Tx ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_App_Step1: inner step on e1. T_App's T1 (arg type) is NOT
     fixed by outer T — so direct IH application would need
     T1_a = T1_b across the two inversions. Resolution: apply
     type_determinacy on the sibling e2 (same expression!) with
     ctx_types_agree on its input contexts (which agree by
     typing_types_agree + sym + trans through G). *)
  (* Second S_App_Step1 attempt — duplicate of earlier block; unified
     via step_preserves_type for T1 alignment. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EApp ?e1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?e1' ?e2) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?e1s  (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?e1s' (TFun ?T1b ?T2') ?Gmid',
            Hs : (_, _, ?e1s) -->> (_, _, ?e1s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ H1  : has_type ?R  ?G ?e1s  (TFun ?T1 ?T2) ?Gmid,
            H2  : has_type ?R  ?Gmid ?e2 ?T1 _,
            H1' : has_type ?R' ?G ?e1s' (TFun ?T1 ?T2) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T1 _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_App_Step2: v1 value, e2 steps. Outer T = T2 (function range).
     v1's TFun typings align via type_determinacy (same R needed —
     but with v1 a value, region invariance via region_env_perm_typing
     would bridge; here we use Lemma B's IH on stepping e2 directly,
     since it's universal in R/R'). *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hv : is_value ?v1,
        Hte : has_type ?R ?G (EApp ?v1 ?e2) ?T ?Ga,
        Hte' : has_type ?R' ?G (EApp ?v1 ?e2') ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        (* Use step_preserves_type to align v1's TFun types across
           Hte/Hte''s different R-derivations. *)
        match goal with
        | [ H1  : has_type ?R0  ?G0 ?v1 (TFun ?T1a ?T2)  ?Gmid,
            H1' : has_type ?R0' ?G0 ?v1 (TFun ?T1b ?T2') ?Gmid' |- _ ] =>
            (* v1 is a value so it doesn't step; but step_preserves_type
               applies to the (e2, e2') pair, not v1. Instead use
               value_context_unchanged for context, then IH on e2. *)
            assert (HGm : Gmid = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid;
            assert (HGm' : Gmid' = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gmid'
        end;
        (* For the stepping e2: step_preserves_type aligns its type. *)
        match goal with
        | [ H2  : has_type ?R0  ?G  ?e2s  ?T1a _,
            H2' : has_type ?R0' ?G  ?e2s' ?T1b _,
            Hs : (_, _, ?e2s) -->> (_, _, ?e2s') |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hs _ _ _ H2 _ _ H2') as HT12;
            subst T1b
        end;
        match goal with
        | [ H2  : has_type ?R  ?G ?e2s  ?T1 ?Ga,
            H2' : has_type ?R' ?G ?e2s' ?T1 ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H2 H2') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_If_Step: cond steps, branches unchanged. Outer T pinned. *)
  all: try (
    match goal with
    | [ IH : forall (_:mem) (_:region_env) (_:expr) (_:mem) (_:region_env) (_:expr),
              _ = _ -> _ = _ -> forall (_:ctx) (_:ty) (_:ctx) (_:ctx),
              _ -> _ -> _ = _,
        Hin : step _ _,
        Hte : has_type ?R ?G (EIf ?e1 ?e2 ?e3) ?T ?Ga,
        Hte' : has_type ?R' ?G (EIf ?e1' ?e2 ?e3) ?T ?Gb
        |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        match goal with
        | [ H1 : has_type ?R ?G ?e1s (TBase TBool) ?Gmid,
            H2 : has_type ?R ?Gmid ?e2 ?T ?Ga,
            H1' : has_type ?R' ?G ?e1s' (TBase TBool) ?Gmid',
            H2' : has_type ?R' ?Gmid' ?e2 ?T ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hmid;
            subst Gmid';
            eapply output_ctx_det_across_step;
              [ exact Hin | exact H2 | exact H2' ]
        end
    end).
  (* S_StringLen_Step: T_StringLen wraps EBorrow e. Inversion of
     EBorrow's typing forces e to be EVar or a value — neither
     steps. Vacuous closure (like S_Borrow_Step). *)
  all: try solve [
    match goal with
    | [ Hin : step _ _,
        Hte : has_type _ _ (EStringLen _) _ _ |- _ ] =>
        inversion Hte; subst;
        match goal with
        | [ Hbor : has_type _ _ (EBorrow _) _ _ |- _ ] =>
            inversion Hbor; subst;
            [ inversion Hin
            | exfalso;
              match goal with
              | [ Hv : is_value ?v |- _ ] =>
                  eapply values_dont_step; [exact Hv | exact Hin]
              end
            ]
        end
    end
  ].
  (* S_StringLen (atomic): EStringLen (ELoc l r) -> EI32 n. The step
     rule's input is EStringLen on a raw ELoc (NOT EBorrow-wrapped);
     T_StringLen's typing wraps it as EBorrow (ELoc l r) at type
     TBorrow (TString r). Inversion chain: T_StringLen ->
     T_Borrow_Val (since ELoc is a value, T_Borrow's EVar form is
     impossible) -> T_Loc. Each preserves the context unchanged,
     so Ga = G. Hte' (T_I32) gives Gb = G. Reflexivity. *)
  all: try solve [
    match goal with
    | [ Hte : has_type ?R ?G (EStringLen (ELoc _ _)) ?T ?Ga,
        Hte' : has_type ?R ?G (EI32 _) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hb : has_type _ _ (EBorrow (ELoc _ _)) _ _ |- _ ] =>
            inversion Hb; subst;
            try (match goal with
                 | [ Hev : has_type _ _ (EVar _) _ _ |- _ ] =>
                     inversion Hev
                 end);
            inversion Hte'; subst;
            repeat match goal with
            | [ H : has_type _ _ (ELoc _ _) _ _ |- _ ] =>
                inversion H; subst; clear H
            end;
            reflexivity
        end
    end
  ].
  (* S_Region_Enter: 4 inversion sub-goals; handle each contradiction
     branch explicitly + use output_ctx_det on the valid sub-goal. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T ?Ga,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first
          [ (* C, D: Hte was T_Region_Active forcing In r R0, but
               step rule premise Hn : ~ In r R0. tauto closes. *)
            exfalso; tauto
          | (* A: Hte' was T_Region forcing ~ In r (r :: R0); trivially false. *)
            exfalso;
            match goal with
            | [ H : ~ In ?r (?r :: _) |- _ ] =>
                apply H; left; reflexivity
            end
          | (* B (valid): output_ctx_det on the two inner typings of e. *)
            match goal with
            | [ H1 : has_type ?R ?G ?e ?T ?Gax,
                H2 : has_type ?R ?G ?e ?T ?Gbx |- ?Gax = ?Gbx ] =>
                eapply output_ctx_det; [exact H1 | exact H2]
            end ]
    end
  ].
  (* S_Region_Enter: ERegion r e (under R, ~In r R) -> ERegion r e
     (under r :: R). Inversion of Hte branches into T_Region (valid,
     since ~In r R0 from step premise) and T_Region_Active (forces
     In r R0, contradicts step premise). Inversion of Hte' branches
     into T_Region (forces ~In r (r :: R0), trivially false) and
     T_Region_Active (valid, since In r (r :: R0) trivially holds).
     4 sub-goals total; close 3 contradictions with exfalso+tauto,
     close the valid one with output_ctx_det on the two inner
     typings of e. *)
  all: try solve [
    match goal with
    | [ Hn : ~ In ?r _,
        Hte : has_type _ _ (ERegion ?r ?e) ?T ?Ga,
        Hte' : has_type _ _ (ERegion ?r ?e) ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        inversion Hte'; subst;
        first [ exfalso; tauto
              | (* The valid sub-goal: both inner typings of e at
                   (r :: R0); G with outputs Ga and Gb. *)
                match goal with
                | [ H1 : has_type ?R ?G ?e ?T ?Gax,
                    H2 : has_type ?R ?G ?e ?T ?Gbx |- ?Gax = ?Gbx ] =>
                    eapply output_ctx_det; [exact H1 | exact H2]
                end ]
    end
  ].
  (* Both S_StringLen (atomic) and S_Region_Enter are now closed
     (above) — Cluster C COMPLETE. *)
  (* S_Region_Exit: ERegion r v -> v (R becomes remove_first r R).
     T_Region_Active inversion + value_context_unchanged twice. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hte : has_type ?R ?G (ERegion ?r ?v) ?T ?Ga,
        Hte' : has_type _ ?G ?v ?T ?Gb |- ?Ga = ?Gb ] =>
        inversion Hte; subst;
        match goal with
        | [ Hvt : has_type ?R ?G ?v ?T ?Ga |- _ ] =>
            assert (HGa : Ga = G) by
              (eapply value_context_unchanged; eassumption);
            subst Ga;
            assert (HGb : Gb = G) by
              (eapply value_context_unchanged; eassumption);
            subst Gb;
            reflexivity
        end
    end
  ].
  (* 7 cases remain (80% closed from 35). All blocked on
     **type-alignment circularity WITHOUT independent-context
     sibling** + Phase 3 region-env weakening.
       - 6 type-alignment-circular WITHOUT independent-context sibling:
         S_Let_Step, S_LetLin_Step, S_Case_Step (sibling exists but
         its context depends on the unconstrained type), S_Drop_Step,
         S_Fst_Step, S_Snd_Step (no unchanged sibling at all). Each
         genuinely needs preservation: the outer type doesn't fix
         all inner types, and no auxiliary lemma within Lemma B's
         induction can align them.
       - 1 Phase 3 blocker (S_Region_Step): needs region-env
         weakening for non-values.
       - Implicit: all RIGHT branches (touches_region) of the closed
         Cluster B cases are admitted locally inside each tactic;
         they share preservation's Phase 3 bottleneck.

     S_App_Step1 and S_App_Step2 — once thought circular — closed
     via the "sibling type_determinacy" trick: the unchanged sibling
     [e2] (or [v1]) provides another typing of the SAME expression at
     R, G with input contexts that ctx_types_agree (composed through
     G via typing_types_agree + sym + trans). type_determinacy then
     aligns the unconstrained T1 across Hte and Hte's inversions. *)

  (* S_Fst_Step: EFst e → EFst e'. T_Fst's TProd T1 T2 has T2
     unpinned. step_preserves_type aligns TProd T1 T2 across the two
     inversions; IH then gives Ga = Gb directly (single-child). *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (EFst ?e) _ _,
        Htype_e' : has_type _ _ (EFst ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  (TProd ?T1a ?T2a) _,
            H1' : has_type _  _ ?e' (TProd ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?TP ?Ga,
            H1' : has_type _ _ ?e' ?TP ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Snd_Step: ESnd e → ESnd e'. Same as Fst with T1 unpinned. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (ESnd ?e) _ _,
        Htype_e' : has_type _ _ (ESnd ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  (TProd ?T1a ?T2a) _,
            H1' : has_type _  _ ?e' (TProd ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?TP ?Ga,
            H1' : has_type _ _ ?e' ?TP ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Drop_Step: EDrop e → EDrop e'. T_Drop's inner type T is unpinned
     (outer T = TBase TUnit). step_preserves_type aligns, then IH closes. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (EDrop ?e) _ _,
        Htype_e' : has_type _ _ (EDrop ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ H1  : has_type _  _ ?e  ?Ta _,
            H1' : has_type _  _ ?e' ?Tb _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ H1 _ _ H1') as HTeq;
            subst Tb
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            H1  : has_type _ _ ?e  ?Tx ?Ga,
            H1' : has_type _ _ ?e' ?Tx ?Gb |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ H1 H1') as Hgeq;
            exact Hgeq
        end
    end).
  (* S_Case_Step: ECase e e1 e2 → ECase e' e1 e2. Scrutinee at
     TSum T1 T2 with T1, T2 unpinned by outer T. step_preserves_type
     aligns TSum T1 T2 across inversions; IH on scrutinee gives
     Gmid = Gmid'; output_ctx_det_across_step on branch e1 closes. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (ECase ?e ?e1 ?e2) _ _,
        Htype_e' : has_type _ _ (ECase ?e' ?e1 ?e2) _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        inversion Htype_e'; subst;
        match goal with
        | [ Hs  : has_type _ _ ?e  (TSum ?T1a ?T2a) _,
            Hs' : has_type _ _ ?e' (TSum ?T1b ?T2b) _ |- _ ] =>
            pose proof (step_preserves_type _ _ _ _ _ _ Hstep _ _ _ Hs _ _ Hs') as HTeq;
            inversion HTeq; subst
        end;
        match goal with
        | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _ _, _ -> _ -> _ = _,
            Hs  : has_type ?R  ?G ?e  (TSum ?T1 ?T2) ?Gmid,
            Hs' : has_type ?R' ?G ?e' (TSum ?T1 ?T2) ?Gmid',
            Hb1 : has_type ?R (ctx_extend ?Gmid ?T1) ?e1 ?T _,
            Hb1' : has_type ?R' (ctx_extend ?Gmid' ?T1) ?e1 ?T _ |- _ ] =>
            pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ Hs Hs') as Hmid;
            subst Gmid';
            pose proof (output_ctx_det_across_step _ _ _ _ _ _ Hstep _ _ _ _ _ Hb1 Hb1')
              as Hcons;
            injection Hcons; intros; assumption
        end
    end).
  (* S_Region_Step: ERegion r e → ERegion r e' with In r R0. Both Hte
     and Hte' invert into T_Region (~ In r R) or T_Region_Active (In r R).
     T_Region case contradicts In r R0 from S_Region_Step's premise.
     T_Region_Active × T_Region_Active: IH on inner step gives
     Ga = Gb directly. Cross cases need careful R-shape dispatch but
     are typically vacuous or close via IH after careful alignment. *)
  all: try (
    match goal with
    | [ Htype_e : has_type _ _ (ERegion ?r ?e) _ _,
        Htype_e' : has_type _ _ (ERegion ?r ?e') _ _,
        Hstep : (_, _, ?e) -->> (_, _, ?e') |- _ ] =>
        inversion Htype_e; subst;
        [ (* Hte = T_Region: ~ In r R0 contradicts In r R0. *)
          match goal with [ H : In ?r0 ?Rx |- _ ] => exfalso; auto end
        | (* Hte = T_Region_Active *)
          inversion Htype_e'; subst;
          [ (* Hte' = T_Region: ~ In r R0' but step from R0 with In r R0.
               Possible if inner exits r. Bridge via region_env_perm + IH. *)
            match goal with
            | [ Hnin : ~ In ?r _, Hin : In ?r ?R0,
                Hvt : has_type ?R0 ?G ?e ?T _,
                Hvt' : has_type (?r :: ?R0') ?G ?e' ?T _ |- _ ] =>
                pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
                  as [HeqR | [[r1 [Hadd Hnotin]] | [r1 [Hrem HinR1]]]];
                [ subst R0'; exfalso; apply Hnin; exact Hin
                | subst R0'; exfalso; apply Hnin; right; exact Hin
                | subst R0';
                  destruct (String.eqb r r1) eqn:Heqrr1;
                  [ apply String.eqb_eq in Heqrr1; subst r1;
                    pose proof (region_env_perm_typing _ _ _ _ _ Hvt' R0
                                  (remove_first_then_cons_membership_eq r R0 Hin))
                      as Hvt'_R0;
                    eapply step_output_context_eq_at_pre;
                      [ exact Hstep | exact Hvt | exact Hvt'_R0 ]
                  | apply String.eqb_neq in Heqrr1; exfalso; apply Hnin;
                    apply (region_shrink_in_preserves r1 r R0
                            (fun H' => Heqrr1 (eq_sym H'))); exact Hin
                  ]
                ]
            end
          | (* Hte' = T_Region_Active: IH applies directly. *)
            match goal with
            | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _
                      -> forall _ _ _ _, _ -> _ -> _ = _,
                Hvt : has_type ?R0 ?G ?e ?T ?Ga,
                Hvt' : has_type ?R0' ?G ?e' ?T ?Gb |- ?Ga = ?Gb ] =>
                pose proof (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ _ Hvt Hvt') as Hgeq;
                exact Hgeq
            end
          ]
        ]
    end).
Qed.

Theorem preservation :
  forall mu R e mu' R' e',
    (mu, R, e) -->> (mu', R', e') ->
    forall G T G',
    R; G |- e : T -| G' ->
    exists G_out, R'; G |- e' : T -| G_out.
Proof.
  intros mu R e mu' R' e' Hstep.
  (* Remember the configs so `induction Hstep` generates explicit equations on
     the outer expression slots. Without these remembers, `induction Hstep`
     leaves the outer `e`/`e'` abstract — for an axiom step rule like
     S_StringNew the constructor pre-conditions land in the context but the
     equation `e = EStringNew r s` does not, so cross-cases (e.g. S_StringNew
     step + T_Unit typing) have no discriminating equation in scope and the
     `try solve [exfalso; discriminate | exfalso; congruence]` chain below
     cannot close them.
     Empirically (Coq 8.18.0, 2026-05-20): without these remembers,
     `inversion Htype; subst` produces the FULL 35 × 26 = 910 cross-case
     combinatorial and the `try solve [...]` chain closes ZERO of them.
     With these remembers + `inversion Hcfg; subst; inversion Hcfg'; subst;`,
     `inversion Htype` only generates the diagonal arm per step rule (since
     the expression slot is concrete after substitution), and the chain
     closes the trivially-dischargeable ones, leaving ~29 real proof
     obligations. Standard preservation pattern; cf. Software Foundations
     `Stlc.preservation`. The prior `remember e_typed as e_orig` was a
     misdiagnosis of the same problem — it remembered the WRONG expression
     (the typing's `e`, which was already abstract) instead of the config's
     expression slot (which is what `induction Hstep` substitutes for). *)
  remember (mu, R, e) as cfg eqn:Hcfg.
  remember (mu', R', e') as cfg' eqn:Hcfg'.
  (* Generalise mu/R/e/mu'/R'/e' and their cfg-equations so the IHs
     emitted by `induction Hstep` get clean universal quantification
     over each inner step's config — not the outer cfg pair (which
     would make the IH non-applicable, since (mu_inner, R_inner,
     e_inner) ≠ (mu, R, EOuter ...) in general). Without this revert,
     the 28 congruence cases left after the cross-case discriminate
     pass have unusable IHs. *)
  revert mu R e mu' R' e' Hcfg Hcfg'.
  induction Hstep; intros mu0 R0 e0 mu0' R0' e0' Hcfg Hcfg';
    intros G0 T0 G0' Htype;
    inversion Hcfg; subst;
    inversion Hcfg'; subst;
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
  all: try solve [eexists; eapply T_Region_Active; [left; reflexivity | assumption | eassumption]].
  (* T_Borrow cross-cases generated by inversion Htype in S_Borrow_Val / S_Borrow_Step:
     (a) S_Borrow_Val / T_Borrow: after subst v = EVar i, have is_value (EVar i) — impossible.
         Close by inversion on is_value (EVar _) which has no matching constructor.
     (b) S_Borrow_Step / T_Borrow: after subst e = EVar i, have step c1 c2 where c1 contains
         EVar i — no step constructor fires on EVar, so inversion gives 0 cases.
         Use `solve [inversion H]` which only succeeds when inversion closes the goal (0 cases). *)
  all: try solve [match goal with [H: is_value (EVar _) |- _] => inversion H end].
  all: try solve [match goal with [H: step _ _ |- _] => inversion H end].
  (* REMAINING CASE (2026-04-19, post Option-B scaffolding):

     Only ONE case remains open: S_Region_Step + T_Region_Active.

     Given: inner step (mu, R, e) -->> (mu', R', e') with `In r R`
     (from T_Region_Active) and `~ In r (free_regions T)`.
     IH: exists G_out, R'; G |- e' : T -| G_out.
     Goal: exists G_out', R'; G |- ERegion r e' : T -| G_out'.

     Case-split on `In r R'`:
     - If In r R': reapply T_Region_Active.
     - If ~ In r R': need T_Region with `(r :: R'); G |- e' : T -| G_out`,
       but IH only gives `R'; G |- e' : T -| G_out`. Requires region-env
       WEAKENING (add r to R') — a lemma in the opposite direction from
       the shrink lemma and not obviously valid without extra
       invariants on e'.

     S_Region_Exit + T_Region_Active IS NOW CLOSED (see "try solve"
     above), using:
       - expr_free_of_region r v  (new premise on S_Region_Exit, landed
         this session as Option B)
       - region_shrink_preserves_typing (proven above, 1 remaining admit
         for T_Region_Active shadowing case inside the lemma itself).

     Full closure of this preservation admit now blocks on the
     region-env weakening lemma for non-values, which is a narrower,
     better-understood piece of work than the original language-design
     question. *)
  (* S_Region_Exit + T_Region_Active closes via region_shrink_preserves_typing
     using the new step-premise expr_free_of_region. *)
  all: try solve [eexists; eapply region_shrink_preserves_typing;
                  [eassumption | assumption]].
  (* S_Region_Step + T_Region_Active: the last open goal.
     IH gives exists G_out, R'; G |- e' : T -| G_out.
     Case-split on whether r is still in R':
     - If In r R': apply T_Region_Active directly.
     - If ~ In r R': apply T_Region + region_add_typing to weaken
       the IH body typing from R' to r :: R'.
     After all `all: try solve [...]` steps above, exactly one goal
     remains: S_Region_Step + T_Region_Active.
     Use `eassumption` to feed the correct has_type hyp into the IH.
     Then case-split; construct T_Region or T_Region_Active. *)
  (* S_Region_Step + T_Region_Active: the final goal.
     IHHstep is the IH from induction on the inner step of S_Region_Step.
     It has type: forall G T G', R; G |- e : T -| G' -> exists G_out, R'; G |- e' : T -| G_out.
     Apply it to the body typing from T_Region_Active inversion. *)
  all: try (
    match goal with
    | [ |- exists _ : ctx, has_type _ _ (ERegion _ _) _ _ ] =>
        match goal with
        | [ Hbody : has_type _ _ _ _ _, Hfr : ~ In _ (free_regions _) |- _ ] =>
            destruct (IHHstep _ _ _ Hbody) as [G_out Hout];
            destruct (in_dec string_dec r R') as [Hin' | Hnotin'];
            [ eexists; eapply T_Region_Active; [exact Hin' | exact Hfr | exact Hout]
            | eexists; eapply T_Region;
              [ exact Hnotin' | exact Hfr | apply region_add_typing; exact Hout ] ]
        end
    end).
  (* === Goal-closing chain for the post-remember-cfg 29 residuals ===
     Added 2026-05-20 evening per formal/PRESERVATION-HANDOFF.md per-case
     checklist. Each `all: try solve [...]` targets one residual class. *)

  (* Axiom cases (S_StringNew / S_StringConcat): result is `ELoc l r`
     and the *goal's* type is `TString r0` (named from inversion of
     the OUTER typing). To close, invert the sibling-location's typing
     premise (`H : R; G |- ELoc _ r : TString r0 -| G'`) which is
     itself a T_Loc — that derives `r0 = r` and `region_active R r`.
     Then T_Loc applies. *)
  all: try solve [
    match goal with
    | [ H : has_type _ _ (ELoc _ _) (TString _) _
        |- exists _ : ctx, has_type _ _ (ELoc _ _) (TString _) _ ] =>
        inversion H; subst; eexists; apply T_Loc; assumption
    end
  ].

  (* S_StringNew: result is `ELoc l r` at `TString r` (no sibling
     typing in scope, but the step's `In r R` is). *)
  all: try solve [eexists; apply T_Loc; unfold region_active in *; assumption].

  (* S_StringLen: result is `EI32 (String.length s)` at `TBase TI32`. *)
  all: try solve [eexists; apply T_I32].

  (* S_Drop: result is `EUnit` at `TBase TUnit`. *)
  all: try solve [eexists; apply T_Unit].

  (* S_Copy: result is `EPair v v` at `TProd T T`. Constructor +
     assumption on the value's typing premise (carried over by the
     inversion of T_Copy). *)
  all: try solve [eexists; apply T_Pair; eassumption].

  (* β-reduction cases (S_Let_Val, S_LetLin_Val, S_App_Fun, S_Fst,
     S_Snd, S_Case_Inl/Inr): close via the existing
     subst_preserves_typing lemma. *)
  all: try solve [eexists; eapply subst_preserves_typing; eassumption].

  (* S_If_True / S_If_False: pick the appropriate branch's typing premise. *)
  all: try solve [eexists; eassumption].

  (* Congruence cases (S_*_Step variants): the IH (after the revert)
     is universally quantified over each inner step's config — we
     specialise with the constructor's inner-step args + reflexivity
     on the cfg equations. Pattern after revert mu/R/e/mu'/R'/e'/Hcfg/Hcfg':

       IH : forall mu R e mu' R' e',
              (?mu_in, ?R_in, ?e_in) = (mu, R, e) ->
              (?mu_out, ?R_out, ?e_out) = (mu', R', e') ->
              forall G T G', R; G |- e : T -| G' ->
                             exists G_out, R'; G |- e' : T -| G_out

     We use edestruct + eq_refl x 2 on the universal cfg equations,
     supply the inner-expr typing premise from inversion, then close
     by econstructor + eauto. The eauto fallback handles cases where
     the sibling premises need light glue (e.g. region invariance
     follows from the step's region-non-change). *)
  all: try solve [
    match goal with
    | [ IH : forall _ _ _ _ _ _, _ = _ -> _ = _ -> forall _ _ _, _ -> _,
        Hi : has_type _ _ ?e_inner _ _ |- _ ] =>
        let G_out_inner := fresh "G_out_inner" in
        let Hout_inner := fresh "Hout_inner" in
        edestruct (IH _ _ _ _ _ _ eq_refl eq_refl _ _ _ Hi) as [G_out_inner Hout_inner];
        eexists; econstructor; eauto
    end
  ].

  (* === Region-invariance-driven closure for congruence cases ===
     Lemma [step_R_eq_or_touches_region] (proved above) gives a clean
     case-split on the inner step: either the region environment is
     preserved (so the sibling typing premises and the constructor
     can be re-applied to the post-step expression with the same R)
     or the stepped subexpression contains a region operation (which
     needs region weakening — left open).

     For each S_*_Step constructor, we discharge the LEFT branch by:
       1. pose the disjunction, destruct,
       2. in the [HeqR] branch, [subst] R0' so the post-step region
          equals the pre-step region,
       3. specialise IHHstep with eq_refl/eq_refl on cfg-equations
          and the inner-expr's typing premise (named explicitly to
          avoid pattern-match ambiguity with sibling premises),
       4. close the goal by [eexists; econstructor; ...] with the
          stepped-expr typing + any sibling premises.
     The RIGHT branch (touches_region) is left to fall through to
     [Admitted.] — these still need a region-env weakening lemma
     for non-values, separately tracked in PRESERVATION-HANDOFF.md. *)

  (* β-reduction cases that need explicit hypothesis-named applications
     of subst_preserves_typing because the implicit eassumption
     doesn't pick the right has_type for the body (multiple
     R; _ |- _ : _ -| _ premises live in scope and the lemma's first
     arg requires the body's typing, not v's). *)

  (* S_Let_Val and S_LetLin_Val: same shape (modulo linearity
     premise — both succeed without it). H_v: typing of v1 in (G0 → G').
     value_context_unchanged on H_v ⇒ G' = G0, so the body typing
     becomes (T1, false) :: G0 |- e2 : ... and subst_preserves_typing
     applies. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hev : ?R; ?G |- ?v : ?T1 -| ?Gmid,
        Hbody : ?R; ctx_extend ?Gmid ?T1 |- ?e2 : ?T0 -| (?T1, true) :: _
        |- exists _ : ctx, ?R; ?G |- subst 0 ?v ?e2 : ?T0 -| _ ] =>
        assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
        subst Gmid;
        eapply subst_preserves_typing; eassumption
    end
  ].

  (* S_App_Fun: H4: R0'; G0 |- ELam T ebody : TFun T1 T0 -| G',
                H7: R0'; G' |- v2 : T1 -| G0',
                H : is_value v2. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v2,
        Hlam : ?R; ?G |- ELam ?T ?ebody : TFun ?T1 ?T0 -| ?Gmid,
        Harg : ?R; ?Gmid |- ?v2 : ?T1 -| ?Ge
        |- exists _ : ctx, ?R; ?G |- subst 0 ?v2 ?ebody : ?T0 -| _ ] =>
        inversion Hlam; subst;
        assert (Hgeq: Ge = Gmid) by (eapply value_context_unchanged; eassumption);
        subst Ge;
        eapply subst_preserves_typing; eassumption
    end
  ].

  (* S_If_True / S_If_False: branch typing exists but in (G' → G0')
     context; the bool's typing gives G0 → G', and EBool b is a value
     so G' = G0. Then the branch's typing matches the goal. *)
  all: try solve [
    match goal with
    | [ Hbool : has_type ?R ?G (EBool ?b) (TBase TBool) ?Gmid,
        Hbr : has_type ?R ?Gmid ?ebr ?T ?G'
        |- exists _ : ctx, has_type ?R ?G ?ebr ?T _ ] =>
        assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; [exact Hbool | constructor]);
        subst Gmid; eexists; exact Hbr
    end
  ].

  (* S_Case_Inl: H5: EInl T v : TSum T1 T2, H8: e1 body under extended ctx.
     inversion H5; subst gives R0'; G0 |- v : T1 -| G' (named some Hi).
     value_context_unchanged ⇒ G' = G0; then subst + Gmid = G0;
     then subst_preserves_typing closes. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hsum : has_type ?R ?G (EInl ?Tann ?vv) (TSum ?T1 ?T2) ?Gmid
        |- exists _ : ctx, has_type ?R ?G (subst 0 ?vv ?ebody) ?T0 _ ] =>
        inversion Hsum; subst;
        match goal with
        | [ Hvt2 : has_type ?R ?G ?vv ?T1 ?Ge,
            Hbr2 : has_type ?R (ctx_extend ?Ge ?T1) ?ebody ?T0 ((?T1, true) :: _)
            |- _ ] =>
            assert (Hgex: Ge = G) by (eapply value_context_unchanged; eassumption);
            subst Ge;
            eapply subst_preserves_typing; [ exact Hbr2 | exact Hvt2 | exact Hv ]
        end
    end
  ].

  (* S_Case_Inr: symmetric — pick the RIGHT branch body via ?T2. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?vv,
        Hsum : has_type ?R ?G (EInr ?Tann ?vv) (TSum ?T1 ?T2) ?Gmid
        |- exists _ : ctx, has_type ?R ?G (subst 0 ?vv ?ebody) ?T0 _ ] =>
        inversion Hsum; subst;
        match goal with
        | [ Hvt2 : has_type ?R ?G ?vv ?T2 ?Ge,
            Hbr2 : has_type ?R (ctx_extend ?Ge ?T2) ?ebody ?T0 ((?T2, true) :: _)
            |- _ ] =>
            assert (Hgex: Ge = G) by (eapply value_context_unchanged; eassumption);
            subst Ge;
            eapply subst_preserves_typing; [ exact Hbr2 | exact Hvt2 | exact Hv ]
        end
    end
  ].

  (* S_Fst: Hp: EPair v1 v2 : TProd T0 T2, goal: v1 typing.
     Inverting Hp gives v1 : T0 -| ?Gmid and v2 : T2 -| G'.
     eassumption matches the v1 typing (post-context is irrelevant
     since the goal's post-context is existential). *)
  all: try solve [
    match goal with
    | [ Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T0 ?T2) ?G'
        |- exists _ : ctx, has_type ?R ?G ?v1 ?T0 _ ] =>
        inversion Hp; subst; eexists; eassumption
    end
  ].

  (* S_Snd: Hp: EPair v1 v2 : TProd T1 T0 (G0 → G0'), goal: v2 typing
     under (G0 → G_out). After inverting Hp, the first child v1 typing
     has post-context Gmid; value_context_unchanged on it ⇒ Gmid = G0
     (since v1 is a value); then the second child's typing
     (Gmid → G0') becomes (G0 → G0'), which matches the goal. *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v1,
        Hp : has_type ?R ?G (EPair ?v1 ?v2) (TProd ?T1 ?T0) ?G'
        |- exists _ : ctx, has_type ?R ?G ?v2 ?T0 _ ] =>
        inversion Hp; subst;
        match goal with
        | [ Hv1t : has_type ?R ?G ?v1 ?T1 ?Gmid |- _ ] =>
            assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
            subst Gmid; eexists; eassumption
        end
    end
  ].

  (* S_Copy: H4: R0'; G0 |- v : T -| G0' (single typing of v),
              H1: is_linear_ty T = false,
              H : is_value v.
     Goal: exists G_out, R0'; G0 |- EPair v v : TProd T T -| G_out.
     value_context_unchanged on H4 ⇒ G0' = G0; then T_Pair applies
     with both child typings being H4 (now (G0 → G0)). *)
  all: try solve [
    match goal with
    | [ Hv : is_value ?v,
        Hvt : has_type ?R ?G ?v ?T ?G',
        Hnl : is_linear_ty ?T = false
        |- exists _ : ctx, has_type ?R ?G (EPair ?v ?v) (TProd ?T ?T) _ ] =>
        assert (Hgeq: G' = G) by (eapply value_context_unchanged; eassumption);
        subst G';
        eexists; eapply T_Pair; eassumption
    end
  ].

  (* === Congruence cases (S_*_Step) ===
     KNOWN BLOCKER (2026-05-21): These tactic blocks pose the
     region-invariance disjunction and specialise the IH, but the
     final [eapply T_Foo; [exact Hout | exact Hsibling]] fails
     because the IH's output context (a Skolem variable from the
     existential) is not in general equal to the sibling premise's
     pre-context. Closing these would require either:
       (a) a "step preserves output context" lemma that says: if
           [R; G |- e : T -| G'] and [(mu, R, e) -->> (mu', R', e')],
           then the IH's existential output equals G'; or
       (b) using [typing_ctx_transfer] / [type_determinacy] +
           [typing_types_agree] to re-type the sibling under the
           IH's output context.
     Both are non-trivial extra lemmas. The blocks below remain in
     place as documentation of the intended pattern; the [fail] in
     the RIGHT branch + the output-context mismatch in the LEFT
     branch leaves them unclosed, so they fall through to Admitted.
     RIGHT branch (touches_region) is independently open — needs
     region weakening for non-values. *)

  (* S_StringConcat_Step1: inner step on e1. 3-way via [step_R_change_shape]:
     - LEFT (R = R'): close via [step_output_context_eq] oracle.
     - MIDDLE (R' = rw :: R): same oracle + [region_add_typing] lifts sibling.
     - RIGHT (R' = remove_first rw R, pop): idtac — needs Brief C.
     Uses [rw] (not [r]) to avoid collision with the existing TString
     region [r] already bound by outer inversion. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e1 (TString ?r0) ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 (TString ?r0) ?Gout1
        |- exists _ : ctx, has_type ?R' ?G (EStringConcat ?e1' ?e2) (TString ?r0) _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[rw [Hadd Hnotin]] | [rw [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_StringConcat; [exact Hout | exact H2]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ rw H2) as H2lift;
          eexists; eapply T_StringConcat; [exact Hout | exact H2lift]
        | idtac ]
    end).

  (* S_StringConcat_Step2: inner on e2; v1 value ⇒ Gmid = G via
     value_context_unchanged. 3-way (uses [rw] to avoid name clash with
     the outer TString region [r]):
     - LEFT (R = R'): IH on H2 gives Hout at input G; direct.
     - MIDDLE (R' = rw :: R): lift the value-sibling H1 via region_add_typing.
     - RIGHT (pop): idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ Hv : is_value ?v1,
        H1 : has_type ?R ?G ?v1 (TString ?r0) ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 (TString ?r0) ?G'
        |- exists _ : ctx, has_type ?R' ?G (EStringConcat ?v1 ?e2') (TString ?r0) _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[rw [Hadd Hnotin]] | [rw [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          eexists; eapply T_StringConcat; [exact H1 | exact Hout]
        | subst R';
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          pose proof (region_add_typing _ _ _ _ _ rw H1) as H1lift;
          eexists; eapply T_StringConcat; [exact H1lift | exact Hout]
        | idtac ]
    end).

  (* S_StringLen_Step is VACUOUS: T_StringLen wraps e at type
     [TBorrow (TString r)], and T_Borrow forces the inner of [EBorrow]
     to be [EVar i] (no step rule fires on EVar) while T_Borrow_Val
     forces it to be a value (values don't step). So the inner Hstep
     premise of S_StringLen_Step has no model — close vacuously like
     S_Borrow_Step elsewhere in this proof. *)
  all: try solve [
    match goal with
    | [ Hin : (_, _, _) -->> (_, _, _),
        Hte : has_type _ _ (EBorrow _) _ _ |- _ ] =>
        inversion Hte; subst;
        [ inversion Hin
        | exfalso;
          match goal with
          | [ Hv : is_value ?v |- _ ] =>
              eapply values_dont_step; [exact Hv | exact Hin]
          end
        ]
    end
  ].

  (* S_Let_Step — 3-way via [step_R_change_shape]:
     - LEFT (R = R'): close via [step_output_context_eq] oracle.
     - MIDDLE (R' = r :: R, push): same oracle + lift sibling H2 via
       [region_add_typing] (preserves both ctx_extend and output).
     - RIGHT (R' = remove_first r R, pop): idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e1 ?T1 ?Gmid,
        H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 ((?T1, true) :: ?G')
        |- exists _ : ctx, has_type ?R' ?G (ELet ?e1' ?e2) ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_Let; [exact Hout | exact H2]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          eexists; eapply T_Let; [exact Hout | exact H2lift]
        | idtac ]
    end).

  (* S_LetLin_Step — 3-way (parallel to S_Let_Step). LEFT + MIDDLE close;
     RIGHT (pop) idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ Hlin : is_linear_ty ?T1 = true,
        H1 : has_type ?R ?G ?e1 ?T1 ?Gmid,
        H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e2 ?T0 ((?T1, true) :: ?G')
        |- exists _ : ctx, has_type ?R' ?G (ELetLin ?e1' ?e2) ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_LetLin; [exact Hlin | exact Hout | exact H2]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          eexists; eapply T_LetLin; [exact Hlin | exact Hout | exact H2lift]
        | idtac ]
    end).

  (* S_App_Step1 — 3-way. LEFT + MIDDLE close via oracle + region_add_typing.
     RIGHT (pop) idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e1 (TFun ?T1 ?T0) ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 ?T1 ?G'
        |- exists _ : ctx, has_type ?R' ?G (EApp ?e1' ?e2) ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_App; [exact Hout | exact H2]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          eexists; eapply T_App; [exact Hout | exact H2lift]
        | idtac ]
    end).

  (* S_App_Step2: v1 value ⇒ Gmid = G. 3-way:
     - LEFT (R = R'): IH on H2 gives Hout at input G; direct.
     - MIDDLE (R' = r :: R): lift the value-sibling H1 via region_add_typing.
     - RIGHT (pop): idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ Hv : is_value ?v1,
        H1 : has_type ?R ?G ?v1 (TFun ?T1 ?T0) ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 ?T1 ?G'
        |- exists _ : ctx, has_type ?R' ?G (EApp ?v1 ?e2') ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          eexists; eapply T_App; [exact H1 | exact Hout]
        | subst R';
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          pose proof (region_add_typing _ _ _ _ _ r H1) as H1lift;
          eexists; eapply T_App; [exact H1lift | exact Hout]
        | idtac ]
    end).

  (* S_If_Step — 3-way. LEFT + MIDDLE close (both branches lifted via
     region_add_typing in MIDDLE). RIGHT (pop) idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e1 (TBase TBool) ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 ?T0 ?G',
        H3 : has_type ?R ?Gmid ?e3 ?T0 ?G'
        |- exists _ : ctx, has_type ?R' ?G (EIf ?e1' ?e2 ?e3) ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_If; [exact Hout | exact H2 | exact H3]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          pose proof (region_add_typing _ _ _ _ _ r H3) as H3lift;
          eexists; eapply T_If; [exact Hout | exact H2lift | exact H3lift]
        | idtac ]
    end).

  (* S_Pair_Step1 — 3-way. LEFT + MIDDLE close. RIGHT (pop) idtac. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e1 ?T1 ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 ?T2 ?G'
        |- exists _ : ctx, has_type ?R' ?G (EPair ?e1' ?e2) (TProd ?T1 ?T2) _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_Pair; [exact Hout | exact H2]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          eexists; eapply T_Pair; [exact Hout | exact H2lift]
        | idtac ]
    end).

  (* S_Pair_Step2: v1 value ⇒ Gmid = G. 3-way:
     - LEFT (R = R'): IH on H2 gives Hout at G; direct.
     - MIDDLE (R' = r :: R): lift the value-sibling H1.
     - RIGHT (pop): idtac. *)
  all: try (
    match goal with
    | [ Hv : is_value ?v1,
        H1 : has_type ?R ?G ?v1 ?T1 ?Gmid,
        H2 : has_type ?R ?Gmid ?e2 ?T2 ?G'
        |- exists _ : ctx, has_type ?R' ?G (EPair ?v1 ?e2') (TProd ?T1 ?T2) _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          eexists; eapply T_Pair; [exact H1 | exact Hout]
        | subst R';
          assert (Hgeq: Gmid = G) by (eapply value_context_unchanged; eassumption);
          subst Gmid;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H2) as [Gout Hout];
          pose proof (region_add_typing _ _ _ _ _ r H1) as H1lift;
          eexists; eapply T_Pair; [exact H1lift | exact Hout]
        | idtac ]
    end).

  (* S_Case_Step — 3-way. LEFT + MIDDLE close (both branch typings lifted
     via region_add_typing in MIDDLE). RIGHT (pop) idtac — needs Brief C. *)
  all: try (
    match goal with
    | [ H1 : has_type ?R ?G ?e (TSum ?T1 ?T2) ?Gmid,
        H2 : has_type ?R (ctx_extend ?Gmid ?T1) ?e1 ?T0 ((?T1, true) :: ?G'),
        H3 : has_type ?R (ctx_extend ?Gmid ?T2) ?e2 ?T0 ((?T2, true) :: ?G')
        |- exists _ : ctx, has_type ?R' ?G (ECase ?e' ?e1 ?e2) ?T0 _ ] =>
        pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
          as [HeqR | [[r [Hadd Hnotin]] | [r [Hrem HinR]]]];
        [ rewrite <- HeqR in *;
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          eexists; eapply T_Case; [exact Hout | exact H2 | exact H3]
        | subst R';
          edestruct (IHHstep _ _ _ _ _ _ eq_refl eq_refl _ _ _ H1) as [Gout Hout];
          assert (Heq_out : Gmid = Gout) by
            (eapply step_output_context_eq;
              [ exact Hstep | exact H1 | exact Hout ]);
          subst Gmid;
          pose proof (region_add_typing _ _ _ _ _ r H2) as H2lift;
          pose proof (region_add_typing _ _ _ _ _ r H3) as H3lift;
          eexists; eapply T_Case; [exact Hout | exact H2lift | exact H3lift]
        | idtac ]
    end).

(* Show Existentials. *)  (* uncomment to dump the remaining open goals.
                            Post-MIDDLE narrowing (2026-05-26 late eve):
                            10 POP sub-cases (`Hrem : R0' = remove_first r R0`
                            and `HinR : In r R0` in scope) + 1 S_Region_Step
                            = 11 admits. The 10 POP cases share the same
                            shape: stepped child reaches R0' = remove_first r R0
                            with surviving sibling still typed at R0; needs
                            non-value region-env weakening (Brief C structural
                            lemma; the [typing_free_of_absent_region] lemma
                            at Semantics.v:3346 is the kernel). *)
Admitted.
(* PROOF STATUS [preservation] — ADMITTED, down to 12 open goals
   (from 910 cross-case, via PR #102's remember-cfg + PR #106's
   universal-IH revert + 2026-05-21 per-case per-step closures for
   β-reduction, projection, branch-selection, and linear-copy cases).
   A region-invariance lemma [step_R_eq_or_touches_region] now lives
   just before this theorem and dispatches the non-region-step half
   of congruence cases (left branch only — see CLOSURE STATUS below).

   CLOSURE STATUS (2026-05-21):
     Closed (via per-case [all: try solve [match goal ...]]):
       S_Let_Val, S_LetLin_Val (β with subst_preserves_typing)
       S_App_Fun                (β with inversion of ELam typing)
       S_If_True, S_If_False    (branch-select via VBool unchanged-ctx)
       S_Fst, S_Snd             (projection via pair-inversion)
       S_Case_Inl, S_Case_Inr   (β with inversion of EInl/EInr typing)
       S_Copy                   (linear via value_context_unchanged + T_Pair)
     Still open (12 goals — see Existential dump above):
       S_StringConcat_Step1/2, S_StringLen_Step,
       S_Let_Step, S_LetLin_Step, S_App_Step1/2,
       S_If_Step, S_Pair_Step1/2, S_Case_Step
         BLOCKER: the IH's output context (a Skolem variable) is
         not in general equal to the sibling premise's pre-context,
         so the [exact Hout; exact Hsibling] closure fails at
         T_Foo's middle-context unification. Either a "step
         preserves output context" lemma OR a context-transfer
         re-typing of the sibling is needed.
       S_Region_Step
         BLOCKER: needs region-env weakening for non-values
         (touches_region branch of step_R_eq_or_touches_region).
   Tactic blocks for all twelve open S_*_Step cases remain in place
   as documentation of the intended pattern — they pose the
   disjunction lemma and dispatch the left branch, but [fail] in
   the right (touches_region) branch and silently fail in the left
   branch when the output-context mismatch blocks the final eapply. *)
(* PROOF STATUS PRIOR HISTORY:

   PRIOR STATE (before the `remember (mu, R, e) as cfg` introduction at L3232):
   `induction Hstep; intros G0 T0 G0' Htype; inversion Htype; subst; ...`
   left **910 goals open** = 35 (step rules) × 26 (typing rules) — the FULL
   cross-case combinatorial, because `induction Hstep` did not substitute
   the outer expression slot `e` to the constructor's form, so `inversion
   Htype` produced all 26 arms instead of just the diagonal. Cross-cases
   (e.g. S_StringNew step + T_Unit type) had no discriminating equation in
   scope, so `try solve [exfalso; discriminate | exfalso; congruence]` closed
   none of them.

   CURRENT STATE: ~29 real diagonal goals remain — one per step rule, modulo
   the 6 that the existing `try solve [...]` chain closes once the expression
   slots are concrete. Remediation per case:
     - Axiom cases needing explicit reconstruction: S_StringNew, S_StringConcat,
       S_StringLen (typing the result location/literal via T_Loc/T_I32).
     - β-reduction cases needing `subst_preserves_typing`: S_Let_Val,
       S_LetLin_Val, S_App_Fun, S_If_True/False, S_Fst, S_Snd,
       S_Case_Inl/Inr.
     - Congruence cases needing IH + reconstruction: S_*_Step variants.
     - Region: S_Region_Enter, S_Region_Step, S_Region_Exit (the prior named
       "remaining case" + 2 the in-file comment did not name).
     - Linear: S_Drop, S_Copy.

   Supporting lemmas already Qed: subst_preserves_typing,
   region_env_perm_typing, region_add_typing, region_shrink_preserves_typing,
   values_dont_step. Per the handoff doc, the S_Region_Step + T_Region_Active
   case still blocks on a region-env *weakening* lemma for non-values, which
   does not yet exist. The other 28 are per-case tactic glue.

   97% reduction (910 → 29) via the standard preservation pattern (remember
   the configs so `induction Hstep`'s substitution is recovered through
   `inversion Hcfg; subst`). See formal/PRESERVATION-HANDOFF.md for the
   per-case checklist (the handoff doc's 910-goal diagnostic captures the
   PRIOR state; the same Show. recipe applied here yields the 29-goal
   diagnostic for ongoing work). *)
