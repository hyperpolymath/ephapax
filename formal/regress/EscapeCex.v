(* SPDX-License-Identifier: MPL-2.0 *)
(** * EscapeCex — region escape through a [TFun] closure.

    A closed program, well typed in the current L1 judgment
    ([has_type_l1 Linear [] [] ...]), allocates a string in region [r],
    builds a closure that captures a borrow of it, drops the string, and
    returns the closure out of [r]. [T_Region_L1]'s escape check
    [~ In r (free_regions T)] is vacuous here because [TFun] carries no
    region information. After four steps the configuration is a
    well-typed non-value that cannot step: [S_Region_Exit] (and
    [S_Region_Exit_Echo]) are blocked by the syntactic guard
    [expr_free_of_region r v], since the closure body mentions
    [ELoc 0 r]. So progress fails. Were the guard dropped, the exit
    would produce a value untypable at its original type in the
    post-exit region env (see [escaped_value_untypable_at_type]). *)

From Ephapax Require Import Syntax Typing TypingL1 Semantics Semantics_L1 Modality.
Require Import Coq.Lists.List Coq.Strings.String. Import ListNotations.
Open Scope string_scope.

Definition r : region_name := "r".
Definition Targ : ty := TRef Lin (TBase TUnit).
Definition Tclo : ty := TFun Targ (TProd (TBase TUnit) (TBase TI32)).
Definition Tprog : ty := TProd Tclo (TBase TUnit).

(** Surface closure: [fun (k : Targ) => (drop k, strlen &s)], [s] = index 1. *)
Definition clo : expr :=
  ELam Targ (EPair (EDrop (EVar 0)) (EStringLen (EVar 1))).
(** [region r { let s = new@r "s" in (clo, drop s) }] *)
Definition prog : expr :=
  ERegion r (ELet (EStringNew r "s") (EPair clo (EDrop (EVar 0)))).

(** Runtime forms after substitution of the location. *)
Definition clo' : expr :=
  ELam Targ (EPair (EDrop (EVar 0)) (EStringLen (ELoc 0 r))).
Definition stuck_expr : expr := ERegion r (EPair clo' EUnit).

(** Root cause: the result type mentions no region at all. *)
Lemma Tprog_region_free : Typing.free_regions Tprog = [].
Proof. reflexivity. Qed.

(** Typed pre-state: the closed program, empty store, empty region env. *)
Lemma prog_typed : has_type_l1 Linear [] [] prog Tprog [] [].
Proof.
  unfold prog, Tprog, Tclo, clo, Targ.
  change (@nil region_name) with (remove_first_L1 r [r]) at 2.
  apply T_Region_L1; [simpl; auto | simpl; intros [] | simpl; auto |].
  eapply T_Let_L1.
  - apply T_StringNew_L1. simpl; auto.
  - eapply T_Pair_L1.
    + apply T_Lam_L1_Linear. eapply T_Pair_L1.
      * apply (T_Drop_L1 Linear _ _ _ _ _ (TRef Lin (TBase TUnit))); [reflexivity|].
        eapply T_Var_Lin_L1; reflexivity.
      * eapply T_StringLen_L1. eapply T_Borrow_L1. reflexivity.
    + apply (T_Drop_L1 Linear _ _ _ _ _ (TString r)); [reflexivity|].
      eapply T_Var_Lin_L1; reflexivity.
Qed.

(** The four steps. *)
Lemma step1 : step ([], [], prog) ([], [r], prog).
Proof. apply S_Region_Enter. simpl; auto. Qed.

Lemma step2 :
  step ([], [r], prog)
       ([CString r "s"], [r],
        ERegion r (ELet (ELoc 0 r) (EPair clo (EDrop (EVar 0))))).
Proof.
  apply S_Region_Step; [simpl; auto|].
  apply S_Let_Step. apply S_StringNew; [simpl; auto | reflexivity].
Qed.

Lemma step3 :
  step ([CString r "s"], [r],
        ERegion r (ELet (ELoc 0 r) (EPair clo (EDrop (EVar 0)))))
       ([CString r "s"], [r], ERegion r (EPair clo' (EDrop (ELoc 0 r)))).
Proof.
  apply S_Region_Step; [simpl; auto|].
  apply (S_Let_Val [CString r "s"] [r] (ELoc 0 r) (EPair clo (EDrop (EVar 0)))).
  constructor.
Qed.

Lemma step4 :
  step ([CString r "s"], [r], ERegion r (EPair clo' (EDrop (ELoc 0 r))))
       ([CFree], [r], stuck_expr).
Proof.
  apply S_Region_Step; [simpl; auto|].
  apply S_Pair_Step2; [constructor|].
  change [CFree] with (mem_write [CString r "s"] 0 CFree).
  apply S_Drop.
Qed.

Lemma prog_reaches_stuck : multi_step ([], [], prog) ([CFree], [r], stuck_expr).
Proof.
  eapply MS_Step; [exact step1|].
  eapply MS_Step; [exact step2|].
  eapply MS_Step; [exact step3|].
  eapply MS_Step; [exact step4|].
  apply MS_Refl.
Qed.

(** Bad post-state 1: well typed (same type, same final env) ... *)
Lemma stuck_typed : has_type_l1 Linear [r] [] stuck_expr Tprog [] [].
Proof.
  unfold stuck_expr, Tprog, Tclo, clo', Targ.
  change (@nil region_name) with (remove_first_L1 r [r]) at 2.
  apply T_Region_Active_L1; [simpl; auto | simpl; intros [] | simpl; auto |].
  eapply T_Pair_L1.
  - apply T_Lam_L1_Linear. eapply T_Pair_L1.
    + apply (T_Drop_L1 Linear _ _ _ _ _ (TRef Lin (TBase TUnit))); [reflexivity|].
      eapply T_Var_Lin_L1; reflexivity.
    + eapply T_StringLen_L1. apply T_Borrow_Val_L1; [constructor|].
      apply T_Loc_L1. simpl; auto.
  - apply T_Unit_L1.
Qed.

(** ... not a value ... *)
Lemma stuck_not_value : ~ is_value stuck_expr.
Proof. intro H; inversion H. Qed.

(** ... and cannot step: progress fails. *)
Theorem stuck_no_step : forall c', ~ step ([CFree], [r], stuck_expr) c'.
Proof.
  intros c' H. unfold stuck_expr in H. inversion H; subst.
  - (* S_Region_Enter *)
    match goal with Hn : ~ In r [r] |- _ => apply Hn; simpl; auto end.
  - (* S_Region_Exit: guard fails, the closure mentions ELoc 0 r *)
    match goal with Hf : expr_free_of_region r _ |- _ =>
      cbn in Hf; destruct Hf as [[_ Hne] _]; apply Hne; reflexivity end.
  - (* S_Region_Exit_Echo: same guard *)
    match goal with Hf : expr_free_of_region r _ |- _ =>
      cbn in Hf; destruct Hf as [[_ Hne] _]; apply Hne; reflexivity end.
  - (* S_Region_Step: the body is a value *)
    eapply values_dont_step; [| eassumption]. repeat constructor.
Qed.

(** Headline: a closed well-typed program reaches, in 4 steps, a
    well-typed configuration that is neither a value nor able to step. *)
Theorem escape_cex :
  has_type_l1 Linear [] [] prog Tprog [] [] /\
  multi_step ([], [], prog) ([CFree], [r], stuck_expr) /\
  has_type_l1 Linear [r] [] stuck_expr Tprog [] [] /\
  ~ is_value stuck_expr /\
  (forall c', ~ step ([CFree], [r], stuck_expr) c').
Proof.
  repeat split.
  - exact prog_typed.
  - exact prog_reaches_stuck.
  - exact stuck_typed.
  - exact stuck_not_value.
  - exact stuck_no_step.
Qed.

(** Counterfactual: the escaped value, at the post-exit env [[]], is
    untypable at its original type in any modality and context. So
    removing the [expr_free_of_region] guard would turn the progress
    failure into a preservation failure. *)
Theorem escaped_value_untypable_at_type :
  forall m G R' G', ~ has_type_l1 m [] G (EPair clo' EUnit) Tprog R' G'.
Proof.
  intros m G R' G' H. unfold clo', Tprog, Tclo, Targ in H.
  inversion H; subst.
  match goal with Hl : has_type_l1 _ [] _ (ELam _ _) _ _ _ |- _ =>
    inversion Hl; subst end;
  match goal with Hb : has_type_l1 _ [] _ (EPair _ _) _ [] _ |- _ =>
    inversion Hb; subst end;
  match goal with Hd : has_type_l1 _ [] _ (EDrop (EVar 0)) _ _ _ |- _ =>
    inversion Hd; subst end;
  repeat match goal with Hv : has_type_l1 _ _ _ (EVar 0) _ _ _ |- _ =>
    inversion Hv; subst; clear Hv end;
  match goal with Hs : has_type_l1 _ _ _ (EStringLen _) _ _ _ |- _ =>
    inversion Hs; subst end;
  match goal with Hb : has_type_l1 _ _ _ (EBorrow _) _ _ _ |- _ =>
    inversion Hb; subst end;
  match goal with Hl : has_type_l1 _ _ _ (ELoc _ _) _ _ _ |- _ =>
    inversion Hl; subst end;
  match goal with Hin : In _ [] |- _ => inversion Hin end.
Qed.

Print Assumptions Tprog_region_free.
Print Assumptions prog_typed.
Print Assumptions prog_reaches_stuck.
Print Assumptions stuck_typed.
Print Assumptions stuck_not_value.
Print Assumptions stuck_no_step.
Print Assumptions escape_cex.
Print Assumptions escaped_value_untypable_at_type.
