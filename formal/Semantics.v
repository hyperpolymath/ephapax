(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell *)

(** * Ephapax Operational Semantics (De Bruijn)

    Small-step reduction semantics using De Bruijn indices.
    No variable names in the runtime — environment is indexed.

    This eliminates the shadowing problem that plagued the
    named-variable version's typing_preserves_domain proof.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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

(** Runtime values — closures no longer carry variable names *)
Inductive runtime_val : Type :=
  | RUnit    : runtime_val
  | RBool    : bool -> runtime_val
  | RI32     : nat -> runtime_val
  | RLoc     : loc -> region_name -> runtime_val
  | RClosure : ty -> expr -> runtime_val        (** No variable name *)
  | RPair    : runtime_val -> runtime_val -> runtime_val
  | RInl     : ty -> runtime_val -> runtime_val
  | RInr     : ty -> runtime_val -> runtime_val
  | RBorrow  : loc -> runtime_val.

(** Runtime environment: De Bruijn indexed — just a list of values.
    Index 0 = head (most recently bound). *)
Definition env := list runtime_val.

Definition env_lookup (rho : env) (i : var) : option runtime_val :=
  nth_error rho i.

Definition env_extend (rho : env) (v : runtime_val) : env :=
  v :: rho.

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

(** ** Configuration *)

Definition config := (mem * region_env * env * expr)%type.

(** ** Value Conversion *)

Fixpoint val_to_expr (v : runtime_val) : expr :=
  match v with
  | RUnit => EUnit
  | RBool b => EBool b
  | RI32 n => EI32 n
  | RLoc l r => ELoc l r
  | RClosure T e => ELam T e
  | RPair v1 v2 => EPair (val_to_expr v1) (val_to_expr v2)
  | RInl T2 v' => EInl T2 (val_to_expr v')
  | RInr T1 v' => EInr T1 (val_to_expr v')
  | RBorrow l => ELoc l ""%string
  end.

Fixpoint expr_to_val (e : expr) : runtime_val :=
  match e with
  | EUnit => RUnit
  | EBool b => RBool b
  | EI32 n => RI32 n
  | ELoc l r => RLoc l r
  | ELam T body => RClosure T body
  | EPair e1 e2 => RPair (expr_to_val e1) (expr_to_val e2)
  | EInl T2 e' => RInl T2 (expr_to_val e')
  | EInr T1 e' => RInr T1 (expr_to_val e')
  | _ => RUnit
  end.

(** ** Small-Step Reduction *)

Reserved Notation "c1 '-->>' c2" (at level 70).

Inductive step : config -> config -> Prop :=

  (** Variables: look up by De Bruijn index *)
  | S_Var : forall mu R rho i v,
      env_lookup rho i = Some v ->
      (mu, R, rho, EVar i) -->> (mu, R, rho, val_to_expr v)

  (** String operations *)
  | S_StringNew : forall mu R rho r s mu' l,
      In r R ->
      mem_alloc mu (CString r s) = (mu', l) ->
      (mu, R, rho, EStringNew r s) -->> (mu', R, rho, ELoc l r)

  | S_StringConcat : forall mu R rho l1 l2 r s1 s2 mu' l',
      mem_read mu l1 = Some (CString r s1) ->
      mem_read mu l2 = Some (CString r s2) ->
      mem_alloc (mem_write (mem_write mu l1 CFree) l2 CFree)
                (CString r (s1 ++ s2)) = (mu', l') ->
      (mu, R, rho, EStringConcat (ELoc l1 r) (ELoc l2 r))
        -->> (mu', R, rho, ELoc l' r)

  | S_StringConcat_Step1 : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EStringConcat e1 e2) -->> (mu', R', rho', EStringConcat e1' e2)

  | S_StringConcat_Step2 : forall mu R rho v1 e2 e2' mu' R' rho',
      is_value v1 ->
      (mu, R, rho, e2) -->> (mu', R', rho', e2') ->
      (mu, R, rho, EStringConcat v1 e2) -->> (mu', R', rho', EStringConcat v1 e2')

  | S_StringLen : forall mu R rho l r s,
      mem_read mu l = Some (CString r s) ->
      (mu, R, rho, EStringLen (ELoc l r)) -->> (mu, R, rho, EI32 (String.length s))

  | S_StringLen_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EStringLen e) -->> (mu', R', rho', EStringLen e')

  (** Let: De Bruijn — push value onto env, evaluate body *)
  | S_Let_Val : forall mu R rho v1 e2,
      is_value v1 ->
      (mu, R, rho, ELet v1 e2) -->> (mu, R, env_extend rho (expr_to_val v1), e2)

  | S_Let_Step : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, ELet e1 e2) -->> (mu', R', rho', ELet e1' e2)

  | S_LetLin_Val : forall mu R rho v1 e2,
      is_value v1 ->
      (mu, R, rho, ELetLin v1 e2) -->> (mu, R, env_extend rho (expr_to_val v1), e2)

  | S_LetLin_Step : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, ELetLin e1 e2) -->> (mu', R', rho', ELetLin e1' e2)

  (** Application: De Bruijn — push argument onto env *)
  | S_App_Fun : forall mu R rho T ebody v2,
      is_value v2 ->
      (mu, R, rho, EApp (ELam T ebody) v2) -->>
        (mu, R, env_extend rho (expr_to_val v2), ebody)

  | S_App_Step1 : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EApp e1 e2) -->> (mu', R', rho', EApp e1' e2)

  | S_App_Step2 : forall mu R rho v1 e2 e2' mu' R' rho',
      is_value v1 ->
      (mu, R, rho, e2) -->> (mu', R', rho', e2') ->
      (mu, R, rho, EApp v1 e2) -->> (mu', R', rho', EApp v1 e2')

  (** Conditionals *)
  | S_If_True : forall mu R rho e2 e3,
      (mu, R, rho, EIf (EBool true) e2 e3) -->> (mu, R, rho, e2)

  | S_If_False : forall mu R rho e2 e3,
      (mu, R, rho, EIf (EBool false) e2 e3) -->> (mu, R, rho, e3)

  | S_If_Step : forall mu R rho e1 e1' e2 e3 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EIf e1 e2 e3) -->> (mu', R', rho', EIf e1' e2 e3)

  (** Products *)
  | S_Pair_Step1 : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EPair e1 e2) -->> (mu', R', rho', EPair e1' e2)

  | S_Pair_Step2 : forall mu R rho v1 e2 e2' mu' R' rho',
      is_value v1 ->
      (mu, R, rho, e2) -->> (mu', R', rho', e2') ->
      (mu, R, rho, EPair v1 e2) -->> (mu', R', rho', EPair v1 e2')

  | S_Fst : forall mu R rho v1 v2,
      is_value v1 -> is_value v2 ->
      (mu, R, rho, EFst (EPair v1 v2)) -->> (mu, R, rho, v1)

  | S_Fst_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EFst e) -->> (mu', R', rho', EFst e')

  | S_Snd : forall mu R rho v1 v2,
      is_value v1 -> is_value v2 ->
      (mu, R, rho, ESnd (EPair v1 v2)) -->> (mu, R, rho, v2)

  | S_Snd_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, ESnd e) -->> (mu', R', rho', ESnd e')

  (** Sums *)
  | S_Inl_Step : forall mu R rho T e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EInl T e) -->> (mu', R', rho', EInl T e')

  | S_Inr_Step : forall mu R rho T e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EInr T e) -->> (mu', R', rho', EInr T e')

  (** Case: De Bruijn — push matched value onto env *)
  | S_Case_Inl : forall mu R rho T v e1 e2,
      is_value v ->
      (mu, R, rho, ECase (EInl T v) e1 e2) -->>
        (mu, R, env_extend rho (expr_to_val v), e1)

  | S_Case_Inr : forall mu R rho T v e1 e2,
      is_value v ->
      (mu, R, rho, ECase (EInr T v) e1 e2) -->>
        (mu, R, env_extend rho (expr_to_val v), e2)

  | S_Case_Step : forall mu R rho e e' e1 e2 mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, ECase e e1 e2) -->> (mu', R', rho', ECase e' e1 e2)

  (** Regions *)
  | S_Region_Enter : forall mu R rho r e,
      ~ In r R ->
      (mu, R, rho, ERegion r e) -->> (mu, r :: R, rho, ERegion r e)

  | S_Region_Exit : forall mu R rho r v,
      is_value v ->
      In r R ->
      (mu, R, rho, ERegion r v) -->>
        (mem_free_region mu r, remove_first r R, rho, v)

  | S_Region_Step : forall mu R rho r e e' mu' R' rho',
      In r R ->
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, ERegion r e) -->> (mu', R', rho', ERegion r e')

  (** Borrowing *)
  | S_Borrow_Val : forall mu R rho v,
      is_value v ->
      (mu, R, rho, EBorrow v) -->> (mu, R, rho, v)

  | S_Borrow_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EBorrow e) -->> (mu', R', rho', EBorrow e')

  (** Drop *)
  | S_Drop : forall mu R rho l r,
      (mu, R, rho, EDrop (ELoc l r)) -->>
        (mem_write mu l CFree, R, rho, EUnit)

  | S_Drop_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, EDrop e) -->> (mu', R', rho', EDrop e')

  (** Copy *)
  | S_Copy : forall mu R rho v,
      is_value v ->
      (mu, R, rho, ECopy v) -->> (mu, R, rho, EPair v v)

  | S_Copy_Step : forall mu R rho e e' mu' R' rho',
      (mu, R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, ECopy e) -->> (mu', R', rho', ECopy e')

where "c1 '-->>' c2" := (step c1 c2).

(** ** Multi-Step *)

Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall c, multi_step c c
  | MS_Step : forall c1 c2 c3,
      step c1 c2 -> multi_step c2 c3 -> multi_step c1 c3.

Notation "c1 '-->*' c2" := (multi_step c1 c2) (at level 70).

(** ** Infrastructure Lemmas *)

Lemma val_to_expr_to_val :
  forall v, is_value v -> val_to_expr (expr_to_val v) = v.
Proof.
  intros v Hval. induction Hval; simpl; try reflexivity.
  - rewrite IHHval1, IHHval2. reflexivity.
  - rewrite IHHval. reflexivity.
  - rewrite IHHval. reflexivity.
Qed.

Lemma val_to_expr_is_value :
  forall v, is_value (val_to_expr v).
Proof.
  induction v; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply VPair; assumption.
  - apply VInl; assumption.
  - apply VInr; assumption.
  - constructor.
Qed.

(** Values cannot step — fundamental lemma for progress and no_leaks *)
Lemma values_dont_step :
  forall v mu R rho mu' R' rho' e',
    is_value v -> (mu, R, rho, v) -->> (mu', R', rho', e') -> False.
Proof.
  intros v mu R rho mu' R' rho' e' Hval Hstep.
  generalize dependent e'. generalize dependent rho'.
  generalize dependent R'. generalize dependent mu'.
  generalize dependent rho. generalize dependent R.
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
  forall mu R rho r e mu1 R1 rho1 e1,
    (mu, R, rho, ERegion r e) -->> (mu1, R1, rho1, e1) ->
    (* Enter *) (mu1 = mu /\ R1 = r :: R /\ rho1 = rho /\ e1 = ERegion r e)
    (* Exit *)  \/ (In r R /\ is_value e /\ mu1 = mem_free_region mu r
                    /\ R1 = remove_first r R /\ rho1 = rho /\ e1 = e)
    (* Step *)  \/ (In r R /\ exists e',
                    (mu, R, rho, e) -->> (mu1, R1, rho1, e')
                    /\ e1 = ERegion r e').
Proof.
  intros. inversion H; subst.
  + left. auto.
  + right. left. repeat (split; [auto; fail|]). auto.
  + right. right. split; [assumption|].
    eexists. split; [eassumption | reflexivity].
Qed.

(** env_consistent: every variable in the typing context has a runtime binding *)
Definition env_consistent (rho : env) (G : ctx) : Prop :=
  forall i T u, ctx_lookup G i = Some (T, u) ->
    exists v, env_lookup rho i = Some v.

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

(** val_locs_valid for runtime values *)
Fixpoint val_locs_valid (mu : mem) (v : runtime_val) : Prop :=
  match v with
  | RLoc l r => exists c, mem_read mu l = Some c /\ c <> CFree
  | RPair v1 v2 => val_locs_valid mu v1 /\ val_locs_valid mu v2
  | RInl _ v' => val_locs_valid mu v'
  | RInr _ v' => val_locs_valid mu v'
  | RClosure _ e => True
  | RBorrow l => exists c, mem_read mu l = Some c /\ c <> CFree
  | _ => True
  end.

(** ** Key Theorems *)

(** *** Theorem 1: No Memory Leaks (Qed)

    When a region block completes evaluation (multi-steps to a value with
    empty region stack), all memory cells for that region are freed.

    Proof strategy: induction on multi_step. Three cases per step:
    - Region Enter: recurse (expression still wrapped in ERegion)
    - Region Exit: mem_free_region clears all cells, value can't step further
    - Region Step: recurse (body stepped, still wrapped in ERegion) *)

Lemma no_leaks_gen :
  forall c1 c2, multi_step c1 c2 ->
    forall r mu R rho e,
    c1 = (mu, R, rho, ERegion r e) ->
    forall mu' rho' v l s,
    c2 = (mu', ([] : region_env), rho', v) ->
    is_value v ->
    mem_read mu' l = Some (CString r s) -> False.
Proof.
  intros c1 c2 Hmulti.
  induction Hmulti as [c | ca cb cc Hstep Hmulti IH].
  - intros. subst. injection H0; intros; subst. inversion H1.
  - intros r mu R rho e Hca mu' rho' v l s Hcc Hval Hread.
    subst ca.
    destruct cb as [[[mu1 R1] rho1] e1].
    pose proof (step_from_eregion _ _ _ _ _ _ _ _ _ Hstep) as Hcases.
    destruct Hcases as
      [[-> [-> [-> ->]]]
      | [[_ [Hval_e [-> [-> [-> ->]]]]]
      | [_ [e' [Hsub ->]]]]].
    + (* Enter: expression unchanged, region added to R *)
      eapply (IH r mu (r :: R) rho e eq_refl mu' rho' v l s
              Hcc Hval Hread).
    + (* Exit: body is a value, memory freed *)
      assert (Hcc2: cc = (mem_free_region mu r, remove_first r R, rho, e)).
      { inversion Hmulti.
        - reflexivity.
        - destruct c2 as [[[? ?] ?] ?].
          exfalso. eapply values_dont_step; eassumption. }
      assert (mem_free_region mu r = mu') by congruence.
      assert (e = v) by congruence.
      subst. eapply mem_free_region_clears. eassumption.
    + (* Step: body reduced, still wrapped in ERegion *)
      eapply (IH r _ _ _ e' eq_refl mu' rho' v l s
              Hcc Hval Hread).
Qed.

Theorem no_leaks :
  forall mu R rho r e mu' rho' v,
    multi_step (mu, R, rho, ERegion r e) (mu', [], rho', v) ->
    is_value v ->
    forall l s, mem_read mu' l = Some (CString r s) -> False.
Proof.
  intros. eapply no_leaks_gen; try eassumption; reflexivity.
Qed.

(** *** Theorem 2: Memory Safety (Qed)

    If all environment values have valid memory locs before and after the step,
    and the expression's locs are valid, then the output environment's values
    also have valid locs.

    Proof by fix (induction on step derivation). Non-env-changing cases are
    trivial. Env-extending cases (Let/LetLin/App/Case) use value_expr_to_val_locs.
    Sub-step cases use the IH recursively. *)

Lemma value_expr_to_val_locs :
  forall mu e,
    is_value e -> expr_locs_valid mu e -> val_locs_valid mu (expr_to_val e).
Proof.
  intros mu e Hval.
  induction Hval; simpl; intro Hlocs.
  1-4: exact I.
  - destruct Hlocs as [H1 H2]. split; auto.
  - auto.
  - auto.
  - destruct Hlocs as [sx Hsx].
    refine (ex_intro _ _ (conj Hsx _)). discriminate.
Qed.

Lemma env_extend_valid :
  forall mu rho v,
    (forall i w, env_lookup rho i = Some w -> val_locs_valid mu w) ->
    val_locs_valid mu v ->
    (forall i w, env_lookup (env_extend rho v) i = Some w -> val_locs_valid mu w).
Proof.
  intros mu rho v Henv Hv i w Hlookup.
  destruct i; simpl in Hlookup.
  - injection Hlookup as ->. exact Hv.
  - eapply Henv. exact Hlookup.
Qed.

Theorem memory_safety :
  forall mu R rho e mu' R' rho' e',
    (mu, R, rho, e) -->> (mu', R', rho', e') ->
    (forall i v, env_lookup rho i = Some v -> val_locs_valid mu v) ->
    (forall i v, env_lookup rho i = Some v -> val_locs_valid mu' v) ->
    expr_locs_valid mu e ->
    (forall i v, env_lookup rho' i = Some v -> val_locs_valid mu' v).
Proof.
  fix IH 9.
  intros mu R rho e mu' R' rho' e' Hstep Henv_mu Henv_mu' Hlocs.
  inversion Hstep; subst;
    try (intros i0 v0 Hlu; eapply Henv_mu'; exact Hlu).
  all: try (apply env_extend_valid; [exact Henv_mu'|];
            apply value_expr_to_val_locs; [eassumption|];
            simpl in Hlocs; tauto).
  all: eapply IH; [eassumption | exact Henv_mu | exact Henv_mu' |];
       simpl in Hlocs; tauto.
Qed.

(** *** Theorem 3: Progress (Admitted — needs retacticking) *)
Theorem progress :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall mu rho,
      env_consistent rho G ->
      expr_locs_valid mu e ->
      is_value e \/ exists mu' R' rho' e', (mu, R, rho, e) -->> (mu', R', rho', e').
Proof.
  admit.
Admitted.

(** *** Theorem 4: Preservation (Admitted — needs retacticking) *)
Definition env_typed (R : region_env) (rho : env) (G : ctx) : Prop :=
  forall i T u, ctx_lookup G i = Some (T, u) -> u = false ->
    exists v, env_lookup rho i = Some v /\
    forall G_a, R; G_a |- val_to_expr v : T -| G_a.

Theorem preservation :
  forall R G e T G' mu rho mu' rho' e',
    R; G |- e : T -| G' ->
    (mu, R, rho, e) -->> (mu', R, rho', e') ->
    env_typed R rho G ->
    exists G'' G_out, R; G'' |- e' : T -| G_out.
Proof.
  admit.
Admitted.
