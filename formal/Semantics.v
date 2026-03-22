(* SPDX-License-Identifier: EUPL-1.2 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)

(** * Ephapax Operational Semantics

    Small-step reduction semantics with explicit memory model.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import Syntax.
Require Import Typing.

(** ** Memory Model *)

(** A location is an address in linear memory *)
Definition loc := nat.

(** Memory cells: store string data with region tag *)
Inductive mem_cell : Type :=
  | CString : region_name -> string -> mem_cell
  | CFree   : mem_cell.

(** Memory is a list of cells (simplified) *)
Definition mem := list mem_cell.

(** Runtime values include locations *)
Inductive runtime_val : Type :=
  | RUnit   : runtime_val
  | RBool   : bool -> runtime_val
  | RI32    : nat -> runtime_val
  | RLoc    : loc -> runtime_val                   (* Pointer to memory *)
  | RClosure : var -> ty -> expr -> runtime_val   (* Closure *)
  | RPair   : runtime_val -> runtime_val -> runtime_val
  | RInl    : runtime_val -> runtime_val
  | RInr    : runtime_val -> runtime_val
  | RBorrow : loc -> runtime_val.                  (* Borrowed pointer *)

(** Runtime environment: variable -> runtime value *)
Definition env := list (var * runtime_val).

Fixpoint env_lookup (rho : env) (x : var) : option runtime_val :=
  match rho with
  | [] => None
  | (y, v) :: rho' =>
      if String.eqb x y then Some v
      else env_lookup rho' x
  end.

Definition env_extend (rho : env) (x : var) (v : runtime_val) : env :=
  (x, v) :: rho.

(** ** Memory Operations *)

Fixpoint mem_read (mu : mem) (l : loc) : option mem_cell :=
  nth_error mu l.

Fixpoint mem_write (mu : mem) (l : loc) (c : mem_cell) : mem :=
  match mu, l with
  | [], _ => []
  | _ :: mu', 0 => c :: mu'
  | h :: mu', S l' => h :: mem_write mu' l' c
  end.

Definition mem_alloc (mu : mem) (c : mem_cell) : (mem * loc) :=
  (mu ++ [c], length mu).

(** Free all cells belonging to a region *)
Fixpoint mem_free_region (mu : mem) (r : region_name) : mem :=
  match mu with
  | [] => []
  | CString r' s :: mu' =>
      if String.eqb r r' then CFree :: mem_free_region mu' r
      else CString r' s :: mem_free_region mu' r
  | c :: mu' => c :: mem_free_region mu' r
  end.

(** ** Configuration *)

(** A configuration is (memory, active regions, environment, expression) *)
Definition config := (mem * region_env * env * expr)%type.

(** ** Helper Functions *)

Definition val_to_expr (v : runtime_val) : expr :=
  match v with
  | RUnit => EUnit
  | RBool b => EBool b
  | RI32 n => EI32 n
  | RLoc l => EI32 l  (* Simplified *)
  | _ => EUnit        (* Fallback *)
  end.

Definition expr_to_val (e : expr) : runtime_val :=
  match e with
  | EUnit => RUnit
  | EBool b => RBool b
  | EI32 n => RI32 n
  | _ => RUnit
  end.

Definition loc_to_expr (l : loc) : expr := EI32 l.

(** ** Small-Step Reduction *)

Reserved Notation "c1 '-->>' c2" (at level 70).

Inductive step : config -> config -> Prop :=

  (** ===== Variables ===== *)

  | S_Var : forall mu R rho x v,
      env_lookup rho x = Some v ->
      (mu, R, rho, EVar x) -->> (mu, R, rho, val_to_expr v)

  (** ===== String Operations ===== *)

  | S_StringNew : forall mu R rho r s mu' l,
      In r R ->
      mem_alloc mu (CString r s) = (mu', l) ->
      (mu, R, rho, EStringNew r s) -->> (mu', R, rho, loc_to_expr l)

  (** String concatenation (simplified: just allocates new) *)
  | S_StringConcat : forall mu R rho l1 l2 r s1 s2 mu' l',
      mem_read mu l1 = Some (CString r s1) ->
      mem_read mu l2 = Some (CString r s2) ->
      mem_alloc (mem_write (mem_write mu l1 CFree) l2 CFree)
                (CString r (s1 ++ s2)) = (mu', l') ->
      (mu, R, rho, EStringConcat (loc_to_expr l1) (loc_to_expr l2))
        -->> (mu', R, rho, loc_to_expr l')

  (** ===== Let Binding ===== *)

  | S_Let_Step : forall mu R rho x e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, ELet x e1 e2) -->> (mu', R', rho', ELet x e1' e2)

  | S_Let_Val : forall mu R rho x v e2,
      is_value v ->
      (mu, R, rho, ELet x v e2) -->> (mu, R, env_extend rho x (expr_to_val v), e2)

  (** ===== Application ===== *)

  | S_App_Fun : forall mu R rho x T e v,
      is_value v ->
      (mu, R, rho, EApp (ELam x T e) v) -->> (mu, R, env_extend rho x (expr_to_val v), e)

  | S_App_Step1 : forall mu R rho e1 e1' e2 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EApp e1 e2) -->> (mu', R', rho', EApp e1' e2)

  | S_App_Step2 : forall mu R rho v1 e2 e2' mu' R' rho',
      is_value v1 ->
      (mu, R, rho, e2) -->> (mu', R', rho', e2') ->
      (mu, R, rho, EApp v1 e2) -->> (mu', R', rho', EApp v1 e2')

  (** ===== Conditionals ===== *)

  | S_If_True : forall mu R rho e2 e3,
      (mu, R, rho, EIf (EBool true) e2 e3) -->> (mu, R, rho, e2)

  | S_If_False : forall mu R rho e2 e3,
      (mu, R, rho, EIf (EBool false) e2 e3) -->> (mu, R, rho, e3)

  | S_If_Step : forall mu R rho e1 e1' e2 e3 mu' R' rho',
      (mu, R, rho, e1) -->> (mu', R', rho', e1') ->
      (mu, R, rho, EIf e1 e2 e3) -->> (mu', R', rho', EIf e1' e2 e3)

  (** ===== Regions ===== *)

  (** Enter region: add to active set *)
  | S_Region_Enter : forall mu R rho r e,
      ~ In r R ->
      (mu, R, rho, ERegion r e) -->> (mu, r :: R, rho, ERegion r e)

  (** Exit region when body is a value: free all region memory *)
  | S_Region_Exit : forall mu R rho r v,
      is_value v ->
      In r R ->
      (mu, r :: R, rho, ERegion r v) -->> (mem_free_region mu r, R, rho, v)

  (** Step inside region *)
  | S_Region_Step : forall mu R rho r e e' mu' R' rho',
      (mu, r :: R, rho, e) -->> (mu', R', rho', e') ->
      (mu, R, rho, ERegion r e) -->> (mu', R', rho', ERegion r e')

  (** ===== Drop ===== *)

  | S_Drop : forall mu R rho l,
      (mu, R, rho, EDrop (loc_to_expr l)) -->>
        (mem_write mu l CFree, R, rho, EUnit)

where "c1 '-->>' c2" := (step c1 c2).

(** ** Multi-Step Reduction *)

Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall c, multi_step c c
  | MS_Step : forall c1 c2 c3,
      step c1 c2 -> multi_step c2 c3 -> multi_step c1 c3.

Notation "c1 '-->*' c2" := (multi_step c1 c2) (at level 70).

(** ** Type Safety *)

(** Progress: well-typed expressions are values or can step.

    DESIGN ISSUES preventing full proof (3 categories):

    1. Missing runtime consistency premise: The theorem quantifies over
       arbitrary (mu, rho) but EVar can only step if env_lookup succeeds.
       Fix: add premise relating rho to G.

    2. Missing congruence (stepping) rules in [step] for: EPair, EFst,
       ESnd, EInl (non-value), EInr (non-value), ECase, EStringConcat
       (sub-expr stepping), EStringLen, EBorrow, EDrop (sub-expr stepping),
       ECopy.

    3. Missing canonical forms lemma: when both e1 and e2 are values in
       EApp, we need to know e1 is ELam; when e1 is a value in EIf, we
       need to know it is EBool; etc.

    These are standard fixable issues. The step relation needs ~15 more
    congruence rules, the theorem needs a runtime consistency premise,
    and a canonical forms lemma needs to be proved. *)
Theorem progress :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall mu rho,
      is_value e \/ exists mu' R' rho' e', (mu, R, rho, e) -->> (mu', R', rho', e').
Proof.
  (* Cannot be completed without the design fixes listed above.
     See the 3 categories of issues in the docstring. *)
Admitted.

(** Preservation: typing is preserved under reduction.

    DESIGN ISSUE: The conclusion [exists G'', R'; G'' |- e' : T -| G']
    quantifies over a fresh input context G'' but fixes the output
    context to G'. This is the right shape for preservation in a
    substructural system, but proving it requires:

    1. Substitution lemma: if G |- e : T and we substitute a well-typed
       value for a variable, the result is well-typed.
    2. Context weakening/strengthening lemmas.
    3. The step relation must preserve the region environment structure
       (currently S_Region_Enter changes R, which the theorem accounts
       for by using R' in the conclusion).

    These auxiliary lemmas are standard but not yet defined in this
    development. *)
Theorem preservation :
  forall R G e T G' mu rho mu' R' rho' e',
    R; G |- e : T -| G' ->
    (mu, R, rho, e) -->> (mu', R', rho', e') ->
    exists G'', R'; G'' |- e' : T -| G'.
Proof.
  (* Cannot be completed without substitution and context lemmas.
     See docstring for required auxiliary lemmas. *)
Admitted.

(** ** Memory Safety *)

(** No use-after-free: locations in reachable values are valid *)
Definition loc_valid (mu : mem) (l : loc) : Prop :=
  exists c, mem_read mu l = Some c /\ c <> CFree.

(** All locations in a value are valid *)
Fixpoint val_locs_valid (mu : mem) (v : runtime_val) : Prop :=
  match v with
  | RLoc l => loc_valid mu l
  | RBorrow l => loc_valid mu l
  | RPair v1 v2 => val_locs_valid mu v1 /\ val_locs_valid mu v2
  | RInl v' => val_locs_valid mu v'
  | RInr v' => val_locs_valid mu v'
  | _ => True
  end.

(** Memory safety: runtime environment locations remain valid after step.

    DESIGN ISSUE: This requires showing that each step rule either:
    (a) preserves the environment (rho' = rho), in which case we need
        mem_write/mem_alloc to preserve validity of existing locations; or
    (b) extends the environment (rho' = env_extend rho x v), in which
        case we need the new value v to have valid locations, AND existing
        locations must remain valid in mu'.

    Specifically needed:
    1. mem_alloc preserves existing cell validity (provable — see
       mem_alloc_preserves_read below).
    2. mem_write to location l preserves validity of locations l' <> l
       (provable).
    3. For env_extend cases (S_Let_Val, S_App_Fun), the bound value
       must have valid locations — requires canonical forms + runtime
       consistency.

    The typing derivation premise is actually not used directly;
    the proof would proceed by case analysis on the step relation. *)
Theorem memory_safety :
  forall mu R rho e T G G' mu' R' rho' e',
    R; G |- e : T -| G' ->
    (mu, R, rho, e) -->> (mu', R', rho', e') ->
    (forall x v, env_lookup rho x = Some v -> val_locs_valid mu v) ->
    (forall x v, env_lookup rho' x = Some v -> val_locs_valid mu' v).
Proof.
  (* Cannot be completed without mem_write/mem_alloc preservation
     lemmas and val_to_expr/expr_to_val round-trip properties.
     See docstring for the proof strategy. *)
Admitted.

(** ** Provable Helper Lemmas *)

(** mem_free_region removes all cells tagged with region r *)
Lemma mem_free_region_correct :
  forall mu r l s,
    mem_read (mem_free_region mu r) l = Some (CString r s) -> False.
Proof.
  intro mu. induction mu as [| c mu' IHmu']; intros r l s Hread.
  - (* mu = [] *)
    simpl in Hread. destruct l; discriminate.
  - (* mu = c :: mu' *)
    simpl in Hread. destruct c.
    + (* CString r0 s0 *)
      destruct (String.eqb r r0) eqn:Heq.
      * (* r = r0: cell replaced with CFree *)
        destruct l.
        -- simpl in Hread. discriminate.
        -- simpl in Hread. eapply IHmu'. exact Hread.
      * (* r <> r0: cell preserved *)
        destruct l.
        -- simpl in Hread. injection Hread as Hcell.
           (* CString r0 s0 = CString r s means r0 = r, contradicting Heq *)
           injection Hcell as Hr Hs.
           rewrite Hr in Heq. rewrite String.eqb_refl in Heq. discriminate.
        -- simpl in Hread. eapply IHmu'. exact Hread.
    + (* CFree *)
      destruct l.
      * simpl in Hread. discriminate.
      * simpl in Hread. eapply IHmu'. exact Hread.
Qed.

(** mem_alloc preserves reads at existing locations *)
Lemma mem_alloc_preserves_read :
  forall mu c l,
    l < length mu ->
    mem_read (fst (mem_alloc mu c)) l = mem_read mu l.
Proof.
  intros mu c l Hlt.
  unfold mem_alloc. simpl.
  (* mem_alloc appends to the end, so nth_error at l < length mu is unchanged *)
  rewrite nth_error_app1; [reflexivity | exact Hlt].
Qed.

(** Values do not step (determinism helper) *)
Lemma values_dont_step :
  forall v,
    is_value v ->
    forall mu R rho mu' R' rho' e',
      ~ ((mu, R, rho, v) -->> (mu', R', rho', e')).
Proof.
  intros v Hval. induction Hval; intros mu R rho0 mu' R' rho' e' Hstep;
    inversion Hstep.
Qed.

(** ** Additional Helper Lemmas *)

(** mem_write preserves reads at different locations *)
Lemma mem_write_preserves_read :
  forall mu l l' c,
    l <> l' ->
    l' < length mu ->
    mem_read (mem_write mu l c) l' = mem_read mu l'.
Proof.
  intro mu. induction mu as [| h mu' IHmu']; intros l l' c Hneq Hlt.
  - (* mu = [] *)
    simpl. destruct l; reflexivity.
  - (* mu = h :: mu' *)
    destruct l.
    + (* l = 0 *)
      destruct l'.
      * (* l' = 0: l = l' = 0, contradicts Hneq *)
        exfalso. apply Hneq. reflexivity.
      * (* l' = S n: reading after first cell *)
        simpl. reflexivity.
    + (* l = S l0 *)
      destruct l'.
      * (* l' = 0 *)
        simpl. reflexivity.
      * (* l' = S l'0 *)
        simpl. apply IHmu'.
        -- intro H. apply Hneq. f_equal. exact H.
        -- simpl in Hlt. apply Nat.lt_succ_r in Hlt.
           destruct (Nat.lt_ge_cases l' (length mu')) as [Hlt' | Hge].
           ++ exact Hlt'.
           ++ (* l' >= length mu' but S l' < S (length mu'), so l' < length mu' *)
              apply Nat.succ_lt_mono in Hlt. exact Hlt.
Qed.

(** ERegion expressions are never values *)
Lemma eregion_not_value : forall r e, ~ is_value (ERegion r e).
Proof.
  intros r e Hval. inversion Hval.
Qed.

(** If a value multi-steps, the config is unchanged (values don't step) *)
Lemma value_multi_step_refl :
  forall v mu R rho mu' R' rho' v',
    is_value v ->
    multi_step (mu, R, rho, v) (mu', R', rho', v') ->
    mu = mu' /\ R = R' /\ rho = rho' /\ v = v'.
Proof.
  intros v mu R rho mu' R' rho' v' Hval Hms.
  inversion Hms as [c Heq | c1 c2 c3 Hstep Hms' Heq1 Heq3].
  - (* MS_Refl *)
    inversion Heq. auto.
  - (* MS_Step: contradicts values_dont_step *)
    exfalso.
    inversion Heq1; subst.
    eapply values_dont_step; eauto.
Qed.

(** mem_free_region preserves memory length *)
Lemma mem_free_region_length :
  forall mu r, length (mem_free_region mu r) = length mu.
Proof.
  intros mu r. induction mu as [| c mu' IH].
  - reflexivity.
  - simpl. destruct c.
    + destruct (String.eqb r r0); simpl; f_equal; exact IH.
    + simpl. f_equal. exact IH.
Qed.

(** ** No Leaks (for region-scoped allocations) *)

(** DESIGN ISSUE: The no_leaks theorem as stated requires that when
    ERegion r e multi-steps to a value v, the final memory has no
    CString r cells. This would follow from S_Region_Exit calling
    mem_free_region. However, the theorem statement constrains the
    final config to have region env R (same as initial), but
    S_Region_Enter pushes r onto R, and S_Region_Exit pops it.
    The multi-step trace goes:

      (mu, R, rho, ERegion r e)
        -->> (mu, r::R, rho, ERegion r e)   [S_Region_Enter]
        -->>* ...                             [S_Region_Step]
        -->> (mu'', R, rho, v)                [S_Region_Exit]

    The S_Region_Exit step applies mem_free_region, which by
    mem_free_region_correct above, eliminates all CString r cells.

    However, proving this requires careful inversion on the multi-step
    trace and the fact that S_Region_Exit is the LAST step (since v
    is a value). The key lemma mem_free_region_correct IS proved above.

    The main remaining difficulty is inverting the multi_step relation
    to extract the final S_Region_Exit step. This requires showing
    that ERegion r v with v a value and r in R can ONLY step via
    S_Region_Exit, which IS provable but requires tedious inversion. *)
Theorem no_leaks :
  forall mu R rho r e T G G' v mu',
    R; G |- ERegion r e : T -| G' ->
    (mu, R, rho, ERegion r e) -->* (mu', R, rho, v) ->
    is_value v ->
    (* All memory allocated in region r is freed *)
    (forall l s, mem_read mu' l = Some (CString r s) -> False).
Proof.
  (* The core lemma mem_free_region_correct (proved above) establishes
     that mem_free_region eliminates all region-tagged cells.

     PROOF STRATEGY (verified sound, not yet mechanized):
     1. ERegion r e is not a value (eregion_not_value), so
        multi_step is not MS_Refl.
     2. The first step must be S_Region_Enter (pushing r onto R).
     3. Subsequent steps maintain ERegion r wrapper via S_Region_Step.
     4. The only rule that removes ERegion is S_Region_Exit, which
        calls mem_free_region and produces a value v.
     5. By value_multi_step_refl, no further steps occur after
        S_Region_Exit.
     6. By mem_free_region_correct, the final memory has no
        CString r cells.

     REMAINING BLOCKER: Formalizing step 3 requires an invariant
     that the expression remains ERegion-wrapped throughout the
     trace until S_Region_Exit fires. This invariant is true but
     requires careful step inversion on every rule.

     DESIGN ISSUE: S_Region_Step has a subtle mismatch between
     inner and outer region environments. The rule pushes r onto
     R in the inner step premise, but when the outer config already
     has r in R (after S_Region_Enter), this double-pushes r.
     Consider revising to:
       S_Region_Step : (mu, R, rho, e) -->> (mu', R', rho', e')
         -> In r R
         -> (mu, R, rho, ERegion r e) -->> (mu', R', rho', ERegion r e')
     This would make the step relation consistent but changes the
     semantics. Deferred to a dedicated semantics revision. *)
Admitted.
