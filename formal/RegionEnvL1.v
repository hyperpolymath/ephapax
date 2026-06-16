(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * L1 region environment as a count-map (the tropical re-foundation, stage 1)

    This file forks an L1-only region-environment carrier away from the
    first-occurrence list (`region_env := list region_name` in [Syntax.v]),
    which the legacy judgment keeps. The list's [remove_first_L1] pops a
    *specific list occurrence*, so the L1 region-shrink admit needs
    list-structure agreement that no multiset transport provides
    (see the design note in [Semantics_L1.v] and
    [formal/L1-REGION-REFOUNDATION-PLAN.md]). The fix is to remove the
    first-occurrence dependence: a region environment is a **count-map**
    [region_name -> nat] (re-entry depth per region; 0 = dead), reasoned
    up to a **pointwise-equality setoid** [renv_eq].

    Axiom budget: this file is axiom-free. We use a setoid relation
    ([renv_eq]) rather than [functional_extensionality], so [Print
    Assumptions] stays clean — order-insensitivity is *definitional*
    (the carrier is a function; permutation collapses to [renv_eq]),
    and [funext] is never invoked.

    The keystone is [enter_exit_id]: [cntL1 r R >= 1 -> renv_eq (enterL1 r
    (exitL1 r R)) R]. It dissolves the [cnt r R = 1] corner of the
    region-shrink admit (re-entering the freshly-exited region returns to
    the very same environment, up to [renv_eq]) — the exact step the list
    carrier could only achieve up to permutation. *)

Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

From Ephapax Require Import Syntax.  (* region_name := string *)

(** ** Carrier *)

(** A region environment maps each region to its re-entry depth.
    [R r = 0] means [r] is dead (not live); [R r = k] means [r] has been
    entered [k] times net. Total function — finitely supported in practice
    but we never enumerate it, so no finite-support proof obligation. *)
Definition region_env_l1 := region_name -> nat.

(** ** Setoid equivalence: pointwise [nat] equality.

    Two environments are equivalent iff they assign the same depth to every
    region. This is the axiom-free stand-in for function equality: we never
    need [R1 = R2] (which would want [funext]); [renv_eq R1 R2] suffices and
    is provable by [nat] reasoning at each coordinate. *)
Definition renv_eq (R1 R2 : region_env_l1) : Prop :=
  forall r, R1 r = R2 r.

Infix "=R=" := renv_eq (at level 70, no associativity).

#[global] Instance renv_eq_Equivalence : Equivalence renv_eq.
Proof.
  constructor.
  - intros R r; reflexivity.
  - intros R1 R2 H r; symmetry; apply H.
  - intros R1 R2 R3 H12 H23 r; rewrite H12; apply H23.
Qed.

(** ** Operations *)

(** Count / depth of region [r]. *)
Definition cntL1 (r : region_name) (R : region_env_l1) : nat := R r.

(** [r] is live iff its depth is at least one. *)
Definition liveL1 (R : region_env_l1) (r : region_name) : Prop := R r >= 1.

(** Enter (push) region [r]: increment its depth. *)
Definition enterL1 (r : region_name) (R : region_env_l1) : region_env_l1 :=
  fun r' => if String.eqb r' r then S (R r') else R r'.

(** Exit (pop) region [r]: decrement its depth (saturating at 0). *)
Definition exitL1 (r : region_name) (R : region_env_l1) : region_env_l1 :=
  fun r' => if String.eqb r' r then pred (R r') else R r'.

(** The empty environment: every region dead. *)
Definition emptyL1 : region_env_l1 := fun _ => 0.

(** ** Coordinate lemmas — pointwise [nat] facts.

    Each is a one-liner: [unfold], case on [String.eqb], [lia]. These
    replace the list lemmas [remove_first_comm], [count_occ_le_l1_m],
    [remove_first_L1_count_eq_self], [remove_first_L1_count_other]. *)

Lemma eqb_refl_true : forall r : region_name, String.eqb r r = true.
Proof. intro r. apply String.eqb_eq. reflexivity. Qed.

Lemma cnt_enter_self : forall r R, cntL1 r (enterL1 r R) = S (cntL1 r R).
Proof. intros r R. unfold cntL1, enterL1. rewrite eqb_refl_true. reflexivity. Qed.

Lemma cnt_enter_other : forall r r' R, r <> r' -> cntL1 r' (enterL1 r R) = cntL1 r' R.
Proof.
  intros r r' R Hne. unfold cntL1, enterL1.
  destruct (String.eqb r' r) eqn:E; [|reflexivity].
  apply String.eqb_eq in E. subst. contradiction Hne; reflexivity.
Qed.

Lemma cnt_exit_self : forall r R, cntL1 r (exitL1 r R) = pred (cntL1 r R).
Proof. intros r R. unfold cntL1, exitL1. rewrite eqb_refl_true. reflexivity. Qed.

Lemma cnt_exit_other : forall r r' R, r <> r' -> cntL1 r' (exitL1 r R) = cntL1 r' R.
Proof.
  intros r r' R Hne. unfold cntL1, exitL1.
  destruct (String.eqb r' r) eqn:E; [|reflexivity].
  apply String.eqb_eq in E. subst. contradiction Hne; reflexivity.
Qed.

(** Grade monotonicity: an exit never increases any region's depth. *)
Lemma cnt_le_exit : forall r r' R, cntL1 r' (exitL1 r R) <= cntL1 r' R.
Proof.
  intros r r' R. unfold cntL1, exitL1.
  destruct (String.eqb r' r) eqn:E; lia.
Qed.

(** Exits commute (order-free by construction — the whole point). *)
Lemma exit_comm : forall r1 r2 R, exitL1 r1 (exitL1 r2 R) =R= exitL1 r2 (exitL1 r1 R).
Proof.
  intros r1 r2 R r. unfold exitL1.
  destruct (String.eqb r r1) eqn:E1; destruct (String.eqb r r2) eqn:E2; reflexivity.
Qed.

(** Enters commute. *)
Lemma enter_comm : forall r1 r2 R, enterL1 r1 (enterL1 r2 R) =R= enterL1 r2 (enterL1 r1 R).
Proof.
  intros r1 r2 R r. unfold enterL1.
  destruct (String.eqb r r1) eqn:E1; destruct (String.eqb r r2) eqn:E2; reflexivity.
Qed.

(** Exit then enter the same region is the identity (always). *)
Lemma exit_enter_id : forall r R, exitL1 r (enterL1 r R) =R= R.
Proof.
  intros r R r'. unfold exitL1, enterL1.
  destruct (String.eqb r' r) eqn:E.
  - simpl. reflexivity.
  - reflexivity.
Qed.

(** ** KEYSTONE — enter then exit the same *live* region is the identity.

    This is the lemma the list carrier could only reach up to permutation.
    With the count-map and [renv_eq] it is a one-line [nat] fact, and it
    closes the [cnt r R = 1] corner of the region-shrink admit:
    re-entering the region you just exited returns you to the *same*
    environment (up to [renv_eq]), not merely a permuted one. *)
Lemma enter_exit_id : forall r R, cntL1 r R >= 1 -> enterL1 r (exitL1 r R) =R= R.
Proof.
  intros r R Hlive r'. unfold cntL1 in Hlive. unfold enterL1, exitL1.
  destruct (String.eqb r' r) eqn:E.
  - apply String.eqb_eq in E. subst r'. lia.
  - reflexivity.
Qed.

(** ** Liveness facts *)

Lemma live_iff_cnt : forall R r, liveL1 R r <-> cntL1 r R >= 1.
Proof. intros R r. unfold liveL1, cntL1. reflexivity. Qed.

Lemma live_exit_other : forall r r' R, r <> r' -> liveL1 R r' -> liveL1 (exitL1 r R) r'.
Proof.
  intros r r' R Hne Hlive. unfold liveL1 in *. unfold exitL1.
  destruct (String.eqb r' r) eqn:E.
  - apply String.eqb_eq in E. subst r'. contradiction Hne; reflexivity.
  - exact Hlive.
Qed.

Lemma not_live_empty : forall r, ~ liveL1 emptyL1 r.
Proof. intros r H. unfold liveL1, emptyL1 in H. lia. Qed.

(** ** Setoid morphisms — operations respect [renv_eq].

    These [Proper] instances let [rewrite] replace an environment by a
    [renv_eq]-equivalent one underneath the operations, which is how the
    judgment-level [Proper] instance (stage 2) will be built. *)

#[global] Instance enterL1_Proper :
  Proper (eq ==> renv_eq ==> renv_eq) enterL1.
Proof.
  intros r r' <- R1 R2 H r0. unfold enterL1.
  destruct (String.eqb r0 r) eqn:E; rewrite H; reflexivity.
Qed.

#[global] Instance exitL1_Proper :
  Proper (eq ==> renv_eq ==> renv_eq) exitL1.
Proof.
  intros r r' <- R1 R2 H r0. unfold exitL1.
  destruct (String.eqb r0 r) eqn:E; rewrite H; reflexivity.
Qed.

#[global] Instance cntL1_Proper :
  Proper (eq ==> renv_eq ==> eq) cntL1.
Proof. intros r r' <- R1 R2 H. unfold cntL1. apply H. Qed.

#[global] Instance liveL1_Proper :
  Proper (renv_eq ==> eq ==> iff) liveL1.
Proof.
  intros R1 R2 H r r' <-. unfold liveL1. rewrite H. reflexivity.
Qed.
