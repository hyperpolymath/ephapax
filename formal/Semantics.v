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

(** Progress: well-typed expressions are values or can step *)
Theorem progress :
  forall R G e T G',
    R; G |- e : T -| G' ->
    forall mu rho,
      is_value e \/ exists mu' R' rho' e', (mu, R, rho, e) -->> (mu', R', rho', e').
Proof.
  (* Proof by induction on typing derivation *)
Admitted.

(** Preservation: typing is preserved under reduction *)
Theorem preservation :
  forall R G e T G' mu rho mu' R' rho' e',
    R; G |- e : T -| G' ->
    (mu, R, rho, e) -->> (mu', R', rho', e') ->
    exists G'', R'; G'' |- e' : T -| G'.
Proof.
  (* Proof by induction on step derivation *)
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

Theorem memory_safety :
  forall mu R rho e T G G' mu' R' rho' e',
    R; G |- e : T -| G' ->
    (mu, R, rho, e) -->> (mu', R', rho', e') ->
    (forall x v, env_lookup rho x = Some v -> val_locs_valid mu v) ->
    (forall x v, env_lookup rho' x = Some v -> val_locs_valid mu' v).
Proof.
  (* Memory safety follows from linear typing *)
Admitted.

(** ** No Leaks (for region-scoped allocations) *)

Theorem no_leaks :
  forall mu R rho r e T G G' v mu',
    R; G |- ERegion r e : T -| G' ->
    (mu, R, rho, ERegion r e) -->* (mu', R, rho, v) ->
    is_value v ->
    (* All memory allocated in region r is freed *)
    (forall l s, mem_read mu' l = Some (CString r s) -> False).
Proof.
  (* Region exit frees all region-tagged memory *)
Admitted.
