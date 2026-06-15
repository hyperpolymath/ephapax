(* SPDX-License-Identifier: MPL-2.0 *)
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell *)

(** * Ephapax: A Linear Type System for Safe Memory Management

    Formal semantics in Coq using De Bruijn indices.

    Core principle: ephapax (once for all)
    Every linear resource must be used exactly once.

    De Bruijn indices eliminate variable shadowing, making
    typing_preserves_domain provable without name complications.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

(** ** Variables and Names *)

(** Variables use De Bruijn indices — natural numbers indexing into
    the typing context. Index 0 is the most recently bound variable. *)
Definition var := nat.

(** Region names remain strings (they are not bound in the context). *)
Definition region_name := string.

(** ** Linearity Annotations *)

Inductive linearity : Type :=
  | Lin    (* Linear: must use exactly once *)
  | Unr.   (* Unrestricted: may use any number of times *)

(** ** Base Types *)

Inductive base_ty : Type :=
  | TUnit
  | TBool
  | TI32
  | TI64
  | TF32
  | TF64.

(** ** Types with Region Annotations *)

Inductive ty : Type :=
  | TBase   : base_ty -> ty
  | TString : region_name -> ty
  | TRef    : linearity -> ty -> ty
  | TFun    : ty -> ty -> ty
  | TProd   : ty -> ty -> ty
  | TSum    : ty -> ty -> ty
  | TRegion : region_name -> ty -> ty
  | TBorrow : ty -> ty
  (** L3 — Echo / residue type former. [TEcho T] is the type of an
      echo value witnessing an irreversible step that erased a value
      of type [T]. Emitted by [S_Region_Exit] (collapse
      [LiveAt_r → ExitedAt_r]) and [S_Drop] (collapse [T → ⊤]).
      Observation discipline is modality-dispatched at the typing-
      rule boundary, not encoded in the type — see
      [formal/PRESERVATION-DESIGN.md §6.3] and [formal/Echo.v]. *)
  | TEcho   : ty -> ty

  (** L2 Phase 2 / Phase D slice 1 — Effect-typed function former.
      [TFunEff T1 T2 R_in R_out] is the type of a function from [T1]
      to [T2] whose body requires the region environment [R_in] on
      entry and produces [R_out] on exit. The legacy [TFun T1 T2] is
      preserved (per CLAUDE.md owner directive 2026-05-27 — its
      falsity in conjunction with `preservation` is load-bearing for
      `Counterexample.v`); new code uses [TFunEff] to expose lambda
      bodies' R-flow at the type level.

      Closes the structural-blocker root cause: at function-call
      sites, the body's region requirements become visible to
      preservation reasoning, unblocking the lambda-rigidity admit
      at `Semantics_L1.v:1694` and naturally enabling
      body-input-shrinkage for the Phase C list-vs-multiset bridge.

      Slice 1 (this PR): syntax-only landing. Typing rules
      (`T_Lam_L1_*_Eff` + `T_App_L1_Eff`) ship in slice 2. Per the
      L3 wiring playbook (slices 1→4) this is the lightest landable
      shape. *)
  | TFunEff : ty -> ty -> list region_name -> list region_name -> ty.

(** ** Expressions *)

Inductive expr : Type :=
  (* Values *)
  | EUnit   : expr
  | EBool   : bool -> expr
  | EI32    : nat -> expr
  | EVar    : var -> expr                            (* De Bruijn index *)

  (* String operations *)
  | EStringNew    : region_name -> string -> expr
  | EStringConcat : expr -> expr -> expr
  | EStringLen    : expr -> expr

  (* Control flow — binders use index 0 for the bound variable *)
  | ELet    : expr -> expr -> expr                   (* let = e1 in e2 *)
  | ELetLin : expr -> expr -> expr                   (* let! = e1 in e2 *)
  | EIf     : expr -> expr -> expr -> expr

  (* Functions *)
  | ELam    : ty -> expr -> expr                     (* fn(:T) -> e *)
  | EApp    : expr -> expr -> expr

  (* Products *)
  | EPair   : expr -> expr -> expr
  | EFst    : expr -> expr
  | ESnd    : expr -> expr

  (* Sums *)
  | EInl    : ty -> expr -> expr
  | EInr    : ty -> expr -> expr
  | ECase   : expr -> expr -> expr -> expr           (* case e of inl -> e1 | inr -> e2 *)

  (* Regions *)
  | ERegion : region_name -> expr -> expr

  (* Borrowing *)
  | EBorrow : expr -> expr
  | EDeref  : expr -> expr

  (* Explicit resource management *)
  | EDrop   : expr -> expr
  | ECopy   : expr -> expr

  (* Runtime-only values *)
  | ELoc    : nat -> region_name -> expr

  (** L3 — Echo / residue runtime value. [EEcho T v] is the residue
      emitted when an irreversible step (region exit, drop) erased a
      witness [v] of type [T]. Runtime-only: not directly writable in
      surface syntax, like [ELoc]. Observation discipline is
      modality-dispatched at the typing-rule boundary — see
      [formal/PRESERVATION-DESIGN.md §6.3] and [formal/Echo.v]. *)
  | EEcho   : ty -> expr -> expr

  (** L3 — Echo observation. [EObserve e] consumes an echo value
      (whose type is [TEcho T] for some [T]) and discharges the
      observation obligation, returning [TBase TUnit]. Surface-
      writable. Under Linear discipline this consumption is
      mandatory; under Affine discipline it is optional (the echo
      may be implicitly lowered). The modality dispatch lives in
      the typing rules, not in the [expr] constructor. *)
  | EObserve : expr -> expr.

(** ** Values *)

Inductive is_value : expr -> Prop :=
  | VUnit   : is_value EUnit
  | VBool   : forall b, is_value (EBool b)
  | VI32    : forall n, is_value (EI32 n)
  | VLam    : forall T e, is_value (ELam T e)
  | VPair   : forall v1 v2, is_value v1 -> is_value v2 -> is_value (EPair v1 v2)
  | VInl    : forall T v, is_value v -> is_value (EInl T v)
  | VInr    : forall T v, is_value v -> is_value (EInr T v)
  | VLoc    : forall l r, is_value (ELoc l r)
  (** EBorrow v is a value when v is a value — a borrow reference is
      a first-class value of type TBorrow T. This is needed for:
      (a) preservation of T_Borrow_Val: substitution produces EBorrow v,
          which must be a value so reduction halts at the reference form,
          not at v (which would change type from TBorrow T to T).
      (b) values_dont_step: EBorrow v doesn't reduce further once v is
          a value — the reference IS the normal form. *)
  | VBorrow : forall v, is_value v -> is_value (EBorrow v)
  (** L3 — Echo residue values. An echo of a value [v] is itself a
      value (awaiting observation by [T_Observe] or implicit
      lowering). Required so that [S_Region_Exit] and [S_Drop] can
      reduce to a normal form rather than getting stuck. *)
  | VEcho   : forall T v, is_value v -> is_value (EEcho T v).

(** ** Syntactic Region-Closure

    [expr_free_of_region r e] holds when [e] has no syntactic reference
    to region [r] — no [EStringNew r _], no [ELoc _ r], and no sub-expression
    that does. Used by [S_Region_Exit] to ensure that a value leaving a
    region scope cannot later demand that region to be active (e.g., a
    lambda body that would need [r] at application time).

    [ERegion r' e] shadows the name [r] inside [e] when [r = r'], so such
    a sub-term is trivially region-free in the outer sense. Shadowing is
    handled by short-circuiting the recursion in that case. *)

Fixpoint expr_free_of_region (r : region_name) (e : expr) : Prop :=
  match e with
  | EUnit | EBool _ | EI32 _ | EVar _ => True
  | EStringNew r' _ => r <> r'
  | EStringConcat e1 e2 | ELet e1 e2 | ELetLin e1 e2
  | EApp e1 e2 | EPair e1 e2 =>
      expr_free_of_region r e1 /\ expr_free_of_region r e2
  | EStringLen e' | EFst e' | ESnd e' | EInl _ e' | EInr _ e'
  | EBorrow e' | EDeref e' | EDrop e' | ECopy e' | ELam _ e' =>
      expr_free_of_region r e'
  | EIf e1 e2 e3 | ECase e1 e2 e3 =>
      expr_free_of_region r e1 /\ expr_free_of_region r e2
      /\ expr_free_of_region r e3
  | ERegion r' e' =>
      if String.eqb r r' then True
      else expr_free_of_region r e'
  | ELoc _ r' => r <> r'
  (** L3 — Echo carries its witness; region-freedom propagates into
      the witness sub-expression. The witness type annotation [T] is
      closed (no free region names beyond what [v] itself contains). *)
  | EEcho _ e' => expr_free_of_region r e'
  | EObserve e' => expr_free_of_region r e'
  end.

(** ** Strict Region-Freedom (reformulation, closes blocker 5)

    [expr_strictly_free_of_region r e] mirrors [expr_free_of_region]
    EXCEPT in the [ERegion r' body] case, where it recurses
    UNCONDITIONALLY (no shadow short-circuit on [r = r']).

    Why a strict variant exists. The weak [expr_free_of_region]
    short-circuits to [True] when [ERegion r' body] shadows [r]
    (the [String.eqb r r'] guard). That weakness is sound for the
    plain capability-list reading of [R], where a nested
    [ERegion r ...] statically masks the outer [r] and the body
    cannot "reach back." But under the L1 [T_Region_Active_L1]
    judgment — and more sharply under L3 re-entry semantics —
    a body can witness the outer [r] through count-monotonicity /
    multiset accounting that the syntactic shadow does NOT
    discharge. The audit (task #29, 2026-05-28, blocker 5) traced
    one class of "predicate too weak" failures in the region-
    shrinkage lemma family to exactly this short-circuit accepting
    expressions whose body legitimately references the outer [r].

    The strict variant is the conservative reading: an expression
    is strictly free of [r] iff [r] never appears anywhere inside,
    even under a same-named [ERegion r ...] shadow. It implies the
    weak variant (see [expr_strictly_free_implies_free] below).

    Scope. The strict predicate is intended to replace the weak one
    in the L1 region-shrinkage lemma family
    ([region_shrink_preserves_typing_l1_gen_m] and friends in
    [Semantics_L1.v]) and downstream consumers
    ([preservation_l3_region_active_echo]). The legacy step rules
    [S_Region_Exit] / [S_Region_Exit_Echo] in [Semantics.v] still
    emit the weak [expr_free_of_region] premise; migrating those
    is a separate concern (legacy operational semantics) and may
    or may not happen in this PR (see PR description for current
    scope).

    Note. The L1 shadowed-sub-case [admit] at
    [Semantics_L1.v:553/621] is blocked by a list-vs-multiset
    structural mismatch (Phase D work), NOT by predicate weakness.
    Strengthening to [expr_strictly_free_of_region] does NOT close
    those admits. *)

Fixpoint expr_strictly_free_of_region (r : region_name) (e : expr) : Prop :=
  match e with
  | EUnit | EBool _ | EI32 _ | EVar _ => True
  | EStringNew r' _ => r <> r'
  | EStringConcat e1 e2 | ELet e1 e2 | ELetLin e1 e2
  | EApp e1 e2 | EPair e1 e2 =>
      expr_strictly_free_of_region r e1 /\ expr_strictly_free_of_region r e2
  | EStringLen e' | EFst e' | ESnd e' | EInl _ e' | EInr _ e'
  | EBorrow e' | EDeref e' | EDrop e' | ECopy e' | ELam _ e' =>
      expr_strictly_free_of_region r e'
  | EIf e1 e2 e3 | ECase e1 e2 e3 =>
      expr_strictly_free_of_region r e1 /\ expr_strictly_free_of_region r e2
      /\ expr_strictly_free_of_region r e3
  (** The strictness difference: no [String.eqb] shadow short-circuit.
      Always descend into the body. *)
  | ERegion _ e' => expr_strictly_free_of_region r e'
  | ELoc _ r' => r <> r'
  | EEcho _ e' => expr_strictly_free_of_region r e'
  | EObserve e' => expr_strictly_free_of_region r e'
  end.

(** [expr_strictly_free_of_region] strictly strengthens
    [expr_free_of_region]: every strictly-free expression is also
    weakly-free. The converse fails on (e.g.)
    [ERegion r (EStringNew r _)] where the weak variant accepts
    via shadow short-circuit but the strict variant rejects.

    Proof. Structural induction. The only non-trivial case is
    [ERegion r' body]: the weak version short-circuits to [True]
    when [r = r'], which is implied by anything; the strict
    version's recursive hypothesis discharges the weak version's
    recursive case when [r <> r']. *)
Lemma expr_strictly_free_implies_free :
  forall r e, expr_strictly_free_of_region r e -> expr_free_of_region r e.
Proof.
  intros r e. induction e; simpl; intros H; try exact I; try assumption;
    try (apply IHe; exact H);
    try (destruct H as [H1 H2]; split; [apply IHe1 | apply IHe2]; assumption);
    try (destruct H as [H1 [H2 H3]]; split;
         [apply IHe1; assumption | split; [apply IHe2 | apply IHe3]; assumption]).
  - (* ERegion r' e *)
    destruct (String.eqb r r0) eqn:Heq.
    + exact I.
    + apply IHe; exact H.
Qed.

(** ** Typing Contexts (De Bruijn) *)

(** A typing context is a list of (type, used?) pairs.
    Position in the list IS the variable index.
    Index 0 = head of list = most recently bound. *)

Definition ctx := list (ty * bool).

(** Context lookup by De Bruijn index. *)
Definition ctx_lookup (G : ctx) (i : var) : option (ty * bool) :=
  nth_error G i.

(** Projected lookups — avoid option (ty * bool) discrimination in Rocq 9.1.1. *)
Definition ctx_lookup_ty (G : ctx) (i : var) : option ty :=
  match nth_error G i with
  | Some (T, _) => Some T
  | None => None
  end.

Definition ctx_lookup_flag (G : ctx) (i : var) : option bool :=
  match nth_error G i with
  | Some (_, u) => Some u
  | None => None
  end.

(** Mark variable at index i as used. *)
Fixpoint ctx_mark_used (G : ctx) (i : var) : ctx :=
  match G, i with
  | [], _ => []
  | (T, _) :: G', 0 => (T, true) :: G'
  | entry :: G', S i' => entry :: ctx_mark_used G' i'
  end.

(** Extend context with a new binding (prepend — index 0). *)
Definition ctx_extend (G : ctx) (T : ty) : ctx :=
  (T, false) :: G.

(** ===== Projected lookup lemmas ===== *)

(** Bridging: whole lookup splits into projected lookups. *)
Lemma ctx_lookup_split :
  forall G i T u,
    ctx_lookup G i = Some (T, u) ->
    ctx_lookup_ty G i = Some T /\ ctx_lookup_flag G i = Some u.
Proof.
  unfold ctx_lookup, ctx_lookup_ty, ctx_lookup_flag.
  intros G i T u H. rewrite H. auto.
Qed.

(** Bridging: projected lookups combine into whole lookup. *)
Lemma ctx_lookup_combine :
  forall G i T u,
    ctx_lookup_ty G i = Some T ->
    ctx_lookup_flag G i = Some u ->
    ctx_lookup G i = Some (T, u).
Proof.
  unfold ctx_lookup, ctx_lookup_ty, ctx_lookup_flag.
  intros G i T u Ht Hu.
  destruct (nth_error G i) as [[T' u']|] eqn:E.
  - inversion Ht. inversion Hu. subst. reflexivity.
  - discriminate.
Qed.

(** Projected cons lemmas *)
Lemma ctx_lookup_flag_zero :
  forall T u G, ctx_lookup_flag ((T, u) :: G) 0 = Some u.
Proof. reflexivity. Qed.

Lemma ctx_lookup_flag_succ :
  forall entry G i, ctx_lookup_flag (entry :: G) (S i) = ctx_lookup_flag G i.
Proof. reflexivity. Qed.

Lemma ctx_lookup_ty_zero :
  forall T u G, ctx_lookup_ty ((T, u) :: G) 0 = Some T.
Proof. reflexivity. Qed.

Lemma ctx_lookup_ty_succ :
  forall entry G i, ctx_lookup_ty (entry :: G) (S i) = ctx_lookup_ty G i.
Proof. reflexivity. Qed.

(** Flag contradiction — avoids option (ty * bool) discrimination *)
Lemma flag_true_not_false :
  forall G i,
    ctx_lookup_flag G i = Some true ->
    ctx_lookup_flag G i = Some false -> False.
Proof. intros G i Ht Hf. rewrite Ht in Hf. discriminate. Qed.

(** ctx_mark_used sets flag to true at position i *)
Lemma ctx_mark_used_flag_at :
  forall G i,
    ctx_lookup_flag G i <> None ->
    ctx_lookup_flag (ctx_mark_used G i) i = Some true.
Proof.
  induction G as [|[T0 u0] G' IH]; intros i Hlk.
  - simpl in Hlk. destruct i; exfalso; apply Hlk; reflexivity.
  - destruct i.
    + reflexivity.
    + simpl. apply IH. simpl in Hlk. exact Hlk.
Qed.

(** ctx_mark_used preserves flag at other positions *)
Lemma ctx_mark_used_flag_other :
  forall G i j,
    i <> j ->
    ctx_lookup_flag (ctx_mark_used G i) j = ctx_lookup_flag G j.
Proof.
  induction G as [|[T0 u0] G' IH]; intros i j Hne.
  - simpl. destruct i; destruct j; reflexivity.
  - destruct i; destruct j; simpl.
    + exfalso. apply Hne. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro H. apply Hne. f_equal. exact H.
Qed.

(** ctx_mark_used preserves type at other positions *)
Lemma ctx_mark_used_ty_other :
  forall G i j,
    i <> j ->
    ctx_lookup_ty (ctx_mark_used G i) j = ctx_lookup_ty G j.
Proof.
  induction G as [|[T0 u0] G' IH]; intros i j Hne.
  - simpl. destruct i; destruct j; reflexivity.
  - destruct i; destruct j; simpl.
    + exfalso. apply Hne. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro H. apply Hne. f_equal. exact H.
Qed.

(** [ctx_mark_used] commutes with context append when the marked
    position lies within the head. Required by Phase 3b Stage 1b's
    body-transfer lemma for the [T_Var_Lin_L1] case (the only typing
    rule that changes G's flags). *)
Lemma ctx_mark_used_app_lt :
  forall (G_head G_tail : ctx) (i : nat),
    i < List.length G_head ->
    ctx_mark_used (G_head ++ G_tail) i = ctx_mark_used G_head i ++ G_tail.
Proof.
  induction G_head as [|[T0 u0] G_head' IH]; intros G_tail i Hlt; simpl in *.
  - lia.
  - destruct i.
    + reflexivity.
    + simpl. f_equal. apply IH. lia.
Qed.

(** flags_only_increase via projection: if flag is false in output, it was false in input *)
(** Direct contradiction for the T_Let/T_LetLin/T_Case idx=0 case.
    Uses functional extraction to avoid option-pair discrimination. *)
Lemma ctx_lookup_cons_zero_flag_contra :
  forall (T1 : ty) (G'' : ctx) (T0 : ty),
    ctx_lookup ((T1, true) :: G'') 0 = Some (T0, false) -> False.
Proof.
  unfold ctx_lookup. simpl. intros T1 G'' T0 H.
  apply (f_equal (fun x => match x with Some (_, b) => b | None => true end)) in H.
  simpl in H. discriminate H.
Qed.

Lemma flags_only_increase_proj :
  forall (G G' : ctx) (i : var),
    List.length G = List.length G' ->
    (forall j, ctx_lookup_flag G' j = Some false -> ctx_lookup_flag G j = Some false) ->
    ctx_lookup_flag G' i = Some false ->
    ctx_lookup_flag G i = Some false.
Proof. intros. auto. Qed.

(** Check if a type is linear *)
Fixpoint is_linear_ty (T : ty) : bool :=
  match T with
  | TString _ => true
  | TRef Lin _ => true
  | TRegion _ T' => is_linear_ty T'
  | _ => false
  end.

(** Check if a type is a ground non-linear base type — [TUnit], [TBool],
    or [TI32]. Values at these types are R-irrelevant: their typing
    derivations (via [T_Unit_L1] / [T_Bool_L1] / [T_I32_L1]) are
    polymorphic in the region environment, so a retype across any
    [R → R'] is constructively trivial.

    Introduced for [Semantics_L1.ground_nonlinear_retype_l1_m] and the
    Phase D slice 4 non-linear substitution-lemma generalisation
    (formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md Phase 1). *)
Definition is_ground_nonlinear_ty (T : ty) : bool :=
  match T with
  | TBase TUnit => true
  | TBase TBool => true
  | TBase TI32  => true
  | _ => false
  end.

(** Check if a type is an effect-typed function type [TFunEff _ _ _ _].
    Values at these types are TFunEff lambdas whose body is typed at a
    fixed [R_in] (independent of the formation env [R]); a retype across
    [R -> R'] is conditionally valid under the side condition
    [forall r, In r R' -> In r R_in] (the same side condition the
    [T_Lam_L1_*_Eff] formation rules require).

    Introduced for [Semantics_L1.tfuneff_lambda_retype_l1_m] and the
    Phase D slice 4 non-linear substitution-lemma generalisation
    (formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md Phase 3). *)
Definition is_tfuneff_ty (T : ty) : bool :=
  match T with
  | TFunEff _ _ _ _ => true
  | _ => false
  end.

(** Syntactic over-approximation of region names introduced via
    [ERegion] subterms of an expression. Used by Phase 3b's TFunEff
    substitution lemma to discharge the [r ∈ R_in_v] obligation
    that arises in [T_Region_L1] cases — when the substituee body
    introduces a region [r], retyping a TFunEff value at the extended
    [r :: R] requires [r ∈ R_in_v] (the lambda's declared input env).

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 3b option (a)
    and ephapax issue #225. *)
Fixpoint regions_introduced_by (e : expr) : list region_name :=
  match e with
  | EUnit | EBool _ | EI32 _ | EVar _
  | EStringNew _ _ | ELoc _ _ => nil
  | EStringConcat e1 e2 | ELet e1 e2 | ELetLin e1 e2
  | EApp e1 e2 | EPair e1 e2 =>
      regions_introduced_by e1 ++ regions_introduced_by e2
  | EStringLen e' | EFst e' | ESnd e'
  | EBorrow e' | EDeref e' | EDrop e' | ECopy e' | EObserve e' =>
      regions_introduced_by e'
  | ELam _ e' | EInl _ e' | EInr _ e' | EEcho _ e' =>
      regions_introduced_by e'
  | EIf e1 e2 e3 | ECase e1 e2 e3 =>
      regions_introduced_by e1
      ++ regions_introduced_by e2
      ++ regions_introduced_by e3
  | ERegion r e' => r :: regions_introduced_by e'
  end.

(** Syntactic predicate: the expression contains no [ELam] subterm.

    Used by Phase D slice 4 Phase 3b Stage 1's substitution lemma
    [subst_typing_gen_l1_m_tfuneff] to exfalso-eliminate the inner
    [T_Lam_L1_Linear_Eff] / [T_Lam_L1_Affine_Eff] cases. The principle
    is "leaf-only": Stage 1's lemma only fires when the substituee
    body has no inner lambdas, so the conditional [R_in_inner ⊆ R_in_v]
    obligation that Stage 3 (CPS) and Stage 2 (annotated ELam) address
    cannot arise.

    A [TFunEff] lambda is, in the current AST, indistinguishable from
    a [TFun] lambda at the [ELam] node (the type annotation slot carries
    only the parameter type, not the function type). Hence the predicate
    is conservatively false on EVERY [ELam], not only TFunEff-typed
    ones. Stage 2 (#240) reshapes [ELam] to carry [R_in] / [R_out] and
    refines this predicate to TFunEff-specific.

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 3b Stage 1
    and ephapax issue #239. *)
Fixpoint tfuneff_lambda_free (e : expr) : bool :=
  match e with
  | EUnit | EBool _ | EI32 _ | EVar _
  | EStringNew _ _ | ELoc _ _ => true
  | EStringConcat e1 e2 | ELet e1 e2 | ELetLin e1 e2
  | EApp e1 e2 | EPair e1 e2 =>
      andb (tfuneff_lambda_free e1) (tfuneff_lambda_free e2)
  | EStringLen e' | EFst e' | ESnd e'
  | EBorrow e' | EDeref e' | EDrop e' | ECopy e' | EObserve e' =>
      tfuneff_lambda_free e'
  | EInl _ e' | EInr _ e' | EEcho _ e' | ERegion _ e' =>
      tfuneff_lambda_free e'
  | EIf e1 e2 e3 | ECase e1 e2 e3 =>
      andb (andb (tfuneff_lambda_free e1) (tfuneff_lambda_free e2))
           (tfuneff_lambda_free e3)
  | ELam _ _ => false
  end.

(** Syntactic closure predicate: [expr_closed_below k e] holds when [e]
    contains no free de Bruijn variable ≥ [k]. Variables < [k] are bound
    by lambda/let/case binders introduced *above* the term.

    Used by Phase 3b Stage 1b's TFunEff substitution lemma to permit
    G-polymorphic retype of the substituent v: for [expr_closed_below 0
    v] terms, the body of any TFunEff value [v = ELam T0 ebody] is
    [expr_closed_below 1] — i.e., references only position 0 (the bound
    variable). Outer context positions ≥ 1 are inert, which discharges
    the G-mismatch in compound-rule cases of the substitution lemma.

    Binder structure (mirrors [shift] / [subst] at lines 542-606):
    - [ELam _ e0]:   e0 at S k (one binder).
    - [ELet e1 e2]:  e1 at k, e2 at S k.
    - [ELetLin e1 e2]: e1 at k, e2 at S k.
    - [ECase e0 e1 e2]: e0 at k, e1 and e2 each at S k.
    - All other forms: same k across sub-expressions.

    [bool] target per Phase D's post-redesign style ([is_linear_ty],
    [is_ground_nonlinear_ty], [tfuneff_lambda_free] are all bool). The
    legacy [expr_free_of_region] / [expr_strictly_free_of_region] Prop
    predicates are pre-redesign artefacts.

    Refs [formal/SUBST-LEMMA-GENERALIZATION-DESIGN.md] Phase 3b Stage 1b
    and ephapax issue #249. *)
Fixpoint expr_closed_below (k : nat) (e : expr) : bool :=
  match e with
  | EUnit | EBool _ | EI32 _ => true
  | EVar i => Nat.ltb i k
  | EStringNew _ _ | ELoc _ _ => true
  | EStringConcat e1 e2 | EApp e1 e2 | EPair e1 e2 =>
      andb (expr_closed_below k e1) (expr_closed_below k e2)
  | ELet e1 e2 | ELetLin e1 e2 =>
      andb (expr_closed_below k e1) (expr_closed_below (S k) e2)
  | EStringLen e' | EFst e' | ESnd e'
  | EBorrow e' | EDeref e' | EDrop e' | ECopy e' | EObserve e' =>
      expr_closed_below k e'
  | EInl _ e' | EInr _ e' | EEcho _ e' | ERegion _ e' =>
      expr_closed_below k e'
  | EIf e1 e2 e3 =>
      andb (andb (expr_closed_below k e1) (expr_closed_below k e2))
           (expr_closed_below k e3)
  | ECase e0 e1 e2 =>
      andb (andb (expr_closed_below k e0)
                 (expr_closed_below (S k) e1))
           (expr_closed_below (S k) e2)
  | ELam _ e' => expr_closed_below (S k) e'
  end.

(** Check if all linear variables in context have been used *)
Fixpoint ctx_all_linear_used (G : ctx) : Prop :=
  match G with
  | [] => True
  | (T, used) :: G' =>
      (is_linear_ty T = true -> used = true) /\ ctx_all_linear_used G'
  end.

(** ** De Bruijn Shifting and Substitution

    Standard infrastructure for substitution-based operational semantics.

    shift c d e — increment free variables >= cutoff c by amount d
    subst k s e — replace variable k with expression s, decrement vars > k

    DESIGN NOTE (2026-03-28): The original environment-based semantics had
    an environment-leaking bug where congruence rules (S_Let_Step etc.)
    propagated environment extensions from sub-expression evaluation to
    sibling expressions, making preservation genuinely false for nested
    binding reductions. Substitution-based semantics eliminates this class
    of bugs by resolving bindings at reduction time. *)

(** Shift free variables >= cutoff by amount d *)
Fixpoint shift (c : nat) (d : nat) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EI32 n => EI32 n
  | EVar i => if Nat.leb c i then EVar (i + d) else EVar i
  | EStringNew r s => EStringNew r s
  | EStringConcat e1 e2 => EStringConcat (shift c d e1) (shift c d e2)
  | EStringLen e0 => EStringLen (shift c d e0)
  | ELet e1 e2 => ELet (shift c d e1) (shift (S c) d e2)
  | ELetLin e1 e2 => ELetLin (shift c d e1) (shift (S c) d e2)
  | EIf e1 e2 e3 => EIf (shift c d e1) (shift c d e2) (shift c d e3)
  | ELam T e0 => ELam T (shift (S c) d e0)
  | EApp e1 e2 => EApp (shift c d e1) (shift c d e2)
  | EPair e1 e2 => EPair (shift c d e1) (shift c d e2)
  | EFst e0 => EFst (shift c d e0)
  | ESnd e0 => ESnd (shift c d e0)
  | EInl T e0 => EInl T (shift c d e0)
  | EInr T e0 => EInr T (shift c d e0)
  | ECase e0 e1 e2 => ECase (shift c d e0) (shift (S c) d e1) (shift (S c) d e2)
  | ERegion r e0 => ERegion r (shift c d e0)
  | EBorrow e0 => EBorrow (shift c d e0)
  | EDeref e0 => EDeref (shift c d e0)
  | EDrop e0 => EDrop (shift c d e0)
  | ECopy e0 => ECopy (shift c d e0)
  | ELoc l r => ELoc l r
  | EEcho T e0 => EEcho T (shift c d e0)
  | EObserve e0 => EObserve (shift c d e0)
  end.

(** Substitution: replace variable k with s, decrementing vars > k.
    Under binders, k increments and s is shifted up. *)
Fixpoint subst (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EI32 n => EI32 n
  | EVar i => if Nat.eqb i k then s
              else if Nat.ltb k i then EVar (i - 1)
              else EVar i
  | EStringNew r str => EStringNew r str
  | EStringConcat e1 e2 => EStringConcat (subst k s e1) (subst k s e2)
  | EStringLen e0 => EStringLen (subst k s e0)
  | ELet e1 e2 => ELet (subst k s e1) (subst (S k) (shift 0 1 s) e2)
  | ELetLin e1 e2 => ELetLin (subst k s e1) (subst (S k) (shift 0 1 s) e2)
  | EIf e1 e2 e3 => EIf (subst k s e1) (subst k s e2) (subst k s e3)
  | ELam T e0 => ELam T (subst (S k) (shift 0 1 s) e0)
  | EApp e1 e2 => EApp (subst k s e1) (subst k s e2)
  | EPair e1 e2 => EPair (subst k s e1) (subst k s e2)
  | EFst e0 => EFst (subst k s e0)
  | ESnd e0 => ESnd (subst k s e0)
  | EInl T e0 => EInl T (subst k s e0)
  | EInr T e0 => EInr T (subst k s e0)
  | ECase e0 e1 e2 => ECase (subst k s e0)
                             (subst (S k) (shift 0 1 s) e1)
                             (subst (S k) (shift 0 1 s) e2)
  | ERegion r e0 => ERegion r (subst k s e0)
  | EBorrow e0 => EBorrow (subst k s e0)
  | EDeref e0 => EDeref (subst k s e0)
  | EDrop e0 => EDrop (subst k s e0)
  | ECopy e0 => ECopy (subst k s e0)
  | ELoc l r => ELoc l r
  | EEcho T e0 => EEcho T (subst k s e0)
  | EObserve e0 => EObserve (subst k s e0)
  end.

(** Shifting preserves the value property *)
Lemma shift_preserves_value :
  forall c d v, is_value v -> is_value (shift c d v).
Proof.
  intros c d v Hv. induction Hv; simpl; try constructor; auto.
Qed.

(** Closed-below-c terms are shift-invariant at cutoff c.

    The shift function increments free variables ≥ c. A term that is
    [expr_closed_below c] has no such variables, so shift is the
    identity. Companion to [shift_preserves_value] for the closure-
    sensitive Phase 3b Stage 1b machinery: when substituting a closed
    TFunEff value through a binder, the operational [shift 0 1 v] in
    [subst]'s ELam/ELet/ELetLin/ECase cases reduces to [v] itself,
    matching the syntactic shape needed by the substitution lemma's
    recursive rebuild.

    Proof: induction on [e] with c, d re-introduced after [induction]
    to keep the IH polymorphic over c (the cutoff varies through
    binders). *)
Lemma closed_below_shift_id :
  forall e c d, expr_closed_below c e = true -> shift c d e = e.
Proof.
  induction e; intros c d Hc; simpl in *; try reflexivity.
  - (* EVar v: Hc : v <? c = true, so leb c v = false, shift returns
       EVar v unchanged. *)
    apply Nat.ltb_lt in Hc.
    destruct (Nat.leb_spec c v) as [Hle|Hlt]; [lia | reflexivity].
  - (* EStringConcat e1 e2 *)
    apply andb_prop in Hc as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2]; assumption.
  - (* EStringLen e' *)
    f_equal. apply IHe. assumption.
  - (* ELet e1 e2 — e1 at c, e2 at S c *)
    apply andb_prop in Hc as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2]; assumption.
  - (* ELetLin e1 e2 *)
    apply andb_prop in Hc as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2]; assumption.
  - (* EIf e1 e2 e3 *)
    apply andb_prop in Hc as [H12 H3].
    apply andb_prop in H12 as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2 | apply IHe3]; assumption.
  - (* ELam T e' — e' at S c *)
    f_equal. apply IHe. assumption.
  - (* EApp e1 e2 *)
    apply andb_prop in Hc as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2]; assumption.
  - (* EPair e1 e2 *)
    apply andb_prop in Hc as [H1 H2].
    f_equal; [apply IHe1 | apply IHe2]; assumption.
  - (* EFst *)
    f_equal. apply IHe. assumption.
  - (* ESnd *)
    f_equal. apply IHe. assumption.
  - (* EInl T e' *)
    f_equal. apply IHe. assumption.
  - (* EInr T e' *)
    f_equal. apply IHe. assumption.
  - (* ECase e0 e1 e2 — e0 at c, e1 and e2 at S c *)
    apply andb_prop in Hc as [H01 H2].
    apply andb_prop in H01 as [H0 H1].
    f_equal; [apply IHe1 | apply IHe2 | apply IHe3]; assumption.
  - (* ERegion *)
    f_equal. apply IHe. assumption.
  - (* EBorrow *)
    f_equal. apply IHe. assumption.
  - (* EDeref *)
    f_equal. apply IHe. assumption.
  - (* EDrop *)
    f_equal. apply IHe. assumption.
  - (* ECopy *)
    f_equal. apply IHe. assumption.
  - (* EEcho T e' *)
    f_equal. apply IHe. assumption.
  - (* EObserve *)
    f_equal. apply IHe. assumption.
Qed.

(** Closure is preserved under shifting at any cutoff.

    A term [e] that is closed below cutoff [c] remains closed below
    cutoff [c + d] after shifting by d at any cutoff ≤ c. Useful when
    propagating closure through binder traversals in the substitution
    lemma's recursive calls.

    Proof: induction on [e] with all parameters generalised. The
    EVar case is the only non-trivial one — the others propagate
    through structural recursion. *)
Lemma expr_closed_below_shift_mono :
  forall e c c' d,
    c' <= c ->
    expr_closed_below c e = true ->
    expr_closed_below (c + d) (shift c' d e) = true.
Proof.
  induction e; intros cu cu' d Hle Hc; simpl in *; try reflexivity.
  - (* EVar v *)
    apply Nat.ltb_lt in Hc.
    destruct (Nat.leb_spec cu' v) as [Hge|Hlt].
    + (* cu' ≤ v: shift produces EVar (v + d); need v + d < cu + d *)
      simpl. apply Nat.ltb_lt. lia.
    + (* v < cu': shift unchanged; v < cu ≤ cu + d *)
      simpl. apply Nat.ltb_lt. lia.
  - (* EStringConcat *)
    apply andb_prop in Hc as [H1 H2]. simpl.
    rewrite IHe1 by assumption. rewrite IHe2 by assumption. reflexivity.
  - (* EStringLen *)
    apply IHe; assumption.
  - (* ELet — e2 at S cu, with the shift cutoff also at S cu' *)
    apply andb_prop in Hc as [H1 H2]. simpl.
    rewrite IHe1 by assumption.
    replace (S (cu + d)) with (S cu + d) by lia.
    rewrite IHe2; [reflexivity | lia | assumption].
  - (* ELetLin *)
    apply andb_prop in Hc as [H1 H2]. simpl.
    rewrite IHe1 by assumption.
    replace (S (cu + d)) with (S cu + d) by lia.
    rewrite IHe2; [reflexivity | lia | assumption].
  - (* EIf *)
    apply andb_prop in Hc as [H12 H3].
    apply andb_prop in H12 as [H1 H2]. simpl.
    rewrite IHe1, IHe2, IHe3 by assumption. reflexivity.
  - (* ELam — e' at S cu *)
    simpl.
    replace (S (cu + d)) with (S cu + d) by lia.
    apply IHe; [lia | assumption].
  - (* EApp *)
    apply andb_prop in Hc as [H1 H2]. simpl.
    rewrite IHe1, IHe2 by assumption. reflexivity.
  - (* EPair *)
    apply andb_prop in Hc as [H1 H2]. simpl.
    rewrite IHe1, IHe2 by assumption. reflexivity.
  - (* EFst *) apply IHe; assumption.
  - (* ESnd *) apply IHe; assumption.
  - (* EInl *) apply IHe; assumption.
  - (* EInr *) apply IHe; assumption.
  - (* ECase *)
    apply andb_prop in Hc as [H01 H2].
    apply andb_prop in H01 as [H0 H1]. simpl.
    rewrite IHe1 by assumption.
    replace (S (cu + d)) with (S cu + d) by lia.
    rewrite IHe2; [|lia|assumption].
    rewrite IHe3; [reflexivity|lia|assumption].
  - (* ERegion *) apply IHe; assumption.
  - (* EBorrow *) apply IHe; assumption.
  - (* EDeref *) apply IHe; assumption.
  - (* EDrop *) apply IHe; assumption.
  - (* ECopy *) apply IHe; assumption.
  - (* EEcho *) apply IHe; assumption.
  - (* EObserve *) apply IHe; assumption.
Qed.

(** ** Region Environment *)

Definition region_env := list region_name.

Definition region_active (R : region_env) (r : region_name) : Prop :=
  In r R.
