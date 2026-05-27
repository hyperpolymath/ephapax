(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(** * Ephapax L3 — Echo / residue type former (forward-looking scaffold)

    This file mechanises Layer 3 of the four-layer preservation
    redesign (PRESERVATION-DESIGN.md §6). L3 is the irreversibility-
    residue layer: every irreversible operation in Ephapax
    ([S_Region_Exit], [S_Drop], and Affine-implicit drop) produces a
    residue value whose type carries a proof-relevant witness of
    *which* value was erased.

    Per the design doc, L3 is FORWARD-LOOKING — [preservation_l1] does
    not depend on this layer. The mechanisation here mirrors the Agda
    upstream at:

    - [echo-types/proofs/agda/Echo.agda] — the fiber type former
      [Echo : (A → B) → B → Set] defined as [Σ A (λ x → f x ≡ y)].
    - [echo-types/proofs/agda/EchoLinear.agda] — the two-mode
      [LEcho : Mode → Set]; the weakening [Linear → Affine]; the
      decoration-commuting per-mode composition lemma
      [degradeMode-comp].

    What is in this file (first L3 slice):

    - [Mode], the [mode_le] thin-poset, [mode_le_refl] /
      [mode_le_trans] / [mode_le_prop] all [Qed].
    - [Echo] as a record-shaped fiber type former.
    - A concrete [collapse : bool → unit] and
      [LEcho : Mode → Type] mode-polymorphic family.
    - [weaken : LEcho Linear → LEcho Affine] (the irreversible
      collapse) and [weaken_collapses_distinction] witnessing that
      the Linear distinction is genuinely erased.
    - [degrade_mode] and the headline composition law
      [degrade_mode_comp] ([Qed]).
    - [affine_canonical] / [affine_all_equal] — propositionality of
      Affine echoes.

    What is NOT in this file (separate forward-looking PRs):

    - [TEcho] type former added to [Syntax.v] (the new [ty]
      constructor). L3 cannot type-decorate ephapax expressions until
      [TEcho] lands in [ty].
    - [T_Observe] typing rule. Linear-mode [T_Observe] consumes;
      Affine-mode [T_Observe] does not.
    - Residue-producing operational rules ([S_Region_Exit] and
      [S_Drop] with residue outputs).
    - Integration into [has_type_l1] / [preservation_l1].
    - Full collapse/residue characteristic infrastructure (separating
      models, the [EchoR ⊤ TrivialCert] form, the no-section result).

    Per PRESERVATION-DESIGN.md §6.4, L1 + L2 must not bake in
    assumptions that block L3. The three constraints are:

    1. Preservation must not assume residue ≡ nothing.
    2. No per-type echo-ability predicates.
    3. Typing rules are modality-polymorphic (only [T_Observe]
       splits per mode).

    The L1 design as captured in [TypingL1.v] and [Semantics_L1.v]
    satisfies all three constraints. This file does not introduce
    contradictions with them. *)

(** ** Proof-debt note (axiom dependencies)

    Two lemmas in this file ([mode_le_trans] and [degrade_mode_comp])
    use [dependent destruction] from [Coq.Program.Equality] to
    discriminate impossible cases on the indexed inductive
    [mode_le]. This pulls in Coq's standard [eq_rect_eq] (K / UIP)
    axiom.

    The Agda upstream ([EchoLinear.agda]) is [--safe --without-K]
    and discharges these cases without K. The rest of the Ephapax
    Coq codebase (per [Print Assumptions] on [value_R_G_preserving_l1],
    [subst_preserves_typing_l1]) is also K-free.

    A follow-up slice should rewrite [mode_le_trans] and
    [degrade_mode_comp] using raw dependent pattern matching with
    motive tricks to be K-free, aligning with the Agda upstream and
    the rest of the Coq codebase. Tracked as L3.K proof-debt. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.

(** ===== Modes =====

    The L2 layer of the design (PRESERVATION-DESIGN.md §5) parameterises
    the typing judgment over a modality [ℓ ∈ {Linear, Affine}]. L3
    consumes the modality to choose the echo discipline: Linear echoes
    are full fibers (proof-relevant), Affine echoes are propositional
    residues (proof-irrelevant). *)

Inductive Mode : Type :=
  | Linear : Mode
  | Affine : Mode.

(** The thin poset on Mode: [Linear ⊑ Linear], [Linear ⊑ Affine],
    [Affine ⊑ Affine]. This is the linearity-side analog of
    EchoLinear.agda's [_≤m_]. *)

(** Sort [Type] (not [Prop]) so [mode_le] can drive the
    [degrade_mode] dispatch at the Type level. Mirrors the Agda
    [data _≤m_ : Mode → Mode → Set]. *)

Inductive mode_le : Mode -> Mode -> Type :=
  | Linear_le_Linear : mode_le Linear Linear
  | Linear_le_Affine : mode_le Linear Affine
  | Affine_le_Affine : mode_le Affine Affine.

Lemma mode_le_refl : forall m, mode_le m m.
Proof. intros [|]; constructor. Qed.

(** [Defined] (not [Qed]) so [mode_le_trans] is transparent and
    [degrade_mode_comp] can [simpl] through its applications. Uses
    [dependent destruction] (K-dependent) — see the proof-debt note
    at the top of the file. *)

Definition mode_le_trans
  (m1 m2 m3 : Mode)
  (H12 : mode_le m1 m2) (H23 : mode_le m2 m3) : mode_le m1 m3.
Proof.
  destruct H12.
  - exact H23.
  - dependent destruction H23. exact Linear_le_Affine.
  - exact H23.
Defined.

(** Propositionality of the mode order. Each pair [(m1, m2)] has at
    most one inhabitant in [mode_le]. This is what lets us collapse
    composed-via-[m2] weakening proofs against an independently-given
    [m1 ⊑ m3] in [degrade_mode_compose].

    Mirrors EchoLinear.agda's [≤m-prop]. *)

Lemma mode_le_prop :
  forall m1 m2 (p q : mode_le m1 m2), p = q.
Proof.
  intros m1 m2 p q.
  destruct p;
    refine
      match q as q'
        in mode_le mA mB
        return
          (match mA, mB return mode_le mA mB -> Prop with
           | Linear, Linear => fun q'' => Linear_le_Linear = q''
           | Linear, Affine => fun q'' => Linear_le_Affine = q''
           | Affine, Affine => fun q'' => Affine_le_Affine = q''
           | _, _ => fun _ => True
           end q')
      with
      | Linear_le_Linear => eq_refl
      | Linear_le_Affine => eq_refl
      | Affine_le_Affine => eq_refl
      end.
Qed.

(** ===== The Echo type former =====

    [Echo f y] is the fiber of [f : A → B] over [y : B] — the type of
    pairs [(x, p)] where [x : A] and [p : f x = y]. Proof-relevant:
    *which* preimage maps to [y] is information the irreversibility of
    [f] deliberately erased and that this type recovers as a witness.

    Mirrors echo-types/proofs/agda/Echo.agda:14-15. *)

Record Echo {A B : Type} (f : A -> B) (y : B) : Type := mkEcho {
  echo_witness : A;
  echo_eq      : f echo_witness = y
}.

Arguments mkEcho       {A B f y} echo_witness echo_eq.
Arguments echo_witness {A B f y} _.
Arguments echo_eq      {A B f y} _.

(** Introduction into the own fiber. Mirrors [echo-intro] in Echo.agda. *)

Definition echo_intro {A B : Type} (f : A -> B) (x : A) : Echo f (f x) :=
  mkEcho x eq_refl.

(** ===== Linear vs Affine echo: the L3 carrier =====

    A concrete instance of the two-mode echo, matching
    EchoLinear.agda's characteristic carrier:

    - Linear echo is the full fiber [Echo collapse tt] for the
      forgetful [collapse : bool → unit]. The fiber has two distinct
      inhabitants (one per bool); these are the [echo_true] and
      [echo_false] of EchoCharacteristic.agda.
    - Affine echo is the trivial residue [unit]: any two affine
      echoes are equal.

    This concrete pair is enough to state and prove the headline
    weakening + decoration-commuting lemmas. The full
    [EchoR ⊤ TrivialCert tt] residue form and the [no-section]
    impossibility result are deferred to a separate slice. *)

Definition collapse (b : bool) : unit := tt.

Definition LEcho (m : Mode) : Type :=
  match m with
  | Linear => Echo collapse tt
  | Affine => unit
  end.

(** Linear-mode constants: the two distinguishable echoes. *)

Definition echo_true  : LEcho Linear := mkEcho true  eq_refl.
Definition echo_false : LEcho Linear := mkEcho false eq_refl.

(** The two Linear echoes really are distinct — the witnesses are
    different bools. *)

Lemma echo_true_ne_echo_false : echo_true <> echo_false.
Proof.
  intro H.
  assert (Hwit : echo_witness echo_true = echo_witness echo_false)
    by (rewrite H; reflexivity).
  simpl in Hwit. discriminate.
Qed.

(** The Linear-to-Affine weakening: the irreversible collapse.

    Mirrors EchoLinear.agda:38-39 ([weaken : LEcho linear → LEcho
    affine]). In this concrete instance the weakening simply forgets
    the bool witness, since the affine residue carries none. *)

Definition weaken (e : LEcho Linear) : LEcho Affine := tt.

(** Witness that the Linear distinction collapses under weakening —
    both [echo_true] and [echo_false] weaken to the same affine
    residue. Mirrors EchoLinear.agda's
    [weaken-collapses-distinction]. *)

Lemma weaken_collapses_distinction :
  weaken echo_true = weaken echo_false.
Proof. reflexivity. Qed.

(** All Affine echoes are equal (propositionality of [unit]). *)

Lemma affine_canonical : forall e : LEcho Affine, e = tt.
Proof. intros []; reflexivity. Qed.

Lemma affine_all_equal :
  forall e1 e2 : LEcho Affine, e1 = e2.
Proof.
  intros e1 e2.
  rewrite (affine_canonical e1).
  rewrite (affine_canonical e2).
  reflexivity.
Qed.

(** ===== Mode weakening on echoes (decoration-commuting recipe) =====

    [degrade_mode] is the dispatch function: identity on the
    reflexive cases ([Linear ⊑ Linear], [Affine ⊑ Affine]) and
    [weaken] on the strict step ([Linear ⊑ Affine]).

    Mirrors EchoLinear.agda:85-88. *)

Definition degrade_mode {m1 m2 : Mode}
  (p : mode_le m1 m2) : LEcho m1 -> LEcho m2 :=
  match p in mode_le mA mB return LEcho mA -> LEcho mB with
  | Linear_le_Linear => fun e => e
  | Linear_le_Affine => weaken
  | Affine_le_Affine => fun e => e
  end.

(** Identity weakening corollaries: degrading along a reflexive proof
    is the identity. Useful when chaining with [degrade_mode_comp]. *)

Lemma degrade_mode_id_linear :
  forall e : LEcho Linear,
    degrade_mode Linear_le_Linear e = e.
Proof. reflexivity. Qed.

Lemma degrade_mode_id_affine :
  forall e : LEcho Affine,
    degrade_mode Affine_le_Affine e = e.
Proof. reflexivity. Qed.

(** The strict step agrees with [weaken] definitionally. *)

Lemma degrade_mode_strict_is_weaken :
  forall e : LEcho Linear,
    degrade_mode Linear_le_Affine e = weaken e.
Proof. reflexivity. Qed.

(** Headline per-decoration composition lemma: two successive mode
    weakenings agree with a single weakening along the composed
    ordering proof.

    Mirrors EchoLinear.agda's [degradeMode-comp] (lines 93-101). This
    is the L3 instance of the "decoration commuting" recipe noted in
    PRESERVATION-DESIGN.md §3 and §5; combined with [mode_le_prop],
    it lets any two factorisations of a mode-weakening through the
    same composite [m1 ⊑ m3] agree. *)

Lemma degrade_mode_comp :
  forall {m1 m2 m3} (p12 : mode_le m1 m2) (p23 : mode_le m2 m3)
         (e : LEcho m1),
    degrade_mode p23 (degrade_mode p12 e) =
    degrade_mode (mode_le_trans m1 m2 m3 p12 p23) e.
Proof.
  intros m1 m2 m3 p12 p23 e.
  destruct p12.
  - reflexivity.
  - dependent destruction p23. reflexivity.
  - dependent destruction p23. reflexivity.
Qed.

(** Free-factoring composition law: any direct ordering proof
    [p13 : mode_le m1 m3] agrees with the composed-via-[m2] weakening,
    because [mode_le_prop] makes the choice of factoring irrelevant.

    Mirrors EchoLinear.agda's [degradeMode-compose]. *)

Lemma degrade_mode_compose :
  forall {m1 m2 m3}
         (p12 : mode_le m1 m2) (p23 : mode_le m2 m3)
         (p13 : mode_le m1 m3) (e : LEcho m1),
    degrade_mode p23 (degrade_mode p12 e) =
    degrade_mode p13 e.
Proof.
  intros m1 m2 m3 p12 p23 p13 e.
  rewrite (mode_le_prop _ _ p13 (mode_le_trans _ _ _ p12 p23)).
  apply degrade_mode_comp.
Qed.

(** ===== Cross-mode characteristic =====

    Witness that Linear→Affine weakening is genuinely lossy: there
    exist distinct Linear echoes whose Affine weakenings are equal.
    Mirrors EchoLinear.agda's [strict-linear-example]. *)

Lemma strict_linear_example :
  exists e1 e2 : LEcho Linear,
    e1 <> e2 /\ weaken e1 = weaken e2.
Proof.
  exists echo_true, echo_false.
  split.
  - apply echo_true_ne_echo_false.
  - apply weaken_collapses_distinction.
Qed.

(** ===== Phase 2: General residue + no-section irreversibility =====

    The Phase 1 [weaken] above goes directly to [unit] for the
    Affine carrier, which is the simplest possible witness that
    information is lost. Phase 2 introduces a richer residue
    [EchoR C Cert y] — a [C]-valued residue plus a certification
    relation [Cert : C → B → Type] — and lowers the Linear echo into
    it via [echo_to_residue].

    The Phase-2 carrier matches the Agda upstream
    [echo-types/proofs/agda/EchoResidue.agda] one-for-one. The
    headline of Phase 2 is [no_section_collapse_to_residue]: there is
    no inverse to the lowering, so the Linear→Affine collapse is
    *genuinely* irreversible, not merely "I happened to throw away
    the bit".

    Why this matters for L3: when [TEcho] eventually lands in
    [Syntax.v] (separate slice), an Affine-mode residue value will be
    typed at [TEcho ⟨affine-collapse⟩] which inhabits
    [EchoR ⊤ TrivialCert tt]. The fact that no section exists is the
    *structural* statement that an Affine implicit drop has nowhere
    to go back to — the typing system can permit it precisely because
    irreversibility is mechanised. *)

(** Weakened echo: keep a residue [r : C] plus a certification
    relation [Cert r y] to the visible [y : B]. Mirrors
    EchoResidue.agda's [EchoR]. *)

Record EchoR {B : Type} (C : Type) (Cert : C -> B -> Type) (y : B)
  : Type := mkEchoR {
  residue  : C;
  residue_cert : Cert residue y
}.

Arguments mkEchoR {B C Cert y} residue residue_cert.
Arguments residue {B C Cert y} _.
Arguments residue_cert {B C Cert y} _.

(** Every full echo can be lowered to a residue echo, provided
    residue-soundness: a residue-projection [κ] and a soundness
    witness that [κ] respects [Cert] along [f]. Mirrors
    EchoResidue.agda's [echo-to-residue]. *)

Definition echo_to_residue
  {A B C : Type}
  (f : A -> B)
  (kappa : A -> C)
  (Cert : C -> B -> Type)
  (sound : forall x, Cert (kappa x) (f x))
  {y : B}
  (e : Echo f y) : EchoR C Cert y :=
  mkEchoR
    (kappa (echo_witness e))
    (eq_rect (f (echo_witness e))
             (fun b => Cert (kappa (echo_witness e)) b)
             (sound (echo_witness e))
             y
             (echo_eq e)).

(** Specialised to the collapse [bool → unit]: the residue carrier
    is [unit], the certificate is trivial. *)

Definition TrivialCert (_ _ : unit) : Type := unit.

Definition collapse_kappa (b : bool) : unit := tt.

Definition collapse_sound (b : bool)
  : TrivialCert (collapse_kappa b) (collapse b) := tt.

Definition collapse_to_residue
  : Echo collapse tt -> EchoR unit TrivialCert tt :=
  echo_to_residue collapse collapse_kappa TrivialCert collapse_sound.

(** Both [echo_true] and [echo_false] lower to the same residue —
    the bool distinction collapses under the residue projection.
    Mirrors EchoResidue.agda's [collapse-residue-same]. *)

Lemma collapse_residue_same :
  collapse_to_residue echo_true = collapse_to_residue echo_false.
Proof. reflexivity. Qed.

(** ===== Headline irreversibility theorem =====

    There is NO section to the Linear→Affine residue lowering — no
    function from [EchoR ⊤ TrivialCert tt] back to [Echo collapse tt]
    can be a one-sided inverse of [collapse_to_residue].

    This is the *type-theoretic* witness that the Linear→Affine
    collapse is genuinely irreversible: if such a section existed,
    [collapse_residue_same] would force [echo_true = echo_false],
    contradicting [echo_true_ne_echo_false].

    Mirrors EchoResidue.agda's [no-section-collapse-to-residue]. *)

Lemma no_section_collapse_to_residue :
  ~ exists reify : EchoR unit TrivialCert tt -> Echo collapse tt,
      forall e, reify (collapse_to_residue e) = e.
Proof.
  intros [reify sec].
  apply echo_true_ne_echo_false.
  (** Both [echo_true] and [echo_false] must round-trip through
      [reify ∘ collapse_to_residue] to themselves. But
      [collapse_residue_same] forces both inputs to [reify] to be
      equal — so the two outputs must be equal as well. *)
  pose proof (sec echo_true)  as p_true.
  pose proof (sec echo_false) as p_false.
  assert (p_false' : reify (collapse_to_residue echo_true) = echo_false).
  { rewrite collapse_residue_same. exact p_false. }
  rewrite <- p_true. exact p_false'.
Qed.

(** M3 pass: explicit weakening packaged with its non-recoverability
    witness. The L3 layer ships *both* directions — the lowering
    arrow [collapse_to_residue] AND the no-section impossibility —
    because the type-theoretic guarantee of L3 is that the lowering
    exists exactly when the recovery does not.

    Mirrors EchoResidue.agda's [strict-weakening-collapse]. *)

Lemma strict_weakening_collapse :
  exists lower : Echo collapse tt -> EchoR unit TrivialCert tt,
    ~ exists raise : EchoR unit TrivialCert tt -> Echo collapse tt,
        forall e, raise (lower e) = e.
Proof.
  exists collapse_to_residue.
  exact no_section_collapse_to_residue.
Qed.

(** ===== Mode-join structure (propositional join) =====

    Mirrors EchoLinear.agda's [_⊔m_], [≤m-⊔m-{left,right,univ}], and
    [degradeMode-via-join]. The join makes [Mode] a thin meet-
    semilattice: [Affine] is top, [Linear ⊔ _] = the other argument. *)

Definition mode_join (m1 m2 : Mode) : Mode :=
  match m1 with
  | Linear => m2
  | Affine => Affine
  end.

Lemma mode_le_join_left :
  forall m1 m2, mode_le m1 (mode_join m1 m2).
Proof.
  intros [|] [|]; simpl; constructor.
Qed.

Lemma mode_le_join_right :
  forall m1 m2, mode_le m2 (mode_join m1 m2).
Proof.
  intros [|] [|]; simpl; constructor.
Qed.

Lemma mode_le_join_univ :
  forall {m1 m2 m3},
    mode_le m1 m3 -> mode_le m2 m3 -> mode_le (mode_join m1 m2) m3.
Proof.
  intros m1 m2 m3 p1 p2.
  destruct p1; simpl; try assumption; constructor.
Qed.

(** Restating the per-mode weakening through the join structure:
    any weakening into a common upper bound [m3] factors through
    [mode_join m1 m2]. Mirrors EchoLinear.agda's [degradeMode-via-join]. *)

Lemma degrade_mode_via_join :
  forall {m1 m2 m3}
         (p1 : mode_le m1 m3) (p2 : mode_le m2 m3) (e : LEcho m1),
    degrade_mode p1 e =
    degrade_mode (mode_le_join_univ p1 p2)
                 (degrade_mode (mode_le_join_left m1 m2) e).
Proof.
  intros m1 m2 m3 p1 p2 e.
  symmetry.
  apply (degrade_mode_compose (mode_le_join_left m1 m2)
                              (mode_le_join_univ p1 p2)
                              p1 e).
Qed.
