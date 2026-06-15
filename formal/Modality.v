(* SPDX-License-Identifier: MPL-2.0 *)
(* Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  ✅ ACTIVE -- L2 modality (Linear / Affine).                    ***
  ***                                                                ***
  ***  Linear ≤ Affine as a K-free thin poset.                       ***
  ***  `linear_to_affine` Qed with zero axioms.                      ***
  ***                                                                ***
  ***  L3 (Echo) reads the modality off this layer at typing-rule    ***
  ***  boundaries to dispatch observation discipline. DO NOT pattern ***
  ***  match on `Linear`/`Affine` inside `Echo.v` -- L3 orthogonality ***
  ***  requires that the echo type former remains modality-agnostic. ***
  ***                                                                ***
  ***  See `STATUS.adoc`, `formal/PRESERVATION-DESIGN.md §5` and §6. ***
  *********************************************************************

*)

(** * Ephapax L2 — Modality (the typing-layer mode parameter)

    This file defines the modality parameter that the L2 typing
    judgment carries. Per PRESERVATION-DESIGN.md §5, the modality
    [ℓ ∈ {Linear, Affine}] lives on the judgment:

      [R ; G  ⊢_ℓ  e : T  -|  R' ; G']

    The two sublanguages share [Syntax.v] and [Semantics.v]; they
    differ in which derivations the typing relation admits.

    Why a separate datatype from [Echo.Mode]: [Mode] (defined in
    [Echo.v]) classifies *echoes* — the L3 residue layer's
    propositional / proof-relevant distinction. [Modality] (defined
    here) classifies *typing derivations* — the L2 layer's strict /
    relaxed consumption discipline. They happen to be isomorphic
    (both are [{Linear, Affine}] with the same poset) but live at
    distinct conceptual layers; the L4 dyadic-interaction layer
    couples them via the project-level mode declaration.

    Cross-layer bridges are deferred to a follow-up.

    ===== Properties of this layer =====

    - [Modality]: enumerated type with [Linear] and [Affine].
    - [modality_le]: thin poset; [Linear ⊑ Linear], [Linear ⊑
      Affine], [Affine ⊑ Affine]. [Linear ≤ Affine] expresses that
      Linear is the more restrictive mode (so every Linear derivation
      is also an Affine derivation, modulo the same syntax).
    - [modality_le_refl] / [modality_le_trans] / [modality_le_prop]:
      structural properties, all Qed.

    Both K-free properties of this layer are inherited by the L2
    typing judgment: any rule that quantifies over modality can use
    [modality_le_prop] to discriminate proofs and [modality_le_trans]
    to compose mode-weakenings. *)

Inductive Modality : Type :=
  | Linear : Modality
  | Affine : Modality.

(** The thin poset on [Modality]: [Linear] is the strict mode
    (more restrictive), [Affine] the relaxed mode (permits implicit
    drops). [Linear ⊑ Affine] captures that every Linear derivation
    can be viewed as an Affine derivation. *)

Inductive modality_le : Modality -> Modality -> Type :=
  | Linear_le_Linear : modality_le Linear Linear
  | Linear_le_Affine : modality_le Linear Affine
  | Affine_le_Affine : modality_le Affine Affine.

Lemma modality_le_refl : forall m, modality_le m m.
Proof. intros [|]; constructor. Qed.

(** Helper: when the first modality is [Affine], the second is
    [Affine] too. K-free via a motive trick. *)

Definition modality_le_affine_first
  (m2 : Modality) (H : modality_le Affine m2) : m2 = Affine :=
  match H in modality_le mA mB
    return
      (match mA return Prop with
       | Affine => mB = Affine
       | Linear => True
       end)
  with
  | Linear_le_Linear => I
  | Linear_le_Affine => I
  | Affine_le_Affine => eq_refl
  end.

(** [Defined] (not [Qed]) so [modality_le_trans] is transparent.
    Built by raw dependent pattern matching with a motive trick;
    K-free, no [dependent destruction]. *)

Definition modality_le_trans
  (m1 m2 m3 : Modality)
  (H12 : modality_le m1 m2) : modality_le m2 m3 -> modality_le m1 m3 :=
  match H12 in modality_le mA mB
    return modality_le mB m3 -> modality_le mA m3
  with
  | Linear_le_Linear => fun h => h
  | Linear_le_Affine =>
      fun h =>
        eq_rect Affine (fun m => modality_le Linear m)
                Linear_le_Affine m3
                (eq_sym (modality_le_affine_first m3 h))
  | Affine_le_Affine => fun h => h
  end.

(** Propositionality of the modality order. K-free. *)

Lemma modality_le_prop :
  forall m1 m2 (p q : modality_le m1 m2), p = q.
Proof.
  intros m1 m2 p q.
  destruct p;
    refine
      match q as q'
        in modality_le mA mB
        return
          (match mA, mB return modality_le mA mB -> Prop with
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
