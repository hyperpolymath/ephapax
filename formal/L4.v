(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(* SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell *)

(**

  *********************************************************************
  ***  ✅ ACTIVE -- L4 dyadic mode (labelling discipline).            ***
  ***                                                                ***
  ***  L4 is NOT a separate proof layer. This file carries           ***
  ***  Definitions ONLY:                                             ***
  ***    - [ProgramMode]: three-constructor enum.                    ***
  ***    - [program_mode_to_modality]: total mapping to L2.          ***
  ***                                                                ***
  ***  No theorems, no admit, no axiom.                              ***
  ***                                                                ***
  ***  Canonical design: formal/PRESERVATION-DESIGN.md §7.           ***
  ***  Companion doc:    formal/L4-DYADIC.md.                        ***
  *********************************************************************

*)

From Ephapax Require Import Modality.

(** * Ephapax L4 — Dyadic mode (program-level labelling)

    L4 is the outermost ring of the four-layer redesign. Where L1, L2,
    and L3 each carry a typing-layer judgment or per-layer proof
    obligation, L4 carries **none of that**. It is a labelling
    discipline applied at the program / module boundary.

    A closed Ephapax program declares one of three program modes; the
    declaration tells the type checker which L2 modality [m] to thread
    through [has_type_l1]. Once [m] is selected, L3's echo observation
    discipline follows from L2 with no further user input.

    See [formal/L4-DYADIC.md] for the design discussion; this file is
    purely the mechanical scaffold so downstream tools (Idris2 ABI,
    Rust borrow checker, surface parser) can refer to a citable type. *)

Inductive ProgramMode : Type :=
  | PModeLinear      : ProgramMode
  | PModeAffine      : ProgramMode
  | PModeBoundaryMix : Modality -> ProgramMode.

(** [program_mode_to_modality] selects the L2 modality threaded
    through a program's typing derivation. For [PModeBoundaryMix d],
    [d] is the default modality used outside any module-local
    declaration; per-module modality is read from the surrounding
    declaration in the surface syntax and is not represented at this
    layer. *)

Definition program_mode_to_modality (p : ProgramMode) : Modality :=
  match p with
  | PModeLinear        => Linear
  | PModeAffine        => Affine
  | PModeBoundaryMix d => d
  end.

(** Sanity: the round-trip from the two pure program modes through
    [program_mode_to_modality] recovers the expected L2 modality.
    This is definitional, not a theorem about the system. *)

Definition program_mode_linear_selects_linear :
  program_mode_to_modality PModeLinear = Linear := eq_refl.

Definition program_mode_affine_selects_affine :
  program_mode_to_modality PModeAffine = Affine := eq_refl.
