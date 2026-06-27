<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Session handoff — `step_pop` §6 experiment + how to continue (web → desktop)

This note exists so the work from a Claude-Code-on-the-web (cloud) session
survives the move to the desktop app. The cloud container is ephemeral; only
what is pushed to git persists. Everything important is below.

## 1. What already landed (all merged to `main`)

| PR | What | Result |
|---|---|---|
| #322 | `region_liveness` proof closure | removed the provably-false `region_liveness_at_split_l1_gen`; routed its 13 consumers through the true `region_liveness_no_exit_l1_gen` via a new `val_region_no_exit` premise. **Outer `Admitted.` 4 → 3**; L2 β-cases now axiom-free. |
| #323 | iser-style prover bootstrap | `scripts/install-{coq,idris2,zig}.sh` + `bootstrap-provers.sh`, SessionStart hook + devcontainer + `.tool-versions` + `just bootstrap`. |
| #324 | SessionStart hook → synchronous | provers guaranteed before first prompt; cold Idris2 build paid once, container-cached after. |

Provers all install + run (Coq 8.18.0, Idris2 0.7.0, Zig 0.14.0) via the
iser doctrine (curl+tar over HTTPS, never `git clone`). The "403 mystery"
was the proxy scoping the **git protocol** to one repo while allowlisting
**HTTPS egress** — so tarballs from codeload/ziglang.org work.

## 2. The `step_pop` §6 deciding experiment — VERDICT: relocates, cleanly

`step_pop_disjoint_from_type_l1` (`formal/Semantics_L1.v`) is ADMIT 3, the
eliminator fork (see `formal/L1-ELIMINATOR-FORK.md`). I ran the §6 deciding
experiment in Coq. Outcome:

**(a) It reduces from 11 internal admits to 1.** `step_R_change_shape`
(`formal/Semantics.v`, already `Qed`) says every step leaves `R` unchanged,
prepends a fresh region, or removes exactly one. So 10 of 11 cases are
trivial; only "the step exits `r0` itself" is hard. The reduced proof below
**was verified to compile** (with the single `admit`):

```coq
Lemma step_pop_disjoint_from_type_l1 :
  forall mu R e mu' R' e' m G T R_final G',
    (mu, R, e) -->> (mu', R', e') ->
    has_type_l1 m R G e T R_final G' ->
    forall r, In r (Typing.free_regions T) -> In r R -> In r R'.
Proof.
  intros mu R e mu' R' e' m G T R_final G' Hstep Ht r0 Hfree HinR.
  pose proof (step_R_change_shape _ _ _ _ _ _ Hstep)
    as [Heq | [[r [Hadd Hnotin]] | [r [Hrem Hr_in]]]].
  - (* R = R' *) subst R'. exact HinR.
  - (* R' = r :: R (enter) *) subst R'. simpl. right. exact HinR.
  - (* R' = remove_first r R (exit) *) subst R'.
    destruct (string_dec r r0) as [Heqr | Hne].
    + (* r = r0: step exits r0. Need In r0 (remove_first r0 R), i.e.
         cnt r0 R >= 2. THE single relocated obligation. *)
      subst r. admit.
    + (* r <> r0: remove_first r keeps every r0. *)
      apply remove_first_preserves_other; [exact Hne | exact HinR].
Admitted.
```

**(b) The single remaining obligation, precisely:**
> step exits `r0` ∧ `e : T` ∧ `r0 ∈ free_regions(T)` ⟹ `cnt r0 R ≥ 2`.

**(c) Its direct-exit sub-case is vacuous:** if the head redex is
`ERegion r0 v`, `T_Region_Active_L1` carries `~In r0 (free_regions T)`,
contradicting `r0 ∈ free_regions(T)`. The residue is the **congruence-exit**
case (the exiting `ERegion r0` is under a `Let`/`Case`/eliminator and `r0`
appears in a *sibling's* type).

**(d) Why it relocates, not closes:** discharging the congruence case needs
the sibling's `r0` to be a *distinct* occurrence from the exiting one — the
temporal/segment coherence the snapshot-env + result-type judgment cannot
express (a region env can count `r0` but not say *which* occurrence supports
the result vs. is exited). Every route (`free_regions ⊆ R_out`,
`count_occ_le_l1_m`, linking the dynamic exit to the static output) collapses
to connecting the dynamic step to the static typing output = preservation
itself. The §2 "same wall," mechanically confirmed. Also: the diagnosis in
the current source comment ("blocked on §4.8 lambda-rigidity") is **wrong** —
the witness `EDrop (EVar j : TString rv)` has no lambda; the real obstruction
is region-count coherence at a region exit.

## 3. Pending decision (was mid-question when the session moved)

Pick one on the desktop side:
1. **Land the 11→1 reduction** as a PR (proof 255→~15 lines, 1 clean admit,
   corrected diagnosis comment, update `PROOF-NEEDS.md` + `L1-ELIMINATOR-FORK.md`
   §6). Honest still-`Admitted` improvement; **outer count unchanged (still 2)**;
   `Print Assumptions` unchanged.
2. **Record the verdict only** — leave the fenced proof untouched; just add the
   §6 result to `L1-ELIMINATOR-FORK.md`.
3. **Attempt the choreographic closure** — build the tropically-graded
   segment/choreography structure to discharge the count-coherence obligation.
   High-reward (could close `step_pop` → `preservation_l1`), open-ended research.

## 4. How to continue on the desktop app

1. Clone/open ephapax locally and get latest: `git pull origin main`.
2. Get this note + branch: `git fetch origin && git checkout claude/l1-step-pop-eliminator-fork`.
3. Provision the provers locally (the SessionStart hook only fires for the web
   env — locally use): `just bootstrap`  (Coq via apt, Idris2 via codeload
   tarball + chezscheme/libgmp-dev, Zig via ziglang.org). ~15 min cold for Idris2.
4. Start a Claude Code session in that folder and tell it:
   *"Read STEP-POP-HANDOFF.md and continue the step_pop work — start with the pending decision in §3."*

The desktop session will NOT have this conversation's chat history (it's a
fresh local session), but this file carries everything it needs.
