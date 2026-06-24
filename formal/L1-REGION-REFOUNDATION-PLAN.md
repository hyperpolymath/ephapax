<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# L1 region re-foundation — the clean-win Coq work-plan

**Scope.** This plan covers the two admits that the tropical re-foundation
dissolves cleanly: `region_shrink_preserves_typing_l1_gen_m` (ADMIT 1) and the
*false* `region_liveness_at_split_l1_gen` (ADMIT 2). It does **not** cover
`step_pop_disjoint_from_type_l1` (ADMIT 3, the eliminator fork) or the capstone
`preservation_l1` (ADMIT 4, gated on 3) — those are the separate research
problem (see `L1-ELIMINATOR-FORK.md`).

Evidence base: the isomorphism validation against `tropical-resource-typing`
(`docs/applications/ephapax-l1-regions.adoc` in that repo). The carrier
`list region_name` is a `region_name →₀ ℕ` grade vector wearing a list costume;
the admits live where the costume tears.

## ⚠️ REVISION 2026-06-16 — diagnosis correction (read before Step 0)

A code-level re-audit of `Semantics_L1.v` / `TypingL1.v` / `Syntax.v` found
the original plan below rests on a **misdiagnosis**. Step 0 (a single global
edit at `Syntax.v:867`) is **not viable** and the carrier is **not** the
actual blocker. Corrected findings:

1. **The carrier is shared with the fenced legacy judgment.**
   `region_env := list region_name` (`Syntax.v:867`) is used by the legacy
   `Typing.v` / `Semantics.v` (90 `region_env` refs, 88 list-cons, 151
   `In r R`) **and** by `Counterexample.v` (which couples to *both* carriers:
   `remove_first` ×4 *and* `remove_first_L1` ×4). A *global* Step-0 edit would
   rewrite the fenced legacy judgment and risk the `Counterexample.v`
   regression theorems (CLAUDE.md fences #2/#5). Only an **L1-only carrier
   fork** (a new `region_env_l1`, legacy left on the list) is admissible — not
   the "single highest-leverage edit" framing.

2. **The count/multiset view already exists over the list.** `cnt` (`:242`),
   `remove_first_comm` (`:205`, Qed), `remove_first_eq_l1` (`:132`, Qed),
   `remove_first_L1_count_eq_self` / `_count_other`, `count_occ_le_l1_m`
   (`:279`) are all already proved. Step 1/Step 2 ("introduce the count
   operations and coordinate lemmas") are **already done** as a *view* over the
   list. The admits are therefore **not** blocked by the absence of multiset
   reasoning.

3. **The "list costume tears" story is wrong; the blocker is proof-structural.**
   The `:520` / `:565` comments ("Hfree is True (irrelevant)") are **stale** —
   leftovers from the *weak* predicate before the 2026-05-28 strict migration.
   Under the strict predicate, `expr_strictly_free_of_region r (ERegion r e)`
   **descends unconditionally** (`Syntax.v:268-270`), so in the `rr = r`
   shadowed case `Hfree : expr_strictly_free_of_region r e` is *informative*
   and `IHHt r Hfree` is available — the exact tool the *working* descend case
   already uses at `:558`. The admit case has the same tools as the case that
   compiles; it is missing a case-split, not a carrier.

4. **The real obstacle in ADMIT 1** (`T_Region_Active_L1` / `_Echo`, `rr = r`,
   `:576` / `:646`) is a case-split on `cnt r R`:
   - `cnt r R ≥ 2` → `r` survives `remove_first r R`; close via
     `T_Region_Active_L1` on the IH-shrunk body
     (`IHHt r Hfree : remove_first r R ⊢ e -| remove_first r R_body`). Needs a
     **count-preservation-under-strict-freedom** fact: a body strictly free of
     `r` leaves `cnt r` unchanged (`cnt r R_body = cnt r R`), so the rule's
     `In r R_body'` premise holds. Output reconciles via `remove_first_eq_l1`.
   - `cnt r R = 1` → `r` is *dead* after the shrink; the goal must be retyped
     with `T_Region_L1` (fresh), whose body lives at `r :: remove_first r R`.
     This needs an **L1 region-permutation-transport lemma** — the analog of
     the legacy `region_env_perm_typing` (`Semantics.v:3112`), i.e. **option
     (a)** named in the case's own comment. This is the genuinely missing
     infrastructure.

5. **What the carrier fork actually buys — and its cost.** With a count-map
   carrier and `funext`, `enter r (exit r R) = R` *as functions* whenever
   `cnt r R ≥ 1`, which dissolves the `cnt r R = 1` permutation obligation
   (the fresh rule's body input becomes literally `R`, so the original body
   derivation applies). That is the true mechanism — **not** `exit_comm; lia`,
   which only handles the arithmetic, not the rule-selection flip. The price is
   `functional_extensionality` in the L1 trusted base (visible in
   `Print Assumptions`), or a finite-map **setoid** + `Proper` instances on the
   ~1000-line `has_type_l1` inductive to stay axiom-free.

6. **ADMIT 2 is representation-independent.** `region_liveness_at_split_l1_gen`
   (`:1942`) is a *false* lemma; closing it is restatement
   (`expr_no_exit_of_region` side condition) + the ~13-site audit (Step 5/5a
   below), regardless of carrier. The carrier choice does not touch it.

### CORRECTION 2026-06-16 (later same day) — path (A) is NOT viable

I first recommended (A) "axiom-free, list carrier, port a transport lemma" and
the owner selected it. **On execution this was found to be a dead end**, for a
reason already documented in the file's own design note (`Semantics_L1.v:366-414`)
and independently re-derived by dumping the exact admit goal in `coqc`:

```
GOAL (T_Region_Active_L1, rr = r):
  remove_first r R ; G |=L1[m] ERegion r e : T -| remove_first r (remove_first_L1 r R_body) ; G'
```

The `cnt r R = 1` sub-case (r dies after the shrink) must re-type `ERegion r e`
with the **fresh** rule `T_Region_L1`, whose body lives at `r :: remove_first r R`.
Transporting the body derivation there yields an output only **multiset-equal**
to `R_body`; but the rule pops the **first list occurrence**
(`remove_first_L1`), so the goal's output is a **specific list**, and
`remove_first_L1 r` of two multiset-equal lists are themselves only
multiset-equal (`[a;r;b]` vs `[b;r;a]` → `[a;b]` vs `[b;a]`). The design note at
`:374-390` states this exactly: *"the output depends on the list structure, not
just its membership … set-equivalence (and even multiset-equivalence in some
sub-sub-cases) does not provide [list-structure agreement]."* A count/multiset
transport lemma — the keystone (A) needed — is therefore **insufficient by
construction**. Value rules also pin `R_out = R_in` *as a list*, so the judgment
is not `Permutation`-`Proper` either: you cannot bolt order-insensitivity on as a
lemma.

**Conclusion: closing ADMIT 1 requires removing the first-occurrence-list
dependence itself.** That is the owner's original committed route. The viable,
axiom-free realizations:

- **(C) count-map / finite-map carrier + setoid.** L1-only `region_env_l1`
  (legacy stays on the list). Order-free by construction; `enter∘exit = id`
  dissolves the `cnt = 1` corner. Axiom-free via a finite-map setoid + `Proper`
  instances (NOT `funext`). Largest refactor; **also the first step of the
  L1≡L3≡tropical + choreographic unification** (`project_ephapax_choreographic_tropical_foundation`).
- **(b-sorted) canonical sorted-list operations.** Keep `region_env := list`,
  but make `remove_first_L1` / the region rules operate on an *insertion-sorted*
  canonical form so list-structure ≡ multiset and equality is decidable list
  equality (no funext, no setoid). Medium refactor; does not by itself advance
  the tropical unification.
- **(B) count-map carrier + `funext`.** Smallest proof, but **+1 axiom**
  (`functional_extensionality`). Conflicts with the estate axiom-freedom posture.

**Re-surfaced to owner 2026-06-16:** I was wrong to bill (A) as a cheap close;
recommend **(C)** (axiom-free, removes first-occurrence dependence, serves the
broader unification) or **(b-sorted)** if minimal churn is preferred over the
unification payoff. ADMIT 2 (`region_liveness`) is independent of all this —
restatement + 13-site audit, doable under any option.

---

## Step 0 — the carrier change (single highest-leverage edit)  [SUPERSEDED — see REVISION above]

`Syntax.v:867`:

```coq
(* before *)
Definition region_env := list region_name.

(* after *)
Definition region_env := region_name -> nat.   (* cnt r R = re-entry depth of r; 0 = dead *)
```

A total function is preferred over a `FMap`/`list (region_name*nat)` for the
proofs: every region operation becomes a *pointwise `nat` fact*, with no
finiteness obligation and no canonical-form/sortedness bookkeeping. Equality is
`funext` (or work up to pointwise equality with a `region_env_eq` setoid to
avoid axioms — see Step 4 note).

## Step 1 — replace the four operations

| Old (list) | New (count-map) | Definition |
|---|---|---|
| `In r R` | `live R r` | `R r >= 1` |
| `r :: R` (enter) | `enter r R` | `fun r' => if String.eqb r' r then S (R r') else R r'` |
| `remove_first r R` (exit) | `exit r R` | `fun r' => if String.eqb r' r then pred (R r') else R r'` |
| `count_occ _ R r` | `cnt r R` | `R r` |

`remove_first_L1` (the TypingL1 copy) collapses into `exit` — the two are now
literally the same function, removing the list/multiset double-bookkeeping that
PRESERVATION-DESIGN §5.1 flagged.

## Step 2 — the coordinate lemmas (all `nat`-trivial, all become `Qed`)

These replace the list lemmas (`remove_first_comm`, `count_occ_le_l1_m`,
`remove_first_L1_count_eq_self`, `_count_other`). Each is one `unfold` +
`funext` + `destruct (String.eqb …)` + `lia`:

```coq
Lemma exit_comm     : forall r1 r2 R, exit r1 (exit r2 R) = exit r2 (exit r1 R).
Lemma cnt_exit_self : forall r R, cnt r (exit r R) = pred (cnt r R).
Lemma cnt_exit_other: forall r r' R, r <> r' -> cnt r' (exit r R) = cnt r' R.
Lemma cnt_enter_self: forall r R, cnt r (enter r R) = S (cnt r R).
Lemma cnt_le_exit   : forall r r' R, cnt r' (exit r R) <= cnt r' R.   (* monotonicity *)
Lemma live_exit_other: forall r r' R, r <> r' -> live R r' -> live (exit r R) r'.
```

`exit_comm` is the discharge for ADMIT 1's residual sub-cases (:572, :642): the
`rr = r` shadowed `T_Region_Active` case is now `pred (pred (R r))` either way —
order-free by construction. `cnt_le_exit` is grade-monotonicity =
`count_occ_le_l1_m` = the tropical `subsumption_transports` instance.

## Step 3 — re-thread the judgment

In `TypingL1.v` rewrite the region rules' premises/outputs in the new
vocabulary (mechanical):

- `T_Region_L1` / `T_Region_Active_L1`: `In r R` → `live R r`;
  output `remove_first_L1 r R_body` → `exit r R_body`;
  the Tofte–Talpin premise `~ In r (free_regions T)` is unchanged (it is about
  the *type*, not the env).
- `T_Loc_L1` / `T_StringNew_L1`: `In r R` → `live R r`.
- Every step rule in `Semantics_L1.v` / `Semantics.v` touching `r :: R` or
  `remove_first r R` → `enter`/`exit`.

This is the bulk of the diff (every `In`/`remove_first`/`count_occ` use across
`TypingL1.v`, `Semantics_L1.v`, `Counterexample_L2*.v`), but it is find-and-
replace plus re-running tactics; the *content* of the proofs is unchanged
except where it was fighting the list (Step 4).

## Step 4 — ADMIT 1 closes

`region_shrink_preserves_typing_l1_gen_m` (:441). The two internal admits
(:572,:642) were the shadowed `T_Region_Active_L1{,_Echo}` `rr = r` case where
list `remove_first` ordering and `remove_first_L1` disagreed. With `exit` and
`exit_comm`, the goal is `pred`-arithmetic on the `rr` coordinate plus
`cnt_exit_other` on the rest. Close with `exit_comm; cnt_exit_*; lia`. **Qed.**

> Axiom note: if `funext` is unwanted in the trusted base, carry a pointwise
> `region_env_eq` and prove the rules respect it (a `Proper` instance). Mild
> extra work; keeps `Print Assumptions` axiom-free. Decide before Step 0.

## Step 5 — ADMIT 2 repaired (the false lemma)

`region_liveness_at_split_l1_gen` (:1904) is **false as written**
(`In rv R -> In rv R'`; witness `ERegion rv (EI32 5)` at `R=[rv]` pops the only
`rv`). Restate as the *graded, conditional* form and prove from monotonicity:

```coq
(* replaces the false lemma *)
Lemma region_liveness_graded_l1 :
  forall m R G e T R' G' rv,
    R ; G |=L1[m] e : T -| R' ; G' ->
    expr_no_exit_of_region rv e ->          (* e performs no S_Region_Exit on rv *)
    live R rv -> live R' rv.
Proof.
  (* cnt rv R' = cnt rv R  when e exits rv zero times  (from cnt_le_exit + the
     exit-count being 0); live = cnt >= 1 is then preserved. *)
Qed.
```

`expr_no_exit_of_region` is the honest side-condition the *false* version
silently dropped. If a usable predicate already exists, reuse
`expr_strictly_free_of_region` (the region-shrink hypothesis is the same shape).

### Step 5a — call-site audit (the real work in ADMIT 2)

The old `region_liveness_at_split_l1_gen` axiom is consumed at ~13 sites in
`subst_typing_gen_l1*` (Semantics_L1.v ~:2140–:2291). Each must be re-checked:

1. **Served cleanly**: the site already steps a sub-expression provably free of
   `rv`-exits (it usually carries `expr_strictly_free_of_region rv …`). Thread
   `expr_no_exit_of_region` and apply `region_liveness_graded_l1`. Expect the
   majority here.
2. **Needs the threaded side-condition**: add `expr_no_exit_of_region rv` to
   the *caller's* hypotheses and discharge it from that caller's context.
3. **Genuinely unconditional**: any site that *needed* `In rv R -> In rv R'`
   with no no-exit guarantee was relying on a false statement — flag it; it is
   really an ADMIT-3 instance (the eliminator fork) in disguise, not closable
   here.

Produce a table (site :: class :: discharge) before editing; classes (1)/(2)
close ADMIT 2, class (3) sites get moved to the eliminator-fork backlog.

## Step 6 — verify

- `make -f build.mk clean && make -f build.mk` exits 0.
- `region_shrink_preserves_typing_l1_gen_m` and `region_liveness_graded_l1` end
  in `Qed`; the old false lemma is deleted (not `Admitted`).
- `Print Assumptions` for both: no `region_*` self-axioms among them; ideally no
  new axioms (modulo the `funext`/setoid decision in Step 4).
- `Counterexample.v`, `Counterexample_L2*.v` still compile (strengthening only
  shrinks the typable set; untypability witnesses are preserved).
- Net live-admit count: **4 → 2** (`step_pop` + the gated `preservation_l1`
  remain), and **zero false lemmas** (the soundness smell is gone).

## What this buys / does not buy

- **Buys**: ADMIT 1 + ADMIT 2 closed; the false lemma replaced by a true one;
  `remove_first_L1`/`remove_first` double-bookkeeping eliminated; the carrier is
  now the proven tropical/ℕ-multiset grade (re-foundation done, L1≡L3 wiring via
  EchoBridge now possible as an additive follow-on).
- **Does not buy**: closure of `step_pop` (ADMIT 3) or `preservation_l1`
  (ADMIT 4). Those are the eliminator fork — a value/eliminator depending on a
  region absent from its *result type* — and the naïve `T_Var` premise that
  would close them is **proven false**. See `L1-ELIMINATOR-FORK.md`.
