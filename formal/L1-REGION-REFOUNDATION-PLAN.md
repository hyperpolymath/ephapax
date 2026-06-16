<!-- SPDX-License-Identifier: MPL-2.0 -->
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

## Step 0 — the carrier change (single highest-leverage edit)

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
