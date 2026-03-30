# Interactive Proof Session: Close T_Case/T_If

## Setup

```bash
cd /var/mnt/eclipse/repos/nextgen-languages/ephapax/formal
# Open in CoqIDE or vscoq:
coqide -R . Ephapax Semantics.v
# Or: code Semantics.v  (with vscoq extension, add -R . Ephapax to settings)
```

## What to do

### Step 1: Navigate to line ~932

Find the `all: admit.` inside `no_consumption_at_true_linear`.
Step through the proof until you reach the T_Case bullet.

### Step 2: At T_Case goal, run these tactics one at a time:

```coq
(* After stepping past all the closed cases, you should be at T_Case *)
- inversion H2; subst.
  (* NOW: Look at the proof context. You should see:
     - IHe1 : ... (IH for scrutinee e)
     - IHe2 : ... (IH for branch e1)
     - IHe3 : ... (IH for branch e2)
     - Some typing hypothesis for the second derivation's branches

     Write down the EXACT names you see. Then: *)

  (* Apply IH for branch e1 at shifted index S i *)
  eapply IHe2 with (i0 := S i).  (* or whatever the IH parameter is named *)
  (* Fill each subgoal — the pattern is:
     - is_linear_ty T0 = true  → assumption
     - ctx_lookup (ctx_extend G' T1) (S i) = Some (T0, true)  → simpl; eapply flags_monotone; eassumption
     - ctx_lookup ((T1, true) :: G_final) (S i) = Some (T0, true)  → simpl; assumption
     - ctx_types_agree (ctx_extend G' T1) (ctx_extend G2' T1)  → apply ctx_extend_types_agree; eapply typing_preserves_types_agree; eassumption
     - ctx_lookup (ctx_extend G2' T1) (S i) = Some (T0, false)  → simpl; eapply IHe1; eassumption
     - The typing derivation for the second branch  → eassumption
  *)
```

### Step 3: Same for T_If (simpler — no binder shift)

```coq
- inversion H2; subst.
  eapply IHe2; try eassumption.
  + eapply typing_preserves_types_agree; eassumption.
  + eapply flags_monotone; eassumption.
  + eapply IHe1; eassumption.
```

### Step 4: Check remaining admits

After T_Case and T_If are closed, the `all: admit.` should have fewer goals.
If any remain, they're binding cases (T_Let, T_LetLin) that follow the same
S i pattern as T_Case.

### Step 5: Propagate to other theorems

Once `no_consumption_at_true_linear` is Qed:
- `typing_ctx_transfer` uses it — may close more cases
- `subst_preserves_typing` has independent binding issues
- `preservation` depends on both

## Key lemmas available

- `typing_preserves_types_agree` : threading types_agree through a derivation
- `flags_monotone` : flags only increase (false→true, never true→false)
- `ctx_extend_types_agree` : extending preserves types_agree
- `ctx_extend_false_preserved` : extending preserves false_preserved
- `ctx_lookup_extend_succ` : ctx_lookup (ctx_extend G T) (S i) = ctx_lookup G i
- `consumption_chain` : consumption composes through two derivations

## The critical insight

The IH is quantified over `i` (we generalized it). For binding cases:
- Original context has `(T0, true)` at position `i`
- Extended context `(T1, false) :: G` has `(T0, true)` at position `S i`
- The IH at `S i` gives the result at `S i` in the output
- `ctx_lookup ((T1, ??) :: G_final) (S i) = ctx_lookup G_final i`

This is why the generalization was necessary.
