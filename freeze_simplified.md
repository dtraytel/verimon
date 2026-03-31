# Simplified Freeze proof plan

This note keeps only the current proof plan for `Formula.Frz` / `MFrz` in the
simplified runtime.

## Runtime we are proving

The monitor state is

```text
MFrz p m phi psi skip alphas
```

with meaning:

- `phi`: submonitor producing frozen snapshots
- `psi`: shared template monitor, advanced on ordinary input only
- `skip`: unresolved debt between semantic `Frz` progress and snapshot availability
- `alphas`: pending snapshots that still need replay

The step is (Monitor.thy line 1733):

```text
xs      := meval phi on current batch
db0     := update (p,m) with [] in db
zs0     := meval psi on current batch and db0
(skip1, alphas1) := discharge_skip (skip + length zs0) (alphas @ xs)
(ys, alphas2)    := freeze_meval0 (frz_meval ...) alphas1
result  := zs0 @ ys
state'  := MFrz p m phi' psi' skip1 alphas2
```

### Key definitions (refactored)

**`freeze_meval0`** (Monitor.thy line 1684): Simplified to take just `eval :: 'a → 'b list × 'c`
and a list of alphas. No more embedded `j`, `p`, `φ0`, `db0` parameters:

```text
freeze_meval0 eval [] = ([], [])
freeze_meval0 eval (α # αs) =
  (let (ys, _) = eval α in
    case ys of
      [] => ([], α # αs)
    | y # _ =>
        (let (zs, αs') = freeze_meval0 eval αs
        in (y # zs, αs')))
```

**`frz_meval`** (Correctness.thy line 1459): Abbreviation capturing the replay call:

```text
frz_meval n p m j db ψ ≡
  (λα. meval j n []
    (Mapping.update (p, m) (replicate j α) (Mapping.map_values (λ_ _. []) db)) ψ)
```

**MFrz call site** (Monitor.thy line 1738): Uses a lambda directly:

```text
(ys, αs') = freeze_meval0
  (λα. meval n [] (Mapping.update (p, m) (replicate j α)
    (Mapping.map_values (λ_ _. []) db)) ψ) αs
```

Key change from previous sessions: `Mapping.empty` is replaced by
`Mapping.map_values (λ_ _. []) db`, which ensures all predicate keys present in
`db` have `[]` entries. This is essential for constructing a valid `wf_envs` for
the replay call.

## Proof objects

These are the right basic objects in `Correctness.thy`:

- `frz_qtable sigma V m phi k X`
- `wf_frz_queue sigma V m phi ks Xs`
- `wf_frz_state sigma j P V p m phi psi skip Xs`

Definition of `wf_frz_state` (line 55):

```text
skip = jfrz - jphi ∧ wf_frz_queue σ V m φ [jfrz..<jphi] Xs
```
where `jfrz = progress σ P (Formula.Frz p φ ψ) j` and `jphi = progress σ P φ j`.

## Invariant (`wf_mformula.Frz`, line 107)

```text
wf_mformula σ j P V m UNIV φ φ'
wf_mformula σ j (P((p,m) ↦ 0)) (V((p,m) ↦ ⊥)) n R ψ ψ'
wf_frz_state σ j P V p m φ' ψ' skip Xs
{0..<m} ⊆ fv φ'    m = nfv φ'    safe φ'    safe ψ'
```

- `P((p,m) ↦ 0)` because the shared ψ run sees empty `[]` for predicate `(p,m)`
- `V((p,m) ↦ ⊥)` means `V((p,m) := Some(λ_ _. False))` — V(pn) is semantically
  irrelevant when P(pn)=0 (see V-insensitivity below)

## Progress definition for Frz

From Progress.thy line 81:

```text
progress P (Formula.Frz p φ ψ) j =
  (let pn = (p, nfv φ) in
   (LEAST i. i ≤ j ∧ progress (P(pn ↦ (if i < progress P φ j then j else 0))) ψ j ≤ i))
```

Let `jpsi0 = progress(P(pn↦0)) ψ j`, `jpsij = progress(P(pn↦j)) ψ j`, `jphi = progress P φ j`.

From the LEAST definition:
- **Case 1** (`jpsij < jphi`): `jfrz = jpsij`
- **Case 2a** (`jpsij ≥ jphi`, `jpsi0 ≤ jphi`): `jfrz = jphi`
- **Case 2b** (`jpsij ≥ jphi`, `jpsi0 > jphi`): `jfrz = jpsi0`

Always: **`jpsi0 ≤ jfrz`** (proved in earlier REPL sessions).

## Sat for Frz

From Formula.thy line 421:

```text
sat σ V v i (Frz p φ ψ) = sat σ (V((p, nfv φ) ↦ λw j. sat σ V w i φ)) v i ψ
```

Key: uses frozen outer time `i` inside φ, not queried time `j`.

## Existing proved lemmas (no sorry)

In Correctness.thy:
- `wf_frz_state_Nil`, `wf_frz_state_skipD`
- `wf_frz_queue_discharge_skip`, `wf_frz_queue_after_discharge`
- `discharge_skip_alt`, `discharge_skip_eq`
- `discharge_skip_frontier_eq`, `discharge_skip_frontier_le_phi`
- `wf_frz_queue_length`
- `freeze_meval0D` (3 conclusions: queue drop, replay rows, replay stop)
- `freeze_meval0_post_exact`
- `frz_replay_skip_empty`, `wf_envs_update_Nil`
- `frz_discharge_skip_nat`
- `frz_step_post` first conclusion (wf_frz_state post) — PROVED
- `meval_correct` MFrz case skeleton — uses frz_step_post at line 1905/1919

## Current sorry positions (2 remaining)

### Sorry 1 (line 1710 in `frz_step_post`)

```text
list_all2 (λi. qtable n (FV (Formula.Frz p φ ψ)) (mem_restr R)
  (λv. ⟨σ, V, v, i⟩ ⊨ᴹ Formula.Frz p φ ψ))
  [progress σ P (Formula.Frz p φ ψ) j ..< progress σ P' (Formula.Frz p φ ψ) (j+δ)]
  (zs0 @ ys)
```

This requires showing that each output row `zs0[k]` and `ys[k]` has the right
semantic content. For `zs0`, the rows come from the shared ψ run with V(pn)=⊥.
For `ys`, the rows come from replay calls through `frz_meval`.

### Sorry 2 (line 1890 in `meval_correct`)

```text
progress σ P' (Formula.Frz p φ1 ψ1) (j+δ) =
  progress σ P (Formula.Frz p φ1 ψ1) j + length zs0 + length ys
```

This is the fundamental progress equation.

## THE INDEX ALIGNMENT PROBLEM (critical discovery)

### The problem

The `psi_rows` assumption gives tables `zs0` at indices:
```
[jpsi0 ..< jpsi0']  where  jpsi0 = progress(P(pn↦0)) ψ j,  jpsi0' = progress(P'(pn↦0)) ψ (j+δ)
```

The Frz output requires tables at indices:
```
[jfrz ..< jfrz + |zs0|]  where  jfrz = progress σ P (Frz p φ ψ) j
```

Since `|zs0| = jpsi0' - jpsi0`, these ranges differ by the offset `jfrz - jpsi0`.

**If `jfrz > jpsi0`**: the same physical tables `zs0` would need to be valid at
DIFFERENT time indices, which requires both V-insensitivity AND temporal invariance
of sat — a very strong requirement that does NOT hold in general.

### Analysis of when `jfrz = jpsi0`

From the LEAST definition, `jfrz = jpsi0` iff `jpsi0` satisfies the LEAST
condition at `i = jpsi0`:
- **Case A** (`jpsi0 ≥ jphi`): condition becomes `jpsi0 ≤ jpsi0` ✓, so `jfrz = jpsi0`.
- **Case B** (`jpsi0 < jphi`): condition becomes `jpsij ≤ jpsi0`, true iff `jpsij = jpsi0`.

Case B fails when increasing P(pn) from 0 to j changes ψ's progress (i.e.,
`jpsij > jpsi0`). This happens exactly when ψ's progress depends on pn.

### Key saving grace: when `jfrz > jpsi0`, `|zs0| = 0`

**Empirical observation** (verified on many examples, NOT formally proved):

When `jfrz > jpsi0` (Case B with `jpsij > jpsi0`), the ψ-progress with P(pn↦0)
is "stuck" — it doesn't advance between steps. Specifically, `jpsi0' = jpsi0`
and thus `|zs0| = 0`.

**Why this should hold**: When `jpsij > jpsi0`, it means pn IS a bottleneck in ψ.
With P(pn)=0, the pn-dependent paths in ψ have progress bounded by a small constant
(at most the nesting depth of Prev/Since around pn lookups). This bound is
INDEPENDENT of j, so both `progress(P(pn↦0)) ψ j` and `progress(P'(pn↦0)) ψ (j+δ)`
hit the same constant bound, giving `jpsi0' = jpsi0`.

**Examples verified**:
- `ψ = Pred pn ts`: `jpsi0 = 0`, `jpsi0' = 0`, `|zs0| = 0` ✓
- `ψ = And (Pred q ts1) (Pred pn ts2)`: `jpsi0 = 0`, `jpsi0' = 0` ✓
- `ψ = Prev I (Pred pn ts)`: `jpsi0 = min(1,j)`, `jpsi0' = min(1,j+δ) = jpsi0` ✓
- `ψ = Since (Eq t1 t2) I (Pred pn ts)`: `jpsi0 ∈ {0,1}`, constant ✓

**What needs to be proved**: Either
1. `jfrz = jpsi0` directly (under the proof invariants), or
2. `jfrz > jpsi0 ⟹ jpsi0' = jpsi0` (making `|zs0| = 0` and the zs0 part vacuous)

Either result makes the zs0 index alignment problem disappear.

## V-INSENSITIVITY via `sat_prefix_conv_gen`

### The key tool

`sat_prefix_conv_gen` (Progress.thy line 2152) provides V-insensitivity at the sat level:

```text
i < progress σ P φ (plen π)  ⟹  dom V = dom V'  ⟹  dom P = dom V  ⟹
pred_mapping (λx. x ≤ plen π) P  ⟹
(⋀p n v k. (p,n) ∈ dom V ⟹ k < the (P (p,n)) ⟹ n = length v ⟹
  the (V (p,n)) v k = the (V' (p,n)) v k)  ⟹
sat σ V v i φ ⟷ sat σ' V' v i φ
```

**Application to Frz**: With P_ψ = P(pn↦0), V₁ = V(pn↦⊥), V₂ = V(pn↦f):
- For pn: the condition is `∀k < the(P_ψ pn). ...`. Since `the(P_ψ pn) = 0`,
  this is **vacuously true** for any f.
- For other predicates: V₁ and V₂ agree.

**Result**: For `i < progress σ (P(pn↦0)) ψ (plen π)`:
```
sat σ V(pn↦⊥) v i ψ = sat σ V(pn↦f) v i ψ
```
for ANY f. This means the value of V(pn) is semantically irrelevant at these indices.

**Coverage**: This applies to all `i` in `[jpsi0..< jpsi0']` (the psi_rows range).
For the Frz output range `[jfrz..< jfrz + |zs0|]`, coverage requires
`jfrz + |zs0| ≤ jpsi0'`, i.e., `jfrz ≤ jpsi0` (since `|zs0| = jpsi0' - jpsi0`).
This is exactly the `jfrz = jpsi0` condition.

### V-insensitivity at the `wf_mformula` level

For the REPLAY IH (applying `IHψ_new` for sorry 2), we need to convert
`wf_mformula σ (j+δ) (P'(pn↦0)) (V(pn↦⊥)) n R ψ_new ψ1` to
`wf_mformula σ (j+δ) (P'(pn↦0)) (V(pn↦f)) n R ψ_new ψ1` for some f.

This requires a `wf_mformula`-level V-insensitivity lemma:
```
P pn = Some 0  ⟹  wf_mformula σ j P V n R ψ ψ1
  ⟹  wf_mformula σ j P (V(pn := x)) n R ψ ψ1
```

This was previously inserted as a sorry and then removed. It still needs to be
proved (by induction over `wf_mformula`, ~25 cases). The proof sketch:
- When P(pn)=0, no data committed for pn, so V(pn) never appears in any
  non-vacuous buffer/auxiliary-data condition.
- Each wf_mformula constructor stores `list_all2 ... qtable` conditions
  referencing `sat σ V v i φ`. Use `sat_prefix_conv_gen` (vacuously at pn)
  to show these are insensitive to V(pn).
- For recursive wf_mformula calls with P unchanged: use IH directly.
- For recursive calls with P(pn) overwritten (Let, Frz, LetPast): V(pn)
  is also overwritten, so the change to V(pn) at the outer level is irrelevant.

## `sat_prefix_conv` for Frz (Progress.thy line 2212)

The Frz case of `sat_prefix_conv_gen` establishes:

For `i < progress σ P (Frz p φ ψ) (plen π)`:
- Let `q = if i < progress P φ (plen π) then plen π else 0`
- Then `i < progress σ (P(pn↦q)) ψ (plen π)` (proved by contradiction via `Least_le`)
- The IH for ψ is applied with the updated progress map P(pn↦q)
- When `(p',n) = pn` and `k < the(P(pn↦q) pn)`: we get `i < progress P φ (plen π)`,
  and the IH for φ at the FROZEN time `i` gives `sat σ V w i φ = sat σ' V' w i φ`

**Key insight**: The progress of the frozen predicate inside ψ is either `plen π`
(full prefix, when the snapshot at time `i` exists) or `0` (when it doesn't).
This is STRONGER than the `Let` case where the predicate progress is just
`progress P φ (plen π)`.

## Proof strategy for sorry 2 (`frz_prog_eq`)

### Available facts in the MFrz case

- `IHψ_new`: induction hypothesis for ψ_new (the updated ψ monitor after the shared run)
- `wf_envs_empty`: `wf_envs S σ j δ P P' V db ⟹ wf_envs S σ (j+δ) 0 P' P' V (map_values (λ_ _. []) db)`
- `wf_envs_update_Nil`: updates wf_envs with a new pred at progress 0
- `replay_rows`, `replay_stop` from `freeze_meval0D`

### Proof plan

1. From `wf_envs_empty`: get `wf_envs S σ (j+δ) 0 P' P' V db_empty`
2. Apply `wf_envs_update` or custom: get wf_envs for `P'(pn↦(j+δ))` with
   `replicate (j+δ) α` in the db, using `V(pn↦f_frozen)` where
   `f_frozen = λw k. sat σ V w i_frozen φ1`
3. Apply V-insensitivity: convert `wf_mformula ... (V(pn↦⊥)) ... ψ_new ...`
   to `wf_mformula ... (V(pn↦f_frozen)) ... ψ_new ...`
4. Apply `IHψ_new` to get: output length = `jpsij' - jpsi0'`
   (progress(P'(pn↦j+δ)) ψ1 (j+δ) - progress(P'(pn↦0)) ψ1 (j+δ))
5. Use `replay_rows` / `replay_stop` for all-or-nothing:
   each replay call uses the SAME ψ_new state, so either ALL produce ≥1 row
   or NONE do. So `length ys ∈ {0, length alphas1}`.
6. Combine with LEAST properties of jfrz/jfrz' to prove the equation.

**Note**: This plan requires V-insensitivity at the `wf_mformula` level (step 3).
It also requires careful reasoning about the LEAST properties (step 6).

## Proof strategy for sorry 1 (semantic output rows)

### Approach: split into zs0 and ys via `list_all2_appendI`

The goal splits into two subgoals (verified in REPL):

```text
1. list_all2 (λi. qtable ...) [jfrz..< jfrz + |zs0|] zs0
2. list_all2 (λi. qtable ...) [jfrz + |zs0|..< jfrz'] ys
```

### For `zs0` portion

**Prerequisites** (must resolve the index alignment problem first):
- Either prove `jfrz = jpsi0` or prove `|zs0| = 0` when `jfrz > jpsi0`
- If `jfrz = jpsi0`: the psi_rows range matches the target range exactly

**Sat conversion** (assuming index ranges match):
- `psi_rows` gives: `qtable n (FV ψ) (mem_restr R) (λv. sat σ V(pn↦⊥) (map the v) i ψ)`
- Need: `qtable n (FV (Frz p φ ψ)) (mem_restr R) (λv. sat σ V (map the v) i (Frz p φ ψ))`
- Unfold Frz sat: need `sat σ V(pn ↦ λw j. sat σ V w i φ) (map the v) i ψ`
- By V-insensitivity (`sat_prefix_conv_gen` at P(pn↦0)):
  `sat σ V(pn↦⊥) v i ψ = sat σ V(pn ↦ f) v i ψ` for `i < jpsi0'`
- Also need `FV (Frz p φ ψ) = FV ψ` (or a suitable superset relationship)

### For `ys` portion

Each row `ys[k]` comes from a replay call:
```text
meval (j+δ) n [] (Mapping.update pn (replicate (j+δ) α_k) db_empty) ψ_new
```
where `α_k = alphas1[k]` is the frozen snapshot at some start index `i_k`.

Need to show the first output row satisfies:
```
qtable n (FV (Frz p φ ψ)) (mem_restr R) (λv. sat σ V v i_k (Frz p φ ψ))
```

This requires:
1. Constructing `wf_envs` for the replay call with V(pn ↦ λw j. sat σ V w i_k φ)
2. Applying V-insensitivity to convert ψ_new's wf_mformula to the new V
3. Applying IHψ_new to characterize the replay output
4. The first output row satisfies `sat σ V(pn ↦ f_frozen) v i_k ψ` which equals
   `sat σ V v i_k (Frz p φ ψ)` by the Frz sat definition

**The replay "all-or-nothing" property**: Since all replay calls use the SAME
ψ_new state, they either ALL produce ≥1 output row or NONE do. This comes from
the structure of `freeze_meval0` and the fact that `meval` is deterministic.

## Nat arithmetic reminder

All frontier/debt arithmetic here is over natural numbers, not integers.

- `skip = jfrz - jphi` is nat subtraction, so it truncates at `0`
- `jfrz + extra - skip'` must be manipulated with nat lemmas, not by informal
  integer cancellation
- the useful normal form for the discharge frontier is
  `a - (a - b) = min a b`
  instantiated with
  `a = jfrz + extra` and `b = jphi'`
- whenever a proof step "looks obvious by subtraction", first check which side is
  known to be `<=` the other, or rewrite via `min`

## Key lemmas in other files

- `sat_prefix_conv_gen` (Progress.thy line 2152): general V-insensitivity / prefix
  preservation lemma. **Critical for both sorries**.
- `not_contains_pred_progress` (Progress.thy line 582): `¬ contains_pred p φ ⟹ progress (P(p↦x)) φ j = progress P φ j`
- `not_contains_pred_sat` (Formula.thy line 912): `¬ contains_pred p φ ⟹ sat σ (V(p ↦ x)) v i φ = sat σ V v i φ`
- `progress_le_gen`: `pred_mapping (λx. x ≤ j) P ⟹ progress P φ j ≤ j`
- `progress_mono_gen`: monotonicity of progress in P and j
- `sat_prefix_conv` for Frz (Progress.thy line 2212): semantic preservation for Frz
- `wf_envs_empty` (Correct_Until.thy line 32): produces wf_envs with 0 delta
- `wf_envs_update` (Correct_Until.thy line 36): extends wf_envs with a new predicate binding
- `wf_envs_update_sup` (Correct_Until.thy line 83): variant for LetPast

## Relevant files / directories

- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Correctness.thy` — main proof file; **2 sorries at lines 1710 and 1890**
- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Monitor.thy` — `freeze_meval0` (line 1684), `meval` MFrz case (line 1733), `frz_meval` abbreviation is in Correctness.thy
- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Progress.thy` — progress for Frz (line 81), `not_contains_pred_progress` (line 582), `sat_prefix_conv_gen` (line 2152), Frz case of `sat_prefix_conv_gen` (line 2212)
- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Formula.thy` — `Formula.Frz` (line 170), `sat` for `Frz` (line 421), `not_contains_pred_sat` (line 912), `contains_pred` for Frz (line 375)
- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Safety.thy` — `safe_formula` for Frz (line 730): `{0..<nfv φ} ⊆ fv φ ∧ safe φ ∧ safe ψ` (NO `not_contains_pred` constraint on ψ)
- `/Users/kfx532/repos/verimon/thys/MFODL_Monitor_Devel/Correct_Until.thy` — `wf_envs` (line 17), `wf_envs_empty` (line 32), `wf_envs_update` (line 36)

## Recommended attack order

1. **Resolve the index alignment problem** (prerequisite for both sorries):
   - Prove `jfrz = jpsi0` under proof invariants, OR
   - Prove `jfrz > jpsi0 ⟹ jpsi0' = jpsi0` (making `|zs0| = 0` and zs0 part vacuous)
   - This may require a general property of `progress` when one predicate has progress 0

2. **Prove `wf_mformula_V_upd_zero`** (V-insensitivity at wf_mformula level):
   - When `P pn = Some 0`, `wf_mformula σ j P V n R ψ ψ1 ⟹ wf_mformula σ j P (V(pn:=x)) n R ψ ψ1`
   - Induction over `wf_mformula` (~25 cases)
   - Use `sat_prefix_conv_gen` for buffer predicates

3. **Prove sorry 2 (`frz_prog_eq`)**: the progress equation
   - Requires V-insensitivity (step 2) and replay characterization via IHψ_new
   - Key: construct wf_envs for replay, apply IHψ_new, reason about LEAST

4. **Prove sorry 1 (`list_all2`)**: the semantic output correctness
   - Split into zs0 and ys parts via `list_all2_appendI` (verified in REPL)
   - zs0 part: V-insensitivity via `sat_prefix_conv_gen` (requires index alignment from step 1)
   - ys part: replay semantics via IHψ_new application

## Dead ends / things not to repeat

- do not try to reuse the old additive frontier lemma under the new invariant
- do not prove `zs0` as if the plain `psi` run were already a replay run
- do not force the post-state exact interval before the new debt interpretation
  has been propagated through extend, discharge, and replay
- do not use `Mapping.empty` for the replay db — use `Mapping.map_values (λ_ _. []) db`
  (this was the key refactoring that unblocked the proof)
- do not assume `sat σ V(pn↦⊥) v i ψ = sat σ V(pn↦f) v (i+d) ψ` for d>0 —
  V-insensitivity does NOT give temporal shifting
- do not try to split sorry 1 without first resolving the index alignment problem
- the `safe_formula` for Frz has NO `not_contains_pred` restriction on ψ, so ψ
  CAN reference pn — V-insensitivity is necessary, not just `not_contains_pred_sat`
