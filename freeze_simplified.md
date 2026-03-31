# Simplified Freeze proof plan

This note keeps only the current proof plan for `Formula.Frz` / `MFrz` in the
simplified runtime.

## Runtime we are proving

The monitor state is

```text
MFrz p m phi psi jfrz jpsi0 jphi alphas
```

with meaning:

- `phi`: submonitor producing frozen snapshots
- `psi`: shared template monitor, advanced on ordinary input only
- `jfrz`: current progress of `Frz p phi psi` (= number of output tables produced)
- `jpsi0`: current progress of ψ under `P(pn↦0)` (= how far the shared ψ-run has advanced)
- `jphi`: current progress of φ (= how many snapshots have been produced)
- `alphas`: pending snapshots that still need replay

The step is (Monitor.thy line 1733):

```text
xs       := meval phi on current batch           -- xs covers [jphi..jphi')
db0      := update (p,m) with [] in db
zs0      := meval psi on current batch and db0   -- zs0 covers [jpsi0..jpsi0')
zs0_out  := drop (jfrz - jpsi0) zs0              -- trim: only [jfrz..jpsi0')
jpsi0'   := jpsi0 + |zs0|
alphas1  := drop (jfrz - jphi + |zs0_out|) (alphas @ xs)
(ys, alphas') := freeze_meval0 (frz_meval ...) alphas1
jphi'    := jphi + |xs|
jfrz'    := jfrz + |zs0_out| + |ys|
result   := zs0_out @ ys
state'   := MFrz p m phi' psi' jfrz' jpsi0' jphi' alphas'
```

### Why three progress values?

The old design stored `skip = jfrz - jphi` and relied on `discharge_skip` to
thread the leftover skip through the queue. This was both:
- **Incorrect**: it discharged too few elements (missing the skip gap), and
- **Unnecessary**: with three explicit progress values, the skip is always
  computable as `jfrz - jphi`, and the discharge reduces to plain `drop`.

The `discharge_skip` function has been removed from Monitor.thy entirely.

### Key definitions

**`freeze_meval0`** (Monitor.thy line 1679): Takes `eval :: 'a → 'b list × 'c`
and a list of alphas:

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

**`frz_meval`** (Correctness.thy): Abbreviation capturing the replay call:

```text
frz_meval n p m j db ψ ≡
  (λα. meval j n []
    (Mapping.update (p, m) (replicate j α) (Mapping.map_values (λ_ _. []) db)) ψ)
```

**MFrz call site** (Monitor.thy line 1733): Uses a lambda directly:

```text
(ys, αs') = freeze_meval0
  (λα. meval n [] (Mapping.update (p, m) (replicate j α)
    (Mapping.map_values (λ_ _. []) db)) ψ) αs
```

Key design choice: `Mapping.map_values (λ_ _. []) db` instead of `Mapping.empty`.
This ensures all predicate keys present in `db` have `[]` entries, which is
essential for constructing a valid `wf_envs` for the replay call.

## Proof objects

These are the basic objects in `Correctness.thy`:

- `frz_qtable sigma V m phi k X` — a single snapshot table at time k
- `wf_frz_queue sigma V m phi ks Xs` — queue of snapshots with key indices
- `wf_frz_state sigma j P V p m phi psi jphi Xs` — full freeze state invariant

Definition of `wf_frz_state` (to be updated):

```text
wf_frz_state σ j P V p m φ ψ jphi Xs =
  (let jfrz = progress σ P (Formula.Frz p φ ψ) j
   in jphi = progress σ P φ j ∧ wf_frz_queue σ V m φ [jfrz..<jphi] Xs)
```

Note: `jphi` is now stored explicitly in the MFrz state and passed to the
invariant. The invariant asserts that `jphi` matches `progress σ P φ j`.
The interval `[jfrz..<jphi]` is the range of snapshot indices in the queue.
When `jfrz ≥ jphi`, this is empty and `Xs = []`.

## Invariant (`wf_mformula.Frz`)

```text
wf_mformula σ j P V m UNIV φ φ'
∀i. wf_mformula σ j (P((p,m) ↦ 0)) (V((p,m) ↦ λw k. sat σ V w i φ')) n R ψ ψ'
wf_frz_state σ j P V p m φ' ψ' jphi αs
jfrz = progress σ P (Frz p φ' ψ') j
jpsi0 = progress σ (P((p,m) ↦ 0)) ψ' j
{0..<m} ⊆ fv φ'    m = nfv φ'    safe φ'    safe ψ'
⟹ wf_mformula σ j P V n R (MFrz p m φ ψ jfrz jpsi0 jphi αs) (Formula.Frz p φ' ψ')
```

- `P((p,m) ↦ 0)` because the shared ψ run sees empty `[]` for predicate `(p,m)`
- `V((p,m) ↦ ⊥)` is semantically irrelevant when `P(pn)=0` (see V-insensitivity below)
- `jfrz` and `jpsi0` are stored but must equal their semantic definitions

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

## Existing proved lemmas (status uncertain — many need updating)

In Correctness.thy (may be broken by the design change, need checking):
- `wf_frz_state_Nil`, `wf_frz_state_skipD` — may need reformulation
- `wf_frz_queue_discharge_skip`, `wf_frz_queue_after_discharge` — discharge_skip gone, need drop versions
- `discharge_skip_alt`, `discharge_skip_eq` — REMOVE (discharge_skip gone)
- `discharge_skip_frontier_eq`, `discharge_skip_frontier_le_phi` — REMOVE or reformulate
- `wf_frz_queue_length` — likely still valid
- `freeze_meval0D` (3 conclusions: queue drop, replay rows, replay stop) — likely still valid
- `freeze_meval0_post_exact` — likely still valid
- `frz_replay_skip_empty` — needs reformulation (no skip)
- `wf_envs_update_Nil`, `wf_envs_update3` — likely still valid
- `frz_discharge_skip_nat` — REMOVE (discharge_skip gone)
- `frz_step_post` — REWRITE entirely
- `meval_correct` MFrz case — REWRITE entirely

## THE INDEX ALIGNMENT PROBLEM (critical discovery)

### The problem

The `psi_rows` assumption gives tables `zs0` at indices:
```
[jpsi0 ..< jpsi0']  where  jpsi0 = progress(P(pn↦0)) ψ j,  jpsi0' = progress(P'(pn↦0)) ψ (j+δ)
```

The Frz output requires tables at indices:
```
[jfrz ..< jfrz + |zs0_out|]  where  jfrz = progress σ P (Frz p φ ψ) j
```

Since `zs0_out = drop (jfrz - jpsi0) zs0`, the output tables are at indices
`[jfrz ..< jpsi0')` (the tail of the shared-run range starting at jfrz).

**If `jfrz > jpsi0`**: the `drop` trims the first `jfrz - jpsi0` tables from `zs0`.
The remaining tables are at the correct indices `[jfrz ..< jpsi0')`.

### Analysis of when `jfrz = jpsi0`

From the LEAST definition, `jfrz = jpsi0` iff `jpsi0` satisfies the LEAST
condition at `i = jpsi0`:
- **Case A** (`jpsi0 ≥ jphi`): condition becomes `jpsi0 ≤ jpsi0` ✓, so `jfrz = jpsi0`.
- **Case B** (`jpsi0 < jphi`): condition becomes `jpsij ≤ jpsi0`, true iff `jpsij = jpsi0`.

Case B fails when increasing P(pn) from 0 to j changes ψ's progress.

### Key saving grace: when `jfrz > jpsi0`, `|zs0_out| = 0` may hold

When `jfrz > jpsi0` (Case B with `jpsij > jpsi0`), the ψ-progress with P(pn↦0)
may be "stuck" — `jpsi0' = jpsi0` and thus `|zs0| = 0`, making `zs0_out` empty too.

**What needs to be proved**: Either
1. `jfrz = jpsi0` directly (under the proof invariants), or
2. `jfrz > jpsi0 ⟹ |zs0_out| = 0` (making the zs0 part vacuous)

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

### V-insensitivity at the `wf_mformula` level

For the REPLAY IH (applying `IHψ_new` for sorry 2), we need to convert
`wf_mformula σ (j+δ) (P'(pn↦0)) (V(pn↦⊥)) n R ψ_new ψ1` to
`wf_mformula σ (j+δ) (P'(pn↦0)) (V(pn↦f)) n R ψ_new ψ1` for some f.

This requires a `wf_mformula`-level V-insensitivity lemma:
```
P pn = Some 0  ⟹  wf_mformula σ j P V n R ψ ψ1
  ⟹  wf_mformula σ j P (V(pn := x)) n R ψ ψ1
```

This needs to be proved by induction over `wf_mformula` (~25 cases).

## Proof strategy for sorry 2 (`frz_prog_eq`)

### Proof plan

1. From `wf_envs_empty`: get `wf_envs S σ (j+δ) 0 P' P' V db_empty`
2. Apply `wf_envs_update`: get wf_envs for `P'(pn↦(j+δ))` with
   `replicate (j+δ) α` in the db, using `V(pn↦f_frozen)`
3. Apply V-insensitivity: convert `wf_mformula ... (V(pn↦⊥)) ... ψ_new ...`
   to `wf_mformula ... (V(pn↦f_frozen)) ... ψ_new ...`
4. Apply `IHψ_new` to get: output length = `jpsij' - jpsi0'`
5. Use `replay_rows` / `replay_stop` for all-or-nothing reasoning
6. Combine with LEAST properties of jfrz/jfrz' to prove the equation

## Proof strategy for sorry 1 (semantic output rows)

### Approach: split into zs0_out and ys via `list_all2_appendI`

```text
1. list_all2 (λi. qtable ...) [jfrz..< jfrz + |zs0_out|] zs0_out
2. list_all2 (λi. qtable ...) [jfrz + |zs0_out|..< jfrz'] ys
```

### For `zs0_out` portion

**Sat conversion** (the shared-run tables have the right semantics by V-insensitivity):
- `psi_rows` gives: `qtable n (FV ψ) (mem_restr R) (λv. sat σ V(pn↦⊥) v i ψ)`
- Need: `qtable n (FV (Frz p φ ψ)) (mem_restr R) (λv. sat σ V v i (Frz p φ ψ))`
- By V-insensitivity at P(pn↦0): the two are equivalent for i < jpsi0'

### For `ys` portion

Each row comes from a replay call with a frozen snapshot. Construct `wf_envs`
with the frozen binding, apply V-insensitivity, then `IHψ_new`.

## Nat arithmetic reminder

All frontier arithmetic is over natural numbers, not integers.

- `jfrz - jphi` is nat subtraction, so it truncates at `0`
- `drop (jfrz - jphi + |zs0_out|) (αs @ xs)` — the drop amount is always ≥ 0
  since it's a nat expression
- When `jphi ≥ jfrz`, we have `jfrz - jphi = 0`, so we drop only `|zs0_out|`
- When `jphi < jfrz`, we have `αs = []` (positive "skip" means no pending snapshots),
  so we drop `(jfrz - jphi + |zs0_out|)` from `[] @ xs = xs`

## Key lemmas in other files

- `sat_prefix_conv_gen` (Progress.thy line 2152): general V-insensitivity.
- `not_contains_pred_progress` (Progress.thy line 582)
- `not_contains_pred_sat` (Formula.thy line 912)
- `progress_le_gen`: `pred_mapping (λx. x ≤ j) P ⟹ progress P φ j ≤ j`
- `progress_mono_gen`: monotonicity of progress in P and j
- `wf_envs_empty` (Correct_Until.thy line 32)
- `wf_envs_update` (Correct_Until.thy line 36)

## Dead ends / things not to repeat

- do not try to reuse the old additive frontier lemma under the new invariant
- do not prove `zs0` as if the plain `psi` run were already a replay run
- do not force the post-state exact interval before the new debt interpretation
  has been propagated through extend, discharge, and replay
- do not use `Mapping.empty` for the replay db — use `Mapping.map_values (λ_ _. []) db`
- do not assume `sat σ V(pn↦⊥) v i ψ = sat σ V(pn↦f) v (i+d) ψ` for d>0 —
  V-insensitivity does NOT give temporal shifting
- do not try to split sorry 1 without first resolving the index alignment problem
- the `safe_formula` for Frz has NO `not_contains_pred` restriction on ψ, so ψ
  CAN reference pn — V-insensitivity is necessary, not just `not_contains_pred_sat`
- do not use `discharge_skip` — it has been removed; use plain `drop` instead
