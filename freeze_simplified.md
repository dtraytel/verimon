# Simplified Freeze proof story

This note records the final proof story for `Formula.Frz` / `MFrz` in the
simplified runtime.

## Runtime being proved

The freeze monitor state is

```text
MFrz p m phi psi jfrz jpsi0 jphi alphas
```

with meaning:

- `phi`: submonitor producing frozen snapshot tables
- `psi`: shared template monitor advanced on ordinary input only
- `jfrz`: current progress of `Frz p phi psi`
- `jpsi0`: current progress of `psi` under `P((p,m) ↦ 0)`
- `jphi`: current progress of `phi`
- `alphas`: pending snapshots that still need replay

The step is:

```text
xs       := meval phi on current batch              -- xs covers [jphi..<jphi')
zs0      := meval psi on current batch with P(pn)=0 -- zs0 covers [jpsi0..<jpsi0')
zs0_out  := drop (jfrz - jpsi0) zs0                 -- keep only [jfrz..<jpsi0')
jpsi0'   := jpsi0 + |zs0|
alphas1  := drop (jfrz - jphi + |zs0_out|) (alphas @ xs)
(ys, alphas') := freeze_meval0 (frz_meval ...) (jfrz - jpsi0') alphas1
jphi'    := jphi + |xs|
jfrz'    := jfrz + |zs0_out| + |ys|
result   := zs0_out @ ys
state'   := MFrz p m phi' psi' jfrz' jpsi0' jphi' alphas'
```

## Implementation fix that mattered

The `freeze_meval0` call in `Monitor.thy` originally started its counter at `0`.
That is wrong when `jfrz > jpsi0'`: the replay output must start at the offset
`jfrz - jpsi0'` inside each replay run.

The correct call is therefore:

```text
freeze_meval0 ... (jfrz - jpsi0') alphas1
```

Equivalently in the actual code path, the fix was to replace the old initial
counter `0` with `(jfrz - jpsi0)` at the call site after `jpsi0'` is encoded via
the running state values.

This is the only algorithmic bug that had to be fixed in `Monitor.thy`.

## Core invariants

The proof uses three basic objects in `Correctness.thy`:

```text
frz_qtable σ V m φ k X
wf_frz_queue σ V m φ ks Xs
wf_frz_state σ j P V p m φ ψ jphi Xs
```

with:

```text
frz_qtable σ V m φ k X =
  qtable m (Formula.fv φ) (mem_restr UNIV) (λv. Formula.sat σ V (map the v) k φ) X

wf_frz_queue σ V m φ ks Xs =
  list_all2 (λk X. frz_qtable σ V m φ k X) ks Xs

wf_frz_state σ j P V p m φ ψ jphi Xs =
  (let jphi0 = progress σ P φ j;
       jfrz0 = progress σ P (Formula.Frz p φ ψ) j
   in jphi = jphi0 ∧ wf_frz_queue σ V m φ [jfrz0..<jphi0] Xs)
```

So the queue always stores exactly the snapshot interval `[jfrz..<jphi)`.
When `jfrz ≥ jphi`, that interval is empty and the queue is empty.

## Progress facts that drive the proof

Let:

```text
jphi   = progress σ P φ j
jphi'  = progress σ P' φ (j + δ)
jpsi0  = progress σ (P(pn ↦ 0)) ψ j
jpsi0' = progress σ (P'(pn ↦ 0)) ψ (j + δ)
jpsij' = progress σ (P'(pn ↦ j + δ)) ψ (j + δ)
jfrz   = progress σ P (Frz p φ ψ) j
jfrz'  = progress σ P' (Frz p φ ψ) (j + δ)
```

The key facts are:

- `jpsi0 ≤ jfrz`
- if `jfrz > jphi`, then `jfrz = jpsi0`
- `jfrz ≤ jpsij'`
- `jfrz' ≤ jpsij'`
- `jfrz' = (if jpsij' < jphi' then jpsij' else if jpsi0' ≤ jphi' then jphi' else jpsi0')`
- `jfrz' = jfrz + |zs0_out| + |ys|`

Define:

```text
M = jfrz + |zs0_out| = max jfrz jpsi0'
```

Then the final output interval splits cleanly as:

```text
[jfrz..<jfrz') = [jfrz..<M] @ [M..<jfrz')
```

The first part is produced by the shared `psi` run (`zs0_out`), and the second
part by replaying queued snapshots (`ys`).

## Why V-insensitivity is necessary

For `Frz`, semantics is:

```text
sat σ V v i (Frz p φ ψ) =
  sat σ (V((p, nfv φ) ↦ λw j. sat σ V w i φ)) v i ψ
```

So replay rows use a valuation where `pn = (p, m)` is interpreted by a frozen
snapshot function.

The shared `psi` run, however, uses `P(pn) = 0`. At indices below
`progress σ (P(pn ↦ 0)) ψ ...`, the actual value of `V(pn)` is irrelevant, because
the premise in `sat_prefix_conv_gen` for `pn` is vacuous when `P(pn) = 0`.

This is exactly what allows:

- `zs0_out` rows to be converted from `psi` tables to `Frz` tables, and
- replay calls to be analyzed using the induction hypothesis with the correct
  frozen valuation.

The convenient wrapper lemma used in the finished proof is `sat_V_cong`.

## Main structural split of the output proof

The semantic output proof is split into two `list_all2` pieces:

```text
1. zs0_out_rows : [jfrz..<M]
2. ys_rows      : [M..<jfrz')
```

Then `list_all2_appendI` combines them into the full interval
`[jfrz..<jfrz')`.

### Part A: `zs0_out_rows`

This part comes from the shared `psi` run:

- `IHψ2` gives rows for `zs0` on `[jpsi0..<jpsi0')`
- dropping `jfrz - jpsi0` entries gives rows for `zs0_out` on `[jfrz..<jpsi0')`
- `|zs0_out| = jpsi0' - jfrz`, so `[jfrz..<jpsi0') = [jfrz..<M]`
- `sat_V_cong` converts the `psi`-valuation to the `Frz` valuation

This proves that `zs0_out` supplies exactly the left prefix of the freeze
output interval.

### Part B: `ys_rows`

This is the replay portion and was the last part to finish.

The structure is:

1. `freeze_meval0_diagonal` gives the diagonal description of `ys`:

   ```text
   ys ! i = fst (frz_meval ... (alphas1 ! i)) ! (k0 + i)
   ```

   with `k0 = jfrz - jpsi0'` in the proof state.

2. `queue_αs1_B` shows `alphas1` is a well-formed queue over `[M..<jphi')`, so
   each `alphas1 ! i` is a correct `φ`-table at index `M + i`.

3. Applying `IHψ_new` to `alphas1 ! i` yields replay rows for `ψ1` on
   `[jpsi0'..<jpsij')` under the frozen valuation for index `M + i`.

4. The diagonal index `k0 + i` selects exactly the replay row at semantic index
   `M + i`, because:

   ```text
   jpsi0' + k0 = M
   ```

5. Unfolding `Formula.sat` for `Frz` converts that `ψ1` table into the desired
   `Frz` table at index `M + i`.

6. Since `jfrz' = M + |ys|`, these rows cover exactly `[M..<jfrz')`.

That completes `ys_rows`.

## The arithmetic issue that mattered

One subtle point was important in the final proof script:

The identity

```text
length (alphas @ xs) = jphi' - jfrz
```

is **not valid unconditionally**.

It holds only when `jfrz ≤ jphi`. When `jfrz > jphi`, the old queue interval is
empty, `alphas = []`, and the right way to reason is directly from `xs`, not via
that concatenation formula.

This forced a case split in the proof of:

- `len_αs1_B`, and
- `queue_αs1_B`

The repaired proof handles the two cases as follows:

- **Case `jfrz ≤ jphi`**: concatenate old and new queues, then drop.
- **Case `jfrz > jphi`**: use `jfrz = jpsi0`, infer `alphas = []`, and work
  directly from the new queue `xs`.

This was the main proof restructuring needed after the algorithmic fix.

## Final post-state facts

The finished proof establishes:

- `frz_prog_eq`: `jfrz' = jfrz + |zs0_out| + |ys|`
- `frz_step_post`: the post-state queue invariant for `alphas'`
- semantic output correctness for `zs0_out @ ys` on `[jfrz..<jfrz')`
- re-establishment of `wf_mformula` for the updated `MFrz` state

So the `MFrz` case of `meval_correct` is now fully proved.

## What to remember

- The runtime is correct with the drop-based queue discipline.
- The only monitor bug was the initial replay counter passed to `freeze_meval0`.
- `M = max jfrz jpsi0'` is the key boundary between shared-run output and replay
  output.
- `sat_V_cong` / V-insensitivity is essential because `ψ` may still reference
  `pn`; there is no `not_contains_pred` shortcut here.
- The queue proof must split on `jfrz ≤ jphi` vs `jfrz > jphi`.
