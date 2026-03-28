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

The step is:

```text
xs      := meval phi on current batch
db0     := update (p,m) with [] in db
zs0     := meval psi on current batch and db0
skip1   := skip + length zs0
(skip2, alphas1) := discharge_skip skip1 (alphas @ xs)
(ys, alphas2)    := freeze_meval0 (meval [] ) j alphas1 (p,m) psi'
result  := zs0 @ ys
state'  := MFrz p m phi' psi' skip2 alphas2
```

The key semantic fact is that `zs0` and `ys` play different roles:

- `zs0` advances the shared template and may increase semantic `Frz` progress
  before the corresponding snapshots are available
- `ys` is produced by replaying concrete snapshots through `freeze_meval0`

So the proof must follow this operational split directly.

## Proof objects to keep

These are still the right basic objects in `Correctness.thy`:

- `frz_qtable sigma V m phi k X`
- `wf_frz_queue sigma V m phi ks Xs`
- `wf_frz_state sigma j P V p m phi psi skip Xs`

## Recommended new invariant

The most promising reading now is:

```text
jphi = progress P phi j
jfrz = progress P (Frz p phi psi) j

skip = jfrz - jphi
wf_frz_queue sigma V m phi [jfrz ..< jphi] Xs
```

Interpretation:

- `jfrz` is semantic `Frz` progress: the first unresolved output position
- `jphi` is snapshot availability progress: the first start whose `phi` snapshot
  is not yet available
- `Xs` stores the available snapshots for unresolved starts in `[jfrz ..< jphi)`
- `skip = jfrz - jphi` is debt, so it is positive exactly when semantic `Frz`
  progress already runs ahead of available snapshots
- consequently, `skip > 0` should imply `Xs = []` as a derived fact rather than
  as the primary invariant shape

Why this looks better than the additive invariant:

- the plain shared-`psi` run advances semantic `Frz` progress by `length zs0`
- if snapshots are still missing, that progress should show up as debt
- newly arriving snapshots from `phi` reduce debt through `discharge_skip`
- replay consumes the earliest currently available unresolved snapshots
- this avoids the earlier tension where combining the frontier equation with the
  natural semantic progress equation forced `skip1 = skip0`

## Revised `wf_mformula.Frz` invariant

The `Frz` constructor should still use two different binder-progress assumptions
for the stored `psi` monitor:

```text
wf_mformula sigma j P V m UNIV phi phi'
wf_mformula sigma j (P((p,m) |-> 0)) (V((p,m) |-> bot)) n R psi psi'
wf_frz_state sigma j P V p m phi' psi' skip Xs
...
```

Why `0` for the shared run:

- the shared `psi` template is advanced on `db0 = Mapping.update (p,m) [] db`
- operationally this means the local binder is present but has empty information during that run
- so the progress of `(p,m)` for the plain/shared run should be `0`, not `j`

Why `bot` for the shared semantic environment:

- the shared run now really is a standard `wf_envs` instance for
  `P((p,m) |-> 0)` and `V((p,m) |-> bot)`
- this matches `Mapping.update (p,m) [] db` directly, so the main `MFrz` proof can
  reuse the ordinary induction hypothesis for `psi`

## High-level correctness skeleton

The `MFrz` branch of `meval_correct` should be reproved in five layers.

### 1. Refactor the invariant layer

Change `wf_frz_state_def` so it records:

```text
skip = progress Frz j - progress phi j
wf_frz_queue ... [progress Frz j ..< progress phi j] Xs
```

Then immediately reprove the basic lemmas:

- `wf_frz_state_Nil`
- `wf_frz_state_skipD`

Expected shape:

- `wf_frz_state_Nil` should express `progress Frz j = progress phi j + skip`
- `wf_frz_state_skipD` should follow from `skip > 0 => progress phi j < progress Frz j`, hence the queue interval is empty

### 2. Rebuild the queue extension layer

Interpret `xs` as new snapshots and append them to the available queue.

Target lemma:

```text
frz_available_queue_extend:
  wf_frz_state ... skip Xs
  /\ phi rows xs
  ==> wf_frz_queue ... [progress Frz j ..< progress phi' (j + d)] (Xs @ xs)
```

Reason:

- under the new invariant, the queue is indexed by the semantic unresolved range
  that already has snapshots available
- appending new `phi` rows should simply extend the right endpoint from `jphi` to `jphi'`

### 3. Rebuild the discharge layer

`discharge_skip` is now best understood as consuming debt against the front of the
available queue.

Target lemma:

```text
frz_queue_after_discharge:
  discharge_skip (skip + length zs0) (Xs @ xs) = (skip', Xs')
  ==> wf_frz_queue ... [progress Frz j + length zs0 - skip' ..< progress phi' (j + d)] Xs'
```

Intuition:

- the plain shared run advances semantic `Frz` progress by `length zs0`
- `skip'` records how much of that new semantic progress is still ahead of
  snapshot availability after discharging against the newly available queue
- so the first available unresolved snapshot after discharge should be at
  `progress Frz j + length zs0 - skip'`

This is the key bridge from debt accounting to replay.

### 4. Reconnect replay

Reuse the exact replay worker lemmas:

- `freeze_meval0_post_exact`
- `freeze_meval0D`

Target lemma:

```text
frz_queue_after_replay:
  freeze_meval0 ... = (ys, Xs')
  ==> wf_frz_queue ... [progress Frz j + length zs0 + length ys - skip' ..< progress phi' (j + d)] Xs'
```

Reason:

- replay consumes exactly `length ys` earliest available unresolved snapshots
- `freeze_meval0D` should also provide the maximality fact needed later for the
  output proof: the first residual snapshot does not yet yield another replay row

### 5. Prove the semantic progress update

Now prove the real semantic lemma:

```text
progress Frz' = progress Frz + length zs0 + length ys
```

This should use:

- the shared-template output rows `zs0`
- the replay rows `ys`
- the maximality part of `freeze_meval0D`
- the `Frz` progress definition in `Progress.thy`

This is the semantic statement that the old additive invariant kept fighting.

### 6. Reconstruct the post-state invariant

Combine the queue-after-replay lemma with the semantic progress equation to show:

```text
skip' = progress Frz' - progress phi'
wf_frz_queue ... [progress Frz' ..< progress phi'] alphas'
```

This should replace the current fragile frontier/accounting lemma entirely.

## Immediate Isabelle plan

In `Correctness.thy`, the practical order should be:

1. restore / confirm the file is back on the additive invariant before editing
2. change only `wf_frz_state_def`, `wf_frz_state_Nil`, `wf_frz_state_skipD`
3. rework `wf_frz_queue_extend` to the new `[jfrz..<jphi']` shape
4. replace `discharge_skip_wf_frz_state` with a discharge lemma stated in terms of
   `jfrz + length zs0 - skip'`
5. rebuild `frz_replay_residual_exact` on top of that new discharge lemma
6. delete the current `frz_progress_frontier` goal and replace it by the real
   semantic progress lemma
7. finally reprove `frz_full_state_step` and `frz_output_step`

## Dead ends / things not to repeat

- do not try to reuse the old additive frontier lemma under the new invariant
- do not prove `zs0` as if the plain `psi` run were already a replay run
- do not force the post-state exact interval before the new debt interpretation
  has been propagated through extend, discharge, and replay
