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
- `skip`: unresolved skip debt created by plain `psi` outputs
- `alphas`: pending snapshots that still need replay

The step is:

```text
xs      := meval phi on current batch
db0     := delete (p,m) from db
zs0     := meval psi on current batch and db0
skip1   := skip + length zs0
(skip2, alphas1) := discharge_skip skip1 (alphas @ xs)
(ys, alphas2)    := freeze_meval0 (meval [] ) j alphas1 (p,m) psi'
result  := zs0 @ ys
state'  := MFrz p m phi' psi' skip2 alphas2
```

The key semantic fact is that `zs0` and `ys` play different roles:

- `zs0` advances the shared template and creates skip debt
- `ys` is produced by replaying concrete snapshots through `freeze_meval0`

So the proof must follow this operational split directly.

## Proof objects to keep

These are still the right basic objects in `Correctness.thy`:

- `frz_qtable sigma V m phi k X`
- `wf_frz_queue sigma V m phi ks Xs`
- `wf_frz_state sigma j P V p m phi psi skip Xs`

Current intended reading of `wf_frz_state`:

```text
jphi = progress P phi j
jfrz = progress P (Frz p phi psi) j

jfrz + skip <= jphi
wf_frz_queue sigma V m phi [jfrz + skip ..< jphi] Xs
skip > 0 --> Xs = []
```

Interpretation:

- `progress Frz j` is the first unresolved frozen start
- `skip` counts how many starts after that are already discharged by plain `psi`
- `Xs` stores the remaining snapshots for starts in `[jfrz + skip ..< jphi)`

## Revised `wf_mformula.Frz` invariant

The `Frz` constructor should use two different binder-progress assumptions for
the stored `psi` monitor.

Recommended shape:

```text
wf_mformula sigma j P V m UNIV phi phi'
wf_mformula sigma j (P((p,m) |-> 0)) (V((p,m) |-> frz_sat {})) n R psi psi'
wf_frz_state sigma j P V p m phi' psi' skip Xs
...
```

Why `0` for the shared run:

- the shared `psi` template is advanced on `db0 = Mapping.delete (p,m) db`
- operationally this means no frozen information is available during that run
- so the progress of `(p,m)` for the plain/shared run should be `0`, not `j`

Why there is no quantified replay premise in the invariant:

- `freeze_meval0` starts from the stored shared template but does not store any
  replay-derived monitor state back into `MFrz`
- so replay well-formedness is not part of the persisted monitor invariant
- it should instead be proved on demand by worker-specific helper lemmas in the
  `MFrz` branch, from the stored shared template plus the concrete snapshot

## High-level correctness skeleton

The `MFrz` branch of `meval_correct` should be proved in four layers.

### 1. Phi step

Reuse the ordinary induction hypothesis for `phi` exactly as in `Let`.

Target facts:

- `phi_step`: `phi'` remains well-formed
- `xs` is a list of `qtable`s for indices
  `[progress P phi j ..< progress P' phi (j + d)]`

This is already standard.

### 2. Queue update layer

Interpret `xs` as new snapshots and append them to the old queue.

Needed lemmas:

- old queue from `wf_frz_state`
- append lemma turning old queue plus `xs` into a queue for the larger index range
- `discharge_skip` lemmas:
  - residual queue is still a `wf_frz_queue`
  - `skip' > 0 --> Xs' = []`

Important point:

- at this layer we only need an existential residual queue description after
  `discharge_skip`
- we do **not** need to reconstruct the exact interval immediately

So the next helper shape is the right one:

```text
frz_queue_step:
  discharge_skip skip (Xs @ Ys) = (skip', Xs')
  ==> exists ks.
        wf_frz_queue ... ks Xs'
      /\ (forall k in set ks. k < progress P' phi (j + d))
```

This is enough for `freeze_meval0_post`.

### 3. Replay worker layer

`freeze_meval0` is the real freeze-specific worker.

Its postcondition should only talk about:

- residual snapshots still semantically justified
- a size bound saying replay consumes at most one queue element per output

Shape:

```text
freeze_meval0_post:
  wf_frz_queue ... ks xs
  /\ (forall k in set ks. k < progress P phi j)
  ==> residual snapshots are still justified
  /\ length ys + length xs' <= length xs
```

This lemma should stay worker-local. It should not mention the full `Frz`
formula directly.

### 4. Main `MFrz` branch

The main branch should combine five facts:

1. `phi_step`
2. plain `psi` step on `db0`
3. skip accounting through `length zs0`
4. queue preservation through `frz_queue_step`
5. replay postcondition through `freeze_meval0_post`

The proof should then split into two obligations.

#### 4a. New monitor state

Show the returned monitor is well-formed:

```text
wf_mformula ... (MFrz ... phi' psi' skip' alphas') (Frz p phi psi)
```

This should use:

- updated `phi` monitor from `phi_step`
- updated shared `psi` template from the plain `psi` run under `(p,m) |-> 0`
- replay-specific well-formedness proved only when `freeze_meval0` actually
  tries a concrete snapshot
- a repaired freeze-state invariant for `(skip', alphas')`

This is the place where a real successor to `frz_state_step` is needed.

#### 4b. Output stream

Show the returned rows correspond to

```text
[progress P (Frz p phi psi) j ..< progress P' (Frz p phi psi) (j + d)]
```

This must be decomposed as:

- `zs0`: the earliest prefix already determined without replay
- `ys`: the next prefix obtained by replaying the queue

So the semantic statement must be proved in the same prefix order as the code.
Do not try to prove `zs0` by pretending the plain `psi` run already used the
final frozen interpretation.

## What still needs to be formalized

The remaining missing ingredient is a good replacement for the current
`frz_state_step` goal.

The present exact-interval invariant is probably too rigid for the immediate
post-`discharge_skip` proof. The clean route is:

1. keep `frz_queue_step` existential,
2. prove replay correctness from that existential queue fact,
3. only afterwards decide whether `wf_frz_state` should
   - be reconstructed from extra progress facts, or
   - be weakened to an existential-queue version.

Current recommendation:

- do **not** force exact interval reconstruction until the output proof makes
  clear which indexing fact is actually needed.
- first formalize the final `MFrz` branch around `queue_step`, `replay_step`,
  and the plain-`psi` skip contribution.

In particular, keep the two proof tracks separate:

- shared-template lemmas use binder progress `0`
- replay lemmas are derived on demand for the concrete snapshot currently tried
- `wf_frz_state` is the bridge that records when concrete snapshots are
  available to move from the shared track to the replay track

## Dead ends / things that did not work

### 1. Empty-shadow congruence

Dead end:

```text
meval ... (Mapping.delete (p,m) db) psi
= meval ... (Mapping.update (p,m) empty_stream ...) psi
```

Why it failed:

- it is stronger than the proof needs
- it treats `Frz` like a fake `Let`
- it ignores the actual queue-based runtime split

### 2. `wf_envs_frz_delete`

Dead end: trying to make the deleted database directly satisfy a `wf_envs`
statement for the updated binder.

Why it failed:

- `wf_envs` requires database coverage for the whole progress domain
- `Mapping.delete (p,m) db` intentionally removes that key
- the shared `psi` run on `db0` is therefore not itself the right object for a
  generic `wf_envs` update lemma

### 3. Treating the plain `psi` run as a frozen run

Dead end: proving `zs0` by reusing `meval_correct` as if `psi` were already run
under the final frozen interpretation.

Why it failed:

- operationally false: the plain run creates skip debt, it does not replay a
  snapshot
- the real outputs of `Frz` come from `zs0 @ ys`, not from `zs0` alone

### 4. Reconstructing the exact queue interval too early

Dead end: forcing the residual queue after `discharge_skip` into the exact range
`[progress Frz j + skip' ..< progress phi (j+d))` before the final output proof
was in place.

Why it failed:

- the algebra is brittle
- the replay worker only needs an existential queue with valid snapshot indices
- exact reconstruction should be postponed until it is proven necessary
