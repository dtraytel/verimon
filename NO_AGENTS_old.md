# Freeze operator notes for VeriMon

This file is a working note for implementing `Freeze` (`Frz`) in the executable monitor.

## Goal

Implement the monitor-side behavior of `Formula.Frz p phi psi` so that it matches the logical semantics in `Formula.sat`.

Relevant reference points:

- `thys/MFODL_Monitor_Devel/Formula.thy:420` - `Let` semantics
- `thys/MFODL_Monitor_Devel/Formula.thy:421` - `Freeze` semantics
- `thys/MFODL_Monitor_Devel/Monitor.thy:1315` - `minit0` for `Let`
- `thys/MFODL_Monitor_Devel/Monitor.thy:1316` - `minit0` for `Freeze`
- `thys/MFODL_Monitor_Devel/Monitor.thy:1717` - `meval` for `MLet`
- `thys/MFODL_Monitor_Devel/Monitor.thy:1721` - current placeholder for `MFrz`

## Semantics recap

`Let` and `Freeze` differ only in how the fresh predicate `p` is interpreted inside `psi`.

- `Let`:
  - inside `psi`, `p(w, j)` means: evaluate `phi` on environment `w` at the same time `j`
  - semantic equation:
    - `sat sigma V v i (Let p phi psi)`
    - `= sat sigma (V((p, nfv phi) |-> (lambda w j. sat sigma V w j phi))) v i psi`

- `Freeze`:
  - inside `psi`, `p(w, j)` means: evaluate `phi` on environment `w` at the frozen outer time `i`
  - the queried time `j` is ignored for `p`
  - semantic equation:
    - `sat sigma V v i (Frz p phi psi)`
    - `= sat sigma (V((p, nfv phi) |-> (lambda w j. sat sigma V w i phi))) v i psi`

So the important intuition is:

- `Let` exposes a time-varying derived predicate
- `Freeze` exposes a time-constant snapshot taken at the outer time point

## Informal pseudocode for `minit0`

The initialization is already in place and looks right:

```text
minit0 n (Frz p phi psi) =
  let m = nfv phi in
  MFrz p m (minit0 m phi) (minit0 n psi) 0 [] None
```

Interpretation:

- `phi` is monitored with arity `m = nfv phi`
- `psi` is monitored with the outer arity `n`
- `MFrz` needs extra state because, unlike `Let`, the monitor must remember snapshots of `phi` taken at concrete time points and replay them into `psi`
- in particular, it should track both pending frozen snapshots and any unresolved skip debt coming from ordinary `psi` outputs that arrive before the corresponding snapshots do

## Informal pseudocode for `meval`

### Baseline: `Let`

The existing `Let` case is the reference pattern:

```text
meval n ts db (MLet p m phi psi) =
  let xs, phi' = meval m ts db phi
  let ys, psi' = meval n ts (db[(p, m) := xs]) psi
  return ys, MLet p m phi' psi'
```

Why this works:

- `xs[k]` is the relation for `phi` at the `k`-th timestamp in `ts`
- `psi` can directly consume `p` pointwise on the same batch

### Envisioned behavior: `Freeze`

`Freeze` cannot use the same one-line database update as `Let`.

Reason:

- for each outer time point `i`, we first compute one snapshot `alpha = phi(i)`
- then `psi` must be monitored for the verdict at start time `i`, with `p` fixed to that same `alpha` at every global time point
- several frozen start points may be alive at the same time, so we need state across calls
- unlike the earlier suffix-based idea, `beta` may access `p` under past operators, so the frozen binding must be globally aligned, not only aligned to the suffix starting at `i`
- at the same time, `psi` also depends on the ordinary database `db` and timestamps `ts`, so its non-frozen state must be advanced on every call and persisted in the returned monitor state

Suggested informal pseudocode:

```text
meval n ts db (MFrz p m phi psi skip pending current) =
  let xs, phi' = meval m ts db phi
  let db0 = db with (p, m) deleted
  let zs0, psi' = meval n ts db0 psi
  let skip1 = skip + length zs0
  let skip2, pending1, current1 = discharge_skip skip1 (pending @ snapshots_from(xs)) current

  let zs1, current2 = meval_current (meval n) ts db0 current1
  let ys, pending2, current3 = freeze_meval (meval n) j pending1 current2 (p, m) psi'

  return zs0 @ zs1 @ ys, MFrz p m phi' psi' skip2 pending2 current3
```

Important bookkeeping point:

- `psi` and `current` are different monitor states
- `psi` is the shared template for future frozen starts, so it is advanced once to `psi'` by `meval n ts db0 psi`
- `current = Some (psi_i, alpha, ell)` is an already active frozen instance from an earlier call, so it must be advanced separately on the same real input
- there is no double-feeding as long as `meval_current` updates only the persisted `current` state, while freshly spawned frozen jobs start later from `psi'`

Equivalent per-start view:

```text
for each new timestamp i in the batch:
  alpha_i := result of phi at i
  enqueue a frozen job for start time i with snapshot alpha_i

advance the shared psi-state on the real batch input, regardless of whether any frozen output is ready

emit any rows that `psi` can already produce without consulting the frozen predicate, and skip the corresponding earliest pending frozen starts

if those starts do not yet have snapshots available, remember the remaining skip debt in the state and discharge it later when snapshots arrive; note that the active `current` job counts as the first available frozen start when present

update the active frozen job with the same ordinary `db`/`ts` information of the current batch before calling `freeze_meval`; if that update already yields the next frozen output, emit it immediately

advance the earliest unresolved frozen job under a globally constant interpretation of p

whenever that job yields the verdict for its own start time,
emit it and continue with the next queued job
```

## How this differs from `LetPast`

`LetPast` is useful as an implementation pattern because it also needs auxiliary state and iterative stepping.

But the roles differ:

- `LetPast` computes a recursive predicate whose meaning depends on previous values of the same predicate
- `Freeze` is not recursive in that way
- `Freeze` instead needs a family of `psi` evaluations, one per frozen start point, each with a constant binding for `p`

So `letpast_meval0` is a structural inspiration, not a semantic template.

## Likely interpretation of the current `MFrz` state

Current constructor in `Monitor.thy`:

```text
MFrz p m phi psi skip alphas opt
```

Plausible intended meaning:

- `skip`:
  - number of earliest frozen starts that are already resolved by the plain `psi` run
  - these starts should be discarded as soon as their snapshots become available

- `alphas`:
  - queue of frozen relations already obtained from `phi`
  - these correspond to outer time points whose `psi`-evaluation still matters
- `opt`:
  - optional currently active `psi`-instance together with the frozen relation it uses and an index telling how many replicated copies of that relation have already been supplied to it

When thinking about skip discharge, treat the state order as:

- first the active `opt`, if it is present
- then the queue `alphas`

So one unit of skip debt first eliminates the active frozen job, and only then starts consuming the queued snapshots.

The stub

```text
freeze_meval0 eval j alphas p psi0 (Some (psi, alpha, ell)) =
  eval (Mapping.empty(p := replicate (j - ell) alpha)) psi
```

should be read as follows:

- `psi` has already received `ell` copies of the frozen relation `alpha`
- the current global prefix length is `j`
- so this call only needs to supply the missing `j - ell` copies
- after that call, the updated active state should remember `ell' = j`

About access to `j`:

- the abstract `meval` already lives in a context `fixes j :: nat`, so the current prefix length / global time is available without storing it inside `MFrz`
- therefore the extra `MFrz` state only needs to remember freeze-specific information such as the unresolved skip debt, pending snapshots, and the number `ell` of already supplied frozen copies for the active instance
- storing `j` again inside `MFrz` is possible, but it would be redundant and would complicate invariants because that field would have to stay synchronized with the ambient `j`
- so the recommended design is: keep `j` external, keep `ell` internal

About shadowing when advancing the shared `psi` state:

- the plain call that advances `psi` on the real input should not see any ambient database entry for `(p, m)`
- semantically, `Frz p phi psi` binds `p` locally inside `psi`, so any outer meaning of `p` must be shadowed
- therefore, before calling `meval n ts db0 psi`, form `db0` by deleting `(p, m)` from `db` (or equivalently replacing it by an empty/unavailable stream)

Why global alignment is necessary:

- `beta` is allowed to use the frozen predicate under past operators; there are no special restrictions beyond the standard safety conditions
- therefore, when the active `psi` instance evaluates subformulas, it may still ask for the value of `p` at earlier global times
- semantically, this is harmless because `Frz` interprets `p` as a constant-in-time predicate, so the answer is always the same frozen snapshot `alpha`
- operationally, this means the active instance must receive a globally aligned stream of copies of `alpha`; however it only needs the copies that have not yet been supplied before, namely `j - ell`
- so the invariant is not "feed a suffix-local stream from the frozen start", but rather "keep extending one globally aligned constant stream and remember how much of it the current state has already consumed"

So the intended invariant is:

- the active frozen `psi` instance is evaluated in global time, not suffix-local time
- the binding for `p` is constant on the whole known prefix
- the active state stores how much of that constant stream has already been supplied
- this remains correct even when `beta` reaches `p` through nested past operators

An important implementation consequence is that the current state shape suggests a serial strategy:

- `alphas` can hold the later frozen snapshots that have been discovered but not started yet
- `skip` can record how many earliest starts should already be ignored once their snapshots eventually arrive
- `opt` can represent the earliest unresolved `psi` instance currently being advanced
- once that instance yields the next output in prefix order, the monitor can move on to the next snapshot
- the shared `psi` field of `MFrz` should nevertheless always be advanced on the real input and returned, because future frozen instances must start from the newest non-frozen monitor state
- if the shared `psi` state already yields `k` outputs on the real input, then the first `k` frozen starts are skipped, even if some of their snapshots have not yet arrived; that is what `skip` must remember

This is different from a fully parallel implementation with one live `psi` state per start point. The serial approach matches the current datatype better and is likely enough because the monitor only needs to emit the next unresolved prefix of verdicts.

## Concrete plan for `Monitor.thy`

### Suggested control flow for the abstract `MFrz` case

The missing `MFrz` branch in `meval` should probably be implemented as a helper in the same style as `letpast_meval0`, but with freeze-specific state.

Before `freeze_meval` runs, skip debt should be discharged against the currently available frozen work items. A simple helper shape is:

```text
discharge_skip skip pending current =
  if skip = 0 then
    (0, pending, current)
  else
    case current of
      Some _ => discharge_skip (skip - 1) pending None
    | None =>
        case pending of
          [] => (skip, [], None)
        | _ # pending' => discharge_skip (skip - 1) pending' None
```

Intended meaning:

- skip debt is paid off in prefix order
- if there is an active frozen job, it counts as the earliest available start and is discarded first
- only after `current` is gone do we start consuming entries from `pending`
- if both are exhausted before `skip` reaches zero, the remaining `skip` is carried in the `MFrz` state for future calls

The helper order should therefore be:

1. advance the shared `psi` state on `(ts, db0)` and keep the resulting `psi'`
2. discharge skip debt against `current` first and then `pending`
3. advance the surviving `current` state on `(ts, db0)` once, if it exists
4. call `freeze_meval` to supply only frozen copies for `(p, m)`

This ordering ensures that each persisted monitor state sees the ordinary input exactly once per call.

One workable shape is:

```text
freeze_meval eval j pending current p psi0 =
  if current = None then
    case pending of
      [] => ([], [], None)
    | alpha # pending' =>
        freeze_meval eval j pending' (Some (psi0, alpha, 0)) p psi0
  else
    let (psi_state, alpha, ell) = the current in
    let ys, psi_state' = eval (replicate (j - ell) alpha) psi_state in
    if ys = [] then
      ([], pending, Some (psi_state', alpha, j))
    else
      let y = hd ys in
      let zs, pending', current' = freeze_meval eval j pending None p psi0
      in
      (y # zs, pending', current')
```

In this version, the argument `eval` should remain the ordinary `meval` function. The current frozen state should first be updated once with the new real-input information `(ts, db0)`, and only after that should `freeze_meval` supply the missing replicated copies of the frozen relation.

So the intended pre-step is:

```text
meval_current eval ts db0 None = ([], None)
meval_current eval ts db0 (Some (psi, alpha, ell)) =
  let ys, psi' = eval ts db0 psi in
  case ys of
    [] => ([], Some (psi', alpha, ell))
  | y # _ => ([y], None)
```

Then `freeze_meval` itself is responsible only for the frozen-table update.

Crucially, `meval_current` should not create a fresh active state from `psi'`.

- if `current = Some ...`, it advances that persisted state once on the new ordinary input
- if `current = None`, it leaves it as `None`
- fresh activation happens only inside `freeze_meval`, using `psi'` as the already-real-input-updated template

This is exactly what avoids double application of `(ts, db0)` to the same state.

This deliberately keeps the helper simple:

- at most one frozen `psi` instance is active at a time
- the shared `psi` template is advanced first on the real batch input and stored back into `MFrz`
- skip debt is discharged before `freeze_meval` is called, so the helper only sees starts whose snapshots are already available
- the active frozen instance is first advanced once on the current real batch input before `freeze_meval` is entered
- if that pre-step already yields an output row, that row is emitted immediately and the active instance is cleared
- the helper itself then supplies only the missing replicated suffix of the constant stream for `p`
- the bookkeeping index `ell` records exactly how many copies of `alpha` have already been supplied to that active state
- a freshly activated instance starts with `ell = 0`, because it has not yet received any copy of its frozen stream
- once one start yields its next output, the helper may immediately switch to the next queued start
- if the active instance yields no output yet, it stays in `current` and simply waits for the next call with larger `j`

This is intentionally informal. The points that matter are:

- snapshots from `phi` are appended to `alphas` in time order
- `skip` records how many earliest frozen starts are already known to be irrelevant because `psi` has produced outputs without any frozen table
- `opt` always refers to the earliest unresolved frozen start
- the plain `psi` state is always advanced using the real `db` and `ts`, and that updated state is persisted in the returned `MFrz`
- the active frozen instance is also updated once with the new ordinary `db`/`ts` information before `freeze_meval` runs
- if that update already yields the next row for the current frozen start, the row should be emitted and `current` should become `None`
- the helper itself only has to supply the not-yet-supplied copies of the constant snapshot `alpha`
- a fresh frozen instance is created only from `psi'`, so that newly spawned work also sees the ordinary input exactly once
- when one frozen start yields its first output row, that row is the next output of `Frz`
- after producing that output, evaluation may continue immediately with the next queued snapshot on the same batch
- if no output is produced, `meval` may legitimately return `[]` for this call; the unresolved frozen job survives in the monitor state until more input arrives

This deliberately avoids any special restriction on `beta`: if `beta` contains past operators over the frozen predicate, the global alignment already gives them the right value.

Why the direct output of `meval n ts db0 psi` matters:

- those rows are the verdicts of `psi` under the ordinary database, with the local binder for `p` correctly shadowing any outer meaning of `(p, m)`
- if such a row is already produced without any frozen table being supplied, then the corresponding output of `Frz` is already determined as well
- operationally, that means the earliest pending frozen starts no longer need special handling; they can be skipped
- if the corresponding snapshots are not yet available, that skip cannot be discharged immediately and must instead be remembered as skip debt in the `MFrz` state
- at the same time, the updated monitor state `psi'` must still be preserved, because future frozen jobs must start from the newest non-frozen `psi` state

So the correct discipline is:

- evaluate `psi` first on the real input with `(p, m)` deleted from `db`
- emit the resulting rows `zs0`
- add `length zs0` to the unresolved skip debt
- discharge as much of that debt as possible against the currently available pending snapshots
- keep the updated monitor state `psi'`
- return `MFrz ... psi' ...`, not `MFrz ... psi ...`

### Why `freeze_meval` terminates

The helper can be arranged so that recursion only happens in two situations:

1. `current = None` and `pending = alpha # pending'`
   - recurse with `pending'` and `current = Some (...)`
2. `current = Some (...)` and the current frozen job has just produced its next output row
   - recurse with the same `pending` but with `current = None`

In both cases a simple lexicographic measure decreases, for example:

```text
(length pending, if current = None then 0 else 1)
```

Why this works:

- in case 1, the first component decreases because one snapshot is removed from `pending`
- in case 2, the first component stays the same but the second component decreases from `1` to `0`
- in the non-recursive case where the active job does not yet produce an output, the helper returns immediately

So `freeze_meval` does not recurse while merely "making progress inside" one active `psi` instance; it recurses only when it consumes a queued snapshot or discharges the current one.

### Recommended state invariant for the abstract monitor

Treat the runtime state as:

- `phi` = monitor for the snapshot-producing subformula
- `psi` = shared monitor state for `psi`, already advanced on all ordinary database/timestamp input seen so far
- `skip` = number of earliest frozen starts already resolved by the plain `psi` run but not yet discharged against arriving snapshots
- `alphas` = FIFO queue of frozen relations for starts that have been seen but not yet activated
- `opt = None` = no active frozen start
- `opt = Some (psi_i, alpha_i, ell_i)` = currently advancing the earliest unresolved start using snapshot `alpha_i`, after already supplying `ell_i` copies of that constant stream

When discharging `skip`, the effective prefix order is:

- the active `opt`, if present
- then the elements of `alphas`

That is why `discharge_skip` should take both `alphas` and `opt`, and should return an updated `opt` as well.

The important bookkeeping field is therefore not the frozen start index, but the supplied-prefix length.

- the current placeholder for `opt` stores too little information
- the helper really needs `ell`, the number of replicated copies already supplied to the active instance
- if a proof later needs the actual frozen start position as well, that can be reconstructed or stored additionally, but operationally `ell` is the first essential field

So before proving anything, decide whether:

1. `ell` alone is enough operationally, or
2. `MFrz` should also store the original frozen start position explicitly for proofs

For the runtime algorithm described here, `ell` is mandatory.

### First concrete coding target in `Monitor.thy`

The first implementation pass should aim for this behavior:

```text
meval n ts db (MFrz p m phi psi skip alphas opt) =
  let xs, phi' = meval m ts db phi
  let db0 = delete (p, m) db
  let zs0, psi' = meval n ts db0 psi
  let skip1 = skip + length zs0
  let skip2, alphas1, opt1 = discharge_skip skip1 (alphas @ xs) opt
  let zs1, opt2 = meval_current (meval n) ts db0 opt1
  let ys, alphas2, opt' = freeze_meval (meval n) j alphas1 opt2 (p, m) psi'
  in (zs0 @ zs1 @ ys, MFrz p m phi' psi' skip2 alphas2 opt')
```

The important operational split is:

- first update the shared `psi` state on `(ts, db0)` and store it as `psi'`
- update the optional active frozen state on `(ts, db0)` once as well, emitting its head output immediately if one appears
- then call `freeze_meval` with plain `meval`, using it only to feed the missing frozen copies for `(p, m)` into the already-real-input-updated state

So the key reconciliation is:

- old active work is updated through `meval_current`
- newly spawned work starts from `psi'`
- no state is updated twice on the same `(ts, db0)` batch

The important new point is:

- the ordinary output `zs0` of `psi'` is not discarded
- instead, it witnesses that the earliest `length zs0)` verdicts of `Frz` are already determined without the frozen predicate
- so those rows should be emitted immediately, and the first `length zs0)` frozen starts should be skipped
- if not enough snapshots are currently available, that remaining skip debt must be stored in `skip` and discharged on later calls

Even if the final code differs in detail, this should remain the intended contract.

## Concrete plan for `Monitor_Impl.thy`

`Monitor_Impl.thy` currently still reflects the old world:

- `meformula` has `MLet` and `MLetPast`, but no `MFrz`
- `Rep_meformula` therefore has no `MFrz` case
- `meeval` also has no `MFrz` branch

So mirroring the abstract logic requires three structural updates first:

1. add `MFrz` to `meformula`
2. add the corresponding `Rep_meformula` clause
3. add the `meeval` case that mirrors abstract `meval`

After that, the proof/bridge work should mirror the existing `LetPast` pattern:

- define an executable helper analogous to `letpast_meeval0`
- prove it corresponds to the abstract helper, analogous to `letpast_meeval0`
- add congruence and size lemmas so termination and code equations go through cleanly

The executable representation will likely need the same state decision as the abstract one:

- if abstract `MFrz` gets an explicit start index, `meformula.MFrz` should get the same field
- if the abstract version keeps a helper-level reconstruction of the start index, the executable version should do the same to stay lock-step with `Rep_meformula`

In other words, do not try to improvise a different executable state shape unless there is a strong code-generation reason.

## Working hypothesis for `Progress.thy`

For the globally aligned algorithm, the progress equation for `Freeze` should reflect two facts:

- a start time `i` is usable only once the snapshot `phi(i)` is known
- once that snapshot exists, the frozen predicate `p` is available to `psi` at every queried time in the current prefix

So the right first candidate is:

```text
progress P (Formula.Frz p phi psi) j =
  min (progress P phi j)
      (progress (P((p, nfv phi) |-> j)) psi j)
```

More explicitly, the intended per-start reading is:

```text
for an outer position i,
the frozen predicate behaves inside psi like
  if i < progress P phi j then j else 0
```

This is the user's intuition in operational form: if the snapshot at start `i` is already known, then `p` is available everywhere in the current prefix; otherwise the frozen binding is not available yet.

Why this fits the globally aligned story:

- `progress P phi j` bounds how many frozen start points already have a snapshot available
- for any such start point, `p` is then semantically known at all times in the current prefix, because `p(w, t)` ignores `t` and always returns the same frozen snapshot
- therefore, inside `psi`, the derived predicate should behave like a predicate whose progress is already `j`
- the final `min` expresses that both conditions must hold: the snapshot for the start must exist, and `psi` itself must be evaluable with that globally available frozen predicate

Why the displayed equation still uses a plain `min` instead of an explicit `if ... then j else 0` inside the map update:

- the existing progress map stores one natural number per predicate symbol, not a start-position-dependent function
- so it cannot directly express "for starts below `progress phi j` give `j`, otherwise give `0`"
- the outer `min (progress P phi j) ...` is the compact way to enforce exactly that only the first `progress P phi j` frozen starts may contribute outputs
- in other words, the piecewise intuition is semantically right, and the displayed equation is the corresponding compressed bookkeeping form

This is different from `Let`:

- `Let` gives `p` only the progress of `phi`, because `p` at time `t` depends on `phi` at the same time `t`
- `Freeze` gives `p` progress `j` inside `psi`, because once the snapshot at the frozen start is known, the same relation is valid at every queried time in the current prefix

Sanity check:

- for `Frz p phi (Pred p)`, the equation gives `min (progress phi j) j = progress phi j`, as expected
- for `Frz p phi (Next (Pred p))`, the equation gives `min (progress phi j) (j - 1)`, which matches the intended meaning: once the snapshot at start `i` exists, the `Next` query only needs more trace, not more progress of `phi`

### Expected proof shape in `Progress.thy`

Two places should gain a `Frz` case:

- the `progress` function itself
- the semantic preservation lemma that currently has explicit `Let` and `LetPast` cases

For the semantic preservation proof, the `Frz` case should still be close to the `Let` proof, but with a different progress bound for the distinguished predicate:

- `Let`: the predicate entry for `p` in the progress map is `progress P phi j`
- `Frz`: the predicate entry for `p` in the progress map is `j`, but only for outer times below `progress P phi j`
- when `(p', n) = (p, nfv phi)`, use the induction hypothesis for `phi` at the frozen outer time, not at the queried inner time

That is the key semantic difference the proof needs to remember.

More concretely, the future `Frz` proof should likely be organized as follows:

1. unfold `sat` for `Formula.Frz`
2. instantiate the induction hypothesis for `psi` under the updated interpretation
   `V((p, nfv phi) |-> (lambda w j. sat sigma V w i phi))`
3. show that the updated progress environment is admissible:
   - the distinguished predicate has progress `j` inside `psi`
   - the outer `min (progress P phi j) ...` guarantees that we only claim correctness for frozen start points whose snapshot already exists
4. in the distinguished predicate subcase `(p', n) = (p, nfv phi)`, prove
   `sat sigma V w i phi = sat sigma V' w i phi`
   by applying the induction hypothesis for `phi` at the frozen outer time `i`
5. in the non-distinguished predicate subcase, fall back to the ambient preservation assumption exactly as in `Let`

So the proof obligation is not really a different recursion pattern; it is the same `Let`-style proof skeleton, but with:

- a stronger local availability assumption for `p` inside `psi` (`j` instead of `progress phi j`)
- an outer cap by `progress phi j` to ensure only starts with available snapshots are counted

## Working hypothesis for `Correctness.thy`

`Correctness.thy` currently has `wf_mformula` constructors for `MLet` and `MLetPast`, but no constructor for `MFrz`.

The `Freeze` proof will probably need more than a one-line clone of `wf_mformula.Let`, because the monitor state contains delayed snapshots and an optional active frozen instance.

### Recommended proof decomposition

Use the same overall strategy as `LetPast`:

1. define a helper-level invariant for the freeze worker
2. prove an initialization lemma for that invariant
3. prove a step lemma that preserves the invariant across one helper iteration
4. derive a postcondition describing the emitted rows and updated freeze state
5. use that postcondition inside the main `meval` correctness proof for `MFrz`

Suggested names:

- `freeze_meval_invar`
- `freeze_meval_post`
- `freeze_meval_invar_init`
- `freeze_meval_invar_step`
- `freeze_meval_invar_post`

### What the freeze invariant should record

At minimum, the invariant should connect runtime state with semantic objects:

- each relation in `alphas` corresponds to some already-computed snapshot of `phi'`
- these snapshots are ordered by their original start times
- `opt = Some (...)` means the earliest unresolved start is being evaluated against `psi'`
- the active `psi` monitor is well-formed under the frozen interpretation
  `V((p, m) |-> (lambda w j. sat sigma V w k phi'))`
  for its own start time `k`
- any rows already emitted by the helper correspond exactly to the next output prefix of `Formula.Frz p phi' psi'`

This is the central difference from `LetPast`:

- `LetPast` tracks a recursively defined predicate value
- `Freeze` tracks a queue of concrete snapshot relations and one active monitor instance parameterized by a fixed start time

### Shape of the future `wf_mformula.Frz` rule

Expect the final rule to say, informally:

```text
wf_mformula sigma j P V n R phi_m phi'
wf_frz_state sigma j P V p m phi' psi' alphas opt
safe side conditions
----------------------------------------------
wf_mformula sigma j P V n R (MFrz p m phi_m psi_m alphas opt) (Formula.Frz p phi' psi')
```

with `wf_frz_state` packaging the queue/current-instance obligations.

Trying to encode all of that directly into a single constructor premise list will likely make later proofs harder. A dedicated auxiliary predicate is the cleaner route.

## Practical implementation plan

1. Keep `minit0` as-is unless the `MFrz` state shape needs refinement.
2. Finish the abstract `MFrz` case in `thys/MFODL_Monitor_Devel/Monitor.thy`.
3. Mirror the same logic in `thys/MFODL_Monitor_Devel/Monitor_Impl.thy`.
4. Add the missing progress/accounting story for `Frz` in `thys/MFODL_Monitor_Devel/Progress.thy` if needed by the correctness proof.
5. Extend correctness lemmas in `thys/MFODL_Monitor_Devel/Correctness.thy` analogously to the existing `Let` / `LetPast` structure.

## First deliverable

For the first task, it is enough to keep the implementation informal and document the intended runtime story:

- `phi` is evaluated on the current batch
- each result row of `phi` creates a frozen snapshot
- `psi` is evaluated relative to that snapshot, with `p` constant over time
- unfinished frozen instances survive in the monitor state
- emitted results are aligned with the original frozen start times

That informal story should be treated as the contract before proving anything.
