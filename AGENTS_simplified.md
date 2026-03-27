# Simplified Freeze operator notes for VeriMon

This file records a simpler runtime design for `Freeze` (`Frz`) than the one in `AGENTS.md`.

The key simplification is:

- do not persist an active frozen `current` job across calls
- if a frozen attempt does not yet yield output, keep its snapshot in `pending`
- try again later when the ambient prefix length `j` has increased

This is now reflected directly in `Monitor.thy`: `MFrz` no longer stores an `opt/current` field at all.

## Semantics recap

`Freeze` differs from `Let` only in how the fresh predicate `p` is interpreted inside `psi`.

- `Let` exposes a time-varying derived predicate
- `Freeze` exposes a time-constant snapshot taken at the outer start time

So for `Freeze`, each pending snapshot `alpha` should be replayed into `psi` as a constant table stream for `(p, m)`.

## Simplified state story

Current constructor shape in `Monitor.thy`:

```text
MFrz p m phi psi skip alphas
```

Interpretation:

- `skip` = unresolved skip debt from plain `psi` outputs
- `alphas` = pending frozen snapshots still to be tried

So the live state is just `skip` plus the queue `alphas`, together with the shared `psi` template.

## Informal pseudocode for `minit0`

```text
minit0 n (Frz p phi psi) =
  let m = nfv phi in
  MFrz p m (minit0 m phi) (minit0 n psi) 0 []
```

## Informal pseudocode for `meval`

```text
meval n ts db (MFrz p m phi psi skip pending) =
  let xs, phi' = meval m ts db phi
  let db0 = db with (p, m) deleted
  let zs0, psi' = meval n ts db0 psi
  let skip1 = skip + length zs0

  let skip2, pending1 = discharge_skip skip1 (pending @ snapshots_from(xs))
  let ys, pending2 = freeze_meval (meval n []) j pending1 (p, m) psi'

  return zs0 @ ys, MFrz p m phi' psi' skip2 pending2
```

Important reading:

- the shared `psi` state is advanced once on `(ts, db0)` and persisted as `psi'`
- plain outputs `zs0` still create skip debt
- after skip discharge, `freeze_meval` tries the pending snapshots in order
- if a snapshot does not yet produce output, it stays pending and will be retried later with larger `j`

## Simplified `freeze_meval`

```text
freeze_meval eval j pending p psi0 =
  case pending of
    [] => ([], [])
  | alpha # pending' =>
      let ys, psi' = eval (Mapping.empty(p := replicate j alpha)) psi0 in
      case ys of
        [] => ([], alpha # pending')
      | y # _ =>
          let zs, pending'' = freeze_meval eval j pending' p psi0 in
          (y # zs, pending'')
```

Interpretation:

- each attempt starts from the shared template `psi0`
- the frozen binding for `(p, m)` is supplied as a globally aligned constant stream
- if no output appears, the snapshot is put back into `pending`
- there is no separate current-state bookkeeping

This is simpler, but it also means unfinished frozen work does not preserve an incremental `psi` state of its own.

## Trade-off of the simplified design

Pros:

- no active-current bookkeeping
- no need for `ell`
- no reconciliation between `meval_current` and `freeze_meval`

Cons:

- each retry restarts from `psi'` instead of continuing from a persisted frozen-specific state
- this may repeat work
- each retry currently supplies `replicate j alpha`, not just an incremental suffix

## Proof/implementation impact

Above the line where proof repair starts, the main updates are:

- simplify `freeze_meval0`
- simplify `discharge_skip`
- stop using `meval_current`
- remove `opt` from `MFrz`

That gives a simpler first implementation target, and it now matches the current abstract monitor implementation.

## Why `meval_frz_empty_db` is suspicious

The tentative helper

```text
meval_frz_empty_db:
  meval j n ts (Mapping.delete pn db) phi
  = meval j n ts (Mapping.update pn (replicate (length ts) empty_table)
      (Mapping.delete pn db)) phi
```

is suspicious not because it is obviously false, but because it is much stronger than what the
`Frz` correctness argument actually needs.

What the `Frz` proof really needs is only this:

- the shared `psi` template is evaluated in a context where the locally bound predicate `(p,m)` is
  shadowed
- operationally, the current runtime chooses shadowing by deleting `(p,m)` from the ambient db
- the correctness proof, however, wants to reuse the ordinary `meval_correct` induction hypothesis,
  which is phrased using a `wf_envs` fact for some explicit database contents
- the most convenient explicit contents for the shadowed binder are often an all-empty stream

So the real obligation is a representation-independence statement for the shadowed binder:

- absent `(p,m)` in the database
- present `(p,m)` with `replicate (length ts) empty_table`

should behave the same for the particular monitor states that arise as the shared `psi` template of
`Frz`.

That is a contextual statement. The fully polymorphic equality above quantifies over all monitor
states and all uses of the database key, including situations irrelevant to the `Frz` proof.

In other words:

- the lemma may still be true
- but if it is true, proving it globally is likely the wrong proof granularity
- and if it fails, the failure will most likely come from using too weak an invariant, not from the
  `Frz` idea itself

## Re-evaluation: the empty-shadow plan is wrong

The earlier idea of proving an auxiliary lemma such as

```text
meval_frz_shadow_empty:
  meval ... (Mapping.delete (p,m) db) psi_m
  = meval ... (Mapping.update (p,m) (replicate ... empty_table) (Mapping.delete (p,m) db)) psi_m
```

should be treated as a dead end.

Reason:

- `Let` also has a locally binding predicate and therefore also shadows any outer meaning of that
  predicate
- nevertheless the `Let` correctness proof does not need any separate database-shadowing congruence
- instead, `Let` works by proving the right `wf_envs_update` statement and then applying the ordinary
  induction hypothesis to `psi`

So if `Frz` seems to require a special shadowing congruence while `Let` does not, that is a strong
sign that the chosen invariant or proof decomposition is wrong.

The real issue is not the representation of an empty shadowed database entry. The real issue is that
the simplified `Frz` runtime does not run `psi` under the final frozen interpretation at all. It runs
one shared `psi` template on ordinary input, uses its output to create skip debt, and separately
replays concrete frozen snapshots via `freeze_meval0`.

So the proof must talk about that queue-based operational split directly, rather than trying to force
the shared `psi` run into a `wf_mformula ... (V((p,m) := frz_sat {})) ...` mold.

## Corrected proof direction

The right analogy is:

- `Let` correctness is driven by `wf_envs_update`
- `LetPast` correctness is driven by a dedicated stateful environment-update lemma (`wf_envs_update_sup`
  / `wf_envs_update2`) plus a worker invariant
- therefore `Frz` should also use a dedicated queue-based invariant and a dedicated environment/state
  update story

not a general shadowing congruence.

So the intended `Frz` proof shape is now:

1. prove correctness of the `phi` submonitor exactly as in `Let`
2. interpret the resulting `xs` as newly available frozen snapshots
3. use the plain `psi` run only to justify skip debt and the updated shared template state
4. relate the queue `(skip, alphas)` to the unresolved frozen-start interval
5. prove a dedicated helper theorem for `freeze_meval0` against that queue invariant
6. combine:
   - `phi_step`
   - plain `psi` progress / skip accounting
   - queue invariant preservation under `discharge_skip`
   - `freeze_meval0` correctness

This mirrors the runtime much more faithfully.

In particular, the proof should no longer try to claim that the plain `psi` run itself is a run under
the final frozen interpretation. It is not.

## Revised invariant obligations

The current `wf_mformula.Frz` shape is still not obviously the right one.

The problematic part is the clause saying, roughly, that the shared `psi` template is well-formed
under `V((p,m) := frz_sat {})`. That is too close to the failed empty-shadow idea.

What the runtime really stores is:

- a shared `psi` template already advanced on the ordinary input stream
- a queue of concrete snapshots to be replayed later
- a skip counter that says how many earliest starts are already resolved without replay

So the state invariant should be decomposed accordingly.

Recommended split:

- one invariant for the shared `psi` template as an ordinary monitor state advanced on real input
- one invariant for the queue, connecting pending snapshots to concrete frozen start positions
- one invariant for skip debt, including `skip > 0 --> alphas = []`
- one helper postcondition for `freeze_meval0`, relating replay over the queue to the next output
  prefix of `Frz`

This is much closer to the `LetPast` proof architecture than to the `Let` proof architecture.

## Concrete next proof tasks

The next formalization steps should therefore be:

1. Remove the now-misleading shadowing helper direction from `Correctness.thy`:
   - `frz_db_shadow`
   - `frz_db_shadow_lookupD`
   - `meval_MPred_frz_db_shadow`
   - `meval_frz_shadow_empty`

2. Introduce a dedicated helper theorem for `discharge_skip` that exposes the key dichotomy:

```text
discharge_skip skip Xs = (skip', Xs')
==> skip' > 0 --> Xs' = []
```

and, if useful, a stronger statement describing how many earliest queue entries were removed.

3. Introduce a dedicated correctness/postcondition statement for `freeze_meval0` in terms of:

- the shared `psi` template
- the queue of semantically justified snapshots
- the next unresolved frozen-start interval

4. Rework the `MFrz` branch of `meval_correct` to follow the operational split directly, rather than
   routing through a fake empty-shadowed `psi` run.

## Invariant adjustment that is likely needed

The current queue-based invariant records:

- which frozen snapshots are pending
- how `skip` aligns with semantic progress
- that the shared `psi` template is well-formed under `V((p,m) := frz_sat {})`
- and the queue/skip exclusion law `skip > 0 --> alphas = []`

That invariant is still too weak, but not because it lacks a shadowing-congruence clause.

Rather, it is too weak because it does not yet separate clearly enough:

- the ordinary shared-template state,
- the queue of frozen starts,
- and the replay worker behavior.

So the strengthening should go in the direction of a better queue/worker invariant, not in the
direction of a database-shadowing congruence premise.

Still, the `skip > 0 --> alphas = []` clause should remain directly inside the state invariant
itself, because it reflects the runtime behavior of `discharge_skip` rather than a downstream proof
artifact.

## Bottom line

The important correction is now:

- do not pursue `meval_frz_empty_db`
- do not replace it by an "empty shadow" congruence either
- instead, rebuild the `Frz` correctness argument around the actual queue-based runtime split

The proof should look operationally like `LetPast`, not semantically like a fake `Let` with an empty
binder interpretation.

## Working hypothesis for `Correctness.thy`

For the simplified runtime, the `wf_mformula` invariant for `Frz` should also be simplified.

It should not try to remember an active frozen monitor instance, because none exists in the runtime state.
Instead it should be queue-based.

Recommended split:

- `phi` submonitor:
  - well-formed exactly as in `Let`
  - monitored at arity `m = nfv phi`

- shared `psi` template:
  - the stored `psi` monitor is the ordinary shared template advanced on real input
  - correctness should be stated extensionally: for any frozen snapshot `alpha` that is already semantically available,
    re-running this shared template under `(p,m) := replicate j alpha` yields the correct frozen behavior

- `skip`:
  - counts earliest frozen starts already resolved by the plain `psi` run without consulting frozen data
  - so `skip` is semantic prefix debt, not merely an implementation artifact
  - crucial consistency law: if `skip > 0`, then `alphas = []`
  - intuition: `discharge_skip` consumes pending snapshots eagerly, so leftover positive skip debt means
    there were no snapshots available to keep

- `alphas`:
  - FIFO list of the remaining frozen snapshots after those skipped starts are dropped
  - each `alpha` should satisfy a snapshot qtable property for `phi` at its original frozen start index

- alignment invariant:
  - if `jphi = progress P phi j` and `jfrz = progress P (Frz p phi psi) j`,
    then the pending queue should correspond to the index interval
    `[jfrz + skip ..< jphi]`
  - so the number and order of pending snapshots are determined semantically by the unresolved suffix of frozen starts

This suggests helper definitions of the following shape in `Correctness.thy`:

- `frz_qtable sigma V m phi k X`
- `wf_frz_snapshots sigma V m phi ks Xs`
- `wf_frz_state sigma j P V p m phi psi skip Xs`
- `wf_frz_submonitor sigma j P V p m phi n R psi_m psi`

More concretely, `wf_frz_state` should include:

```text
jfrz + skip <= jphi
wf_frz_queue sigma V m phi [jfrz + skip ..< jphi] Xs
skip > 0 --> Xs = []
```

The last clause is important and should be treated as part of the real runtime invariant, not as an
auxiliary lemma proved later on demand.

- after `discharge_skip skip Xs = (skip', Xs')`, the result always satisfies:
  - either `skip' = 0`, and then `Xs'` may be non-empty, or
  - `skip' > 0`, and then necessarily `Xs' = []`
- so a positive skip counter means we have unresolved debt but no currently available snapshots

The crucial proof discipline should be:

- use `Let` as the model for binder semantics and shadowing
- use `LetPast` as the model for introducing helper invariants and postconditions
- but keep the actual `Frz` invariant queue-based, since the simplified runtime stores only `skip` and `alphas`

## Sketch for `safe_letpast` of `Frz`

The `Let`-style clause copied to `Frz` is likely too strong in the wrong direction:

```text
safe_letpast p (Frz e phi psi) =
  (safe_letpast (e, nfv phi) psi * safe_letpast p phi)
  sup
  (if p = (e, nfv phi) then Unused else safe_letpast p psi)
```

Why this is suspicious:

- in `Let`, an occurrence of the bound predicate inside `psi` at time `j` triggers evaluation of `phi` at the same time `j`
- in `Frz`, an occurrence of the bound predicate inside `psi` at time `j` triggers evaluation of `phi` at the frozen outer time `i`
- so temporal delay inside `psi` should not be multiplied into the dependence on `phi` in the same way as for `Let`

Counterexample pattern:

```text
Frz q (Pred p) (Prev I (Pred q))
```

At outer time `i > 0`, `Prev (Pred q)` consults `q` at time `i - 1`, but `q` still means `Pred p` evaluated at outer time `i`.
So the dependence on `p` is `NonFutuRec`, not `PastRec`.

A better first sketch is therefore:

```text
safe_letpast p (Frz e phi psi) =
  frz_dep (safe_letpast (e, nfv phi) psi) (safe_letpast p phi)
  sup
  (if p = (e, nfv phi) then Unused else safe_letpast p psi)
```

where the freeze-specific dependency combiner is:

```text
frz_dep Unused      x = Unused
frz_dep PastRec     x = x
frz_dep NonFutuRec  x = x
frz_dep AnyRec      x = x
```

Equivalently, more compactly:

```text
frz_dep s x = (if s = Unused then Unused else x)
```

Intuition:

- if `psi` does not use the frozen predicate at all, then the binder-mediated dependence is `Unused`
- if `psi` uses the frozen predicate in any way, then the dependence on the external predicate `p` comes entirely from `phi`
- the temporal mode (`PastRec` vs `NonFutuRec`) of that mediated dependence is determined by `phi`, not by where inside `psi` the frozen predicate is queried

The second summand still accounts for direct free occurrences of `p` in `psi` when `p` is different from the locally bound `(e, nfv phi)`.

This is only a sketch, but it explains why the copied `Let` clause fails and what a corrected `Frz` clause should look like.

## Working hypothesis for `Progress.thy`

The previous plain `min` candidate is too coarse, and the ad-hoc dead-binder case split is not satisfactory either.

The simplified monitor is prefix-serial:

- first plain `psi` outputs create skip debt
- then `freeze_meval0` tries pending snapshots in order
- it stops at the first snapshot that still cannot yield output

So the progress/accounting story should likely mirror that control flow with a recursive helper, much like `letpast_progress` mirrors `letpast_meval0`.

The key start-sensitive intuition remains:

```text
for an outer start i,
the frozen predicate behaves inside psi like
  if i < progress P phi j then j else 0
```

This says:

- if the snapshot for start `i` is already available, then inside `psi` the bound predicate is globally available on the whole known prefix
- otherwise the frozen predicate contributes no progress for that start

Since the current progress environment cannot express this start-dependent update directly, a separate recursive helper seems more appropriate.

One plausible sketch is a least-fixed-point style definition:

```text
frz_progress_step P p phi psi j i =
  progress (P((p, nfv phi) |-> (if i < progress P phi j then j else 0))) psi j

frz_progress P p phi psi j =
  (LEAST i. i <= j and frz_progress_step P p phi psi j i <= i)
```

How to read this:

- `i` is the first candidate unresolved frozen start
- `frz_progress_step ... i` asks whether `psi` can already produce the verdict for that start when the frozen predicate is given progress `j` exactly when the corresponding snapshot is available
- the least such `i` is exactly the length of the resolved prefix of frozen starts

This matches the simplified `freeze_meval0` story much better than a single closed-form `min`:

- it naturally handles cases where `psi` is independent of `p`, because then `frz_progress_step` ignores the update and the recursion can continue without depending on `phi`
- it also handles mixed cases where some early starts are independent of frozen information but later starts are not
- and it mirrors the operational fact that the monitor emits a prefix of resolved starts and then stops at the first unresolved one

This should be treated as a sketch, not a final definition.

Open proof obligations / design questions:

- show that a suitable witness `i <= j` always exists
- derive useful monotonicity facts for the `LEAST`-based definition
- relate the helper to the simplified `discharge_skip` + `freeze_meval0` control flow
- derive the final `progress` equation for `Formula.Frz` from `frz_progress`

Sanity checks the final definition should satisfy:

- if `p` is irrelevant for `psi`, then `progress (Formula.Frz p phi psi) j` should collapse to `progress psi j`
- `Frz p phi (Pred p)` should still have progress `progress P phi j`
- `Frz p phi (Next (Pred p))` should still behave like `min (progress P phi j) (j - 1)`
