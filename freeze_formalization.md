# The Current `Frz` Formalization

This note describes the current Isabelle formalization of the freeze quantifier
`Formula.Frz` in the MFODL monitor development under
`thys/MFODL_Monitor_Devel/`.

It is intended for a reader who already knows the general monitor architecture
(`formula`, `mformula`, `progress`, `meval`, `wf_mformula`, `meval_correct`) but
does not yet know the design of the `Frz` case.

The presentation follows the code as it exists now, not an older design.

## 1. Surface syntax and semantic intention

The formula language contains:

```text
Formula.Frz p φ ψ
```

from `Formula.thy`:

```text
datatype formula = ... | Frz name formula formula | ...
```

Intuitively, `Frz p φ ψ` evaluates `ψ` at the current outer time `i`, while
binding the predicate symbol `(p, nfv φ)` to the frozen truth predicate of `φ`
at that same time `i`.

This is analogous to `Let`, except that the binding is frozen to the outer time
instead of varying with the queried time.

## 2. Static shape: free variables, arity, safety, typing

### 2.1 Free variables and arity

`Frz` behaves like `Let` and `LetPast` with respect to variable accounting:

```text
fvi b (Frz p φ ψ) = fvi b ψ
nfv (Frz p φ ψ) = nfv ψ
```

So the outer formula exports exactly the free variables of `ψ`. The frozen
subformula `φ` is only used to define the auxiliary predicate binding.

The auxiliary predicate introduced by `Frz` has name/arity:

```text
pn = (p, Formula.nfv φ)
```

### 2.2 Safety

From `Safety.thy`:

```text
safe_formula (Formula.Frz p φ ψ) =
  ({0..<Formula.nfv φ} ⊆ fv φ ∧ safe_formula φ ∧ safe_formula ψ)
```

The condition `{0..<nfv φ} ⊆ fv φ` is the standard requirement that the frozen
predicate expose all positions of its tuple.

Crucially, unlike some other operators, there is no side condition forbidding
`ψ` from mentioning the bound predicate `pn`. That is why the proof cannot rely
on a simple `not_contains_pred` argument and instead needs the V-insensitivity
machinery.

### 2.3 Monitorability / executable monitorability

`Monitor.thy` uses the same condition for the executable predicate:

```text
mmonitorable_exec (Formula.Frz p φ ψ) =
  ({0..<Formula.nfv φ} ⊆ fv φ ∧ mmonitorable_exec φ ∧ mmonitorable_exec ψ)
```

So `Frz` is accepted by the monitor exactly when both subformulas are accepted
and the frozen tuple is fully exposed.

### 2.4 Typing

The declarative typing rule in `Typing.thy` is:

```text
S, E' ⊢ φ
S((p, Formula.nfv φ) ↦ tabulate E' 0 (Formula.nfv φ)), E ⊢ ψ
-------------------------------------------------------------
S, E ⊢ Formula.Frz p φ ψ
```

Interpretation:

- `φ` is typed in its own environment `E'`; this determines the tuple type of
  the frozen predicate.
- `ψ` is typed in the original environment `E`, but with the signature extended
  by a predicate `(p, nfv φ)` whose argument types are exactly the first
  `nfv φ` entries of `E'`.

The executable checker mirrors the `Let` clause exactly:

```text
check S E (Formula.Frz p φ ψ) =
  (let f0 = new_type_symbol ^^ Formula.nfv φ in
   check (map_sig f0 S) TAny (map_formula f0 φ) >>= (λf1.
   check (map_sig f1 ((map_sig f0 S)
      ((p, Formula.nfv φ) ↦ map TAny [0..<Formula.nfv φ])))
      (f1 ∘ f0 ∘ E) (map_formula (f1 ∘ f0) ψ) >>= (λf2.
   return (f2 ∘ f1 ∘ f0))))
```

and the cheap shape-only checker records:

```text
check_wty_formula (Formula.Frz p φ ψ) =
  (check_wty_formula φ ∧ check_wty_formula ψ)
```

## 3. Semantics

From `Formula.thy`, the semantic clause is:

```text
sat σ V v i (Frz p φ ψ) =
  sat σ (V((p, nfv φ) ↦ λw j. sat σ V w i φ)) v i ψ
```

There are two points worth emphasizing:

1. The bound predicate is interpreted by the function
   ```text
   λw j. sat σ V w i φ
   ```
   so it ignores its own time argument `j` and always reuses the outer time `i`.

2. `ψ` is still evaluated at time `i`; `Frz` does not shift time, it only
   installs a special predicate interpretation.

Thus the entire operator is “freeze current time into predicate `p` and then run
`ψ` normally”.

## 4. Progress

### 4.1 Definition

From `Progress.thy`:

```text
progress P (Formula.Frz p φ ψ) j =
  (let pn = (p, Formula.nfv φ) in
   LEAST i. i ≤ j ∧ progress (P(pn ↦ (if i < progress P φ j then j else 0))) ψ j ≤ i)
```

This definition is the semantic core of the monitor design.

For a candidate frontier `i`:

- if `i < progress P φ j`, then snapshots for `φ` are still available up to `j`,
  so `ψ` is checked under `P(pn ↦ j)`;
- otherwise the frozen predicate is unavailable, and `ψ` is checked under
  `P(pn ↦ 0)`.

The least `i` where `ψ` no longer demands more progress than `i` is the Frz
progress.

### 4.2 Useful derived frontiers

The correctness proof repeatedly uses the abbreviations:

```text
jphi   = progress σ P φ j
jphi'  = progress σ P' φ (j + δ)
jpsi0  = progress σ (P(pn ↦ 0)) ψ j
jpsi0' = progress σ (P'(pn ↦ 0)) ψ (j + δ)
jpsij' = progress σ (P'(pn ↦ j + δ)) ψ (j + δ)
jfrz   = progress σ P (Frz p φ ψ) j
jfrz'  = progress σ P' (Frz p φ ψ) (j + δ)
```

and the key facts:

- `jpsi0 ≤ jfrz`
- if `jfrz > jphi`, then `jfrz = jpsi0`
- `jfrz ≤ jpsij'`
- `jfrz' ≤ jpsij'`
- `jfrz' = (if jpsij' < jphi' then jpsij' else if jpsi0' ≤ jphi' then jphi' else jpsi0')`

The most important operational equality proved in `Correctness.thy` is:

```text
jfrz' = jfrz + |zs0_out| + |ys|
```

This is the progress equation that exactly matches the monitor output.

## 5. Monitor representation

### 5.1 Runtime state

The monitor datatype in `Monitor.thy` contains the state constructor:

```text
MFrz p m φ ψ jfrz jpsi0 jphi alphas
```

where:

- `p` is the frozen predicate name,
- `m = Formula.nfv φ` is the arity of the frozen tuple,
- `φ` is the monitor for the snapshot-producing subformula,
- `ψ` is the monitor for the shared/replay subformula,
- `jfrz` is the already-produced progress of the full Frz formula,
- `jpsi0` is the progress of the shared `ψ` run under `P(pn ↦ 0)`,
- `jphi` is the progress of `φ`,
- `alphas` is the queue of pending snapshots that still need replay.

The design stores all three progress counters explicitly. This replaced an older
design that encoded part of the state as a “skip” debt.

### 5.2 Initialization

From `minit0`:

```text
minit0 n (Formula.Frz p φ ψ) =
  MFrz p (Formula.nfv φ) (minit0 (Formula.nfv φ) φ) (minit0 n ψ) 0 0 0 []
```

So the initial state starts with:

- no produced Frz output,
- no shared `ψ` output consumed,
- no `φ` snapshots produced,
- empty queue.

## 6. The helper replay operator

### 6.1 `freeze_meval0`

The basic replay driver is:

```text
freeze_meval0 eval k [] = ([], [])
freeze_meval0 eval k (α # αs) =
  (let (ys, _) = eval α in
   case drop k ys of
     []     => ([], α # αs)
   | y # _  => let (zs, αs') = freeze_meval0 eval (Suc k) αs
               in (y # zs, αs'))
```

Interpretation:

- for the first snapshot, take the `k`-th row of its replay output,
- for the second snapshot, take the `(k+1)`-st row,
- and so on,
- stop as soon as one replay run does not have that row yet; the remaining
  snapshots stay queued.

This is the diagonal replay pattern.

### 6.2 Replay environment

The correctness proof uses the abbreviation:

```text
frz_meval n p m j db ψ ≡
  (λα. meval j n []
    (Mapping.update (p, m) (replicate j α) (Mapping.map_values (λ_ _. []) db)) ψ)
```

Important details:

- replay is run on an empty timestamp batch `[]`,
- the frozen predicate is given by `replicate j α`, i.e. the same table at all
  times below `j`,
- the rest of the database is not discarded with `Mapping.empty`; instead
  `Mapping.map_values (λ_ _. []) db` preserves the key domain and replaces every
  relation by an empty list. This is essential for `wf_envs`.

## 7. The monitor step for `MFrz`

The current `meval` clause is:

```text
meval n ts db (MFrz p m φ ψ jfrz jpsi0 jphi alphas) =
  (let (xs, φ) = meval m ts db φ;
       db0 = Mapping.update (p, m) [] db;
       (zs0, ψ) = meval n ts db0 ψ;
       zs0_out = drop (jfrz - jpsi0) zs0;
       jpsi0 = jpsi0 + length zs0;
       alphas = drop (jfrz - jphi + length zs0_out) (alphas @ xs);
       (ys, alphas') = freeze_meval0
         (λα. meval n []
            (Mapping.update (p, m) (replicate j α) (Mapping.map_values (λ_ _. []) db)) ψ)
         (jfrz - jpsi0) alphas;
       jphi = jphi + length xs;
       jfrz = jfrz + length zs0_out + length ys
   in (zs0_out @ ys, MFrz p m φ ψ jfrz jpsi0 jphi alphas'))
```

To read this operationally:

1. Evaluate `φ` on the current batch, yielding new snapshots `xs` for the range
   `[jphi..<jphi')`.
2. Evaluate the shared `ψ` run with `P(pn)=0`, yielding `zs0` for the range
   `[jpsi0..<jpsi0')`.
3. Drop the prefix below `jfrz`, since those rows are already semantically past.
   The remaining rows are `zs0_out`.
4. Extend the snapshot queue with the new snapshots and drop everything that is
   already semantically discharged. The drop amount is
   ```text
   (jfrz - jphi) + |zs0_out|
   ```
   i.e. old debt plus the newly emitted shared rows.
5. Replay the remaining queue diagonally via `freeze_meval0`.
6. Update all three progress counters and return `zs0_out @ ys`.

### 7.1 The important bug fix

The replay call must start at offset:

```text
jfrz - jpsi0'
```

in the proof-level notation (equivalently the corresponding state expression at
the call site). Starting at `0` is wrong when `jfrz > jpsi0'`, because replay
must skip the already-semantically-past prefix of each replay output.

This was the crucial algorithmic fix in the current formalization.

## 8. Correctness-side invariants

### 8.1 Snapshot tables and queues

`Correctness.thy` defines:

```text
frz_qtable σ V m φ k X =
  qtable m (fv φ) (mem_restr UNIV) (λv. sat σ V (map the v) k φ) X

wf_frz_queue σ V m φ ks Xs =
  list_all2 (λk X. frz_qtable σ V m φ k X) ks Xs
```

So a freeze queue is literally a list of `φ`-tables paired with their semantic
time indices.

### 8.2 Frz state invariant

```text
wf_frz_state σ j P V p m φ ψ jphi_val Xs =
  (let jphi = progress σ P φ j;
       jfrz = progress σ P (Formula.Frz p φ ψ) j
   in jphi_val = jphi ∧ wf_frz_queue σ V m φ [jfrz..<jphi] Xs)
```

Thus the queue stores exactly the semantic interval `[jfrz..<jphi)`.

This is the key simplification of the current formalization: the queue is not
described via an auxiliary skip counter. It is described directly by semantic
progress endpoints.

### 8.3 `wf_mformula` rule for `Frz`

The inductive invariant for monitor formulas contains the rule:

```text
wf_mformula σ j P V m UNIV φ φ'
∀i. wf_mformula σ j (P((p,m) ↦ 0))
      (V((p,m) ↦ λw j. sat σ V w i φ')) n R ψ ψ'
wf_frz_state σ j P V p m φ' ψ' jphi αs
jfrz = progress σ P (Formula.Frz p φ' ψ') j
jpsi0 = progress σ (P((p,m) ↦ 0)) ψ' j
{0..<m} ⊆ fv φ'
m = nfv φ'
safe_formula φ'
safe_formula ψ'
---------------------------------------------------------------
wf_mformula σ j P V n R
  (MFrz p m φ ψ jfrz jpsi0 jphi αs)
  (Formula.Frz p φ' ψ')
```

This packages exactly the data needed by the monitor step:

- a monitor for `φ`,
- a whole family of monitors for `ψ` under frozen valuations,
- the queue invariant,
- the two stored semantic frontiers `jfrz` and `jpsi0`,
- the arity and safety side conditions.

## 9. Correctness proof sketch

The `MFrz` case in `meval_correct` is the main theorem showing that the runtime
step matches the declarative semantics and restores the `wf_mformula` invariant.

### 9.1 High-level decomposition

Let:

```text
jfrz   = progress σ P (Frz p φ ψ) j
jfrz'  = progress σ P' (Frz p φ ψ) (j + δ)
jpsi0' = progress σ (P'(pn ↦ 0)) ψ (j + δ)
M      = jfrz + |zs0_out| = max jfrz jpsi0'
```

Then the output interval splits as:

```text
[jfrz..<jfrz') = [jfrz..<M] @ [M..<jfrz')
```

The proof mirrors this split:

- `zs0_out_rows` proves correctness of the left part `[jfrz..<M]`,
- `ys_rows` proves correctness of the right part `[M..<jfrz')`,
- then `list_all2_appendI` recombines them.

### 9.2 Shared-run part: `zs0_out_rows`

The induction hypothesis for the ordinary `ψ` step gives rows for `zs0` on
`[jpsi0..<jpsi0')` under `P(pn ↦ 0)`.

Dropping `jfrz - jpsi0` rows yields tables on `[jfrz..<jpsi0')`.

These are not yet Frz tables, but `sat_V_cong` shows that at indices below the
`P(pn ↦ 0)` progress of `ψ`, the actual value of `V(pn)` is irrelevant, since the
side condition for `pn` is vacuous when `P(pn)=0`.

This converts the shared `ψ` rows into `Frz` rows.

### 9.3 Replay part: `ys_rows`

This is the distinctive part of the Frz proof.

1. `freeze_meval0_diagonal` gives:

   ```text
   ys ! i = fst (frz_meval ... (alphas1 ! i)) ! (k0 + i)
   ```

   where `k0 = jfrz - jpsi0'`.

2. `queue_αs1_B` proves that `alphas1` is a well-formed queue over `[M..<jphi')`.
   Hence `alphas1 ! i` is a correct frozen `φ` table at index `M + i`.

3. Applying the replay induction hypothesis `IHψ_new` to `alphas1 ! i` yields
   replay rows for `ψ` on `[jpsi0'..<jpsij')` under the valuation frozen at
   `M + i`.

4. The diagonal index selects exactly the semantic position `M + i`, because:

   ```text
   jpsi0' + k0 = M
   ```

5. Unfolding the semantic clause for `Frz` converts that replay row for `ψ`
   into the desired row for `Frz` at index `M + i`.

6. Since `jfrz' = M + |ys|`, these rows cover exactly `[M..<jfrz')`.

### 9.4 Progress equation

The proof also establishes:

```text
jfrz' = jfrz + |zs0_out| + |ys|
```

This is proved by analyzing the Frz progress definition on the post-state and
matching the three semantic regions:

- already produced before the step,
- newly available from the shared `ψ` run,
- newly available only after replay.

### 9.5 Queue post-state

The post-state queue invariant (`frz_step_post`) shows that after extending the
queue with the new `φ` snapshots and dropping the discharged prefix, the
remaining queue is exactly the expected semantic interval for the next state.

One subtlety is that queue arithmetic must split on whether `jfrz ≤ jphi` or
`jfrz > jphi`:

- if `jfrz ≤ jphi`, the old queue and the new snapshots concatenate to the full
  interval and one can reason by append + drop;
- if `jfrz > jphi`, the old queue interval is empty, so the proof must work
  directly from the new snapshots `xs`.

This case split is essential because the formula

```text
length (alphas @ xs) = jphi' - jfrz
```

is not valid unconditionally.

## 10. Summary of the current design

The current Frz formalization is built around four ideas:

1. **Semantic binding**: `Frz` freezes the current outer time into an auxiliary
   predicate.
2. **Three explicit progress counters**: `jfrz`, `jpsi0`, `jphi` are stored in
   the runtime state.
3. **Queue = semantic interval**: the pending snapshot queue is described by the
   exact interval `[jfrz..<jphi)`.
4. **Output split at `M = max jfrz jpsi0'`**: shared `ψ` output covers the left
   part, replay output covers the right part.

This yields a monitor whose operational structure is simple:

- run `φ`,
- run the shared `ψ` monitor under `P(pn)=0`,
- trim output already below `jfrz`,
- trim the queue by semantic debt,
- replay the remaining queue diagonally,
- update the three frontiers.

And it yields a correctness proof whose structure matches that runtime exactly.

## 11. Main source locations

- Syntax and semantics: `thys/MFODL_Monitor_Devel/Formula.thy`
- Progress: `thys/MFODL_Monitor_Devel/Progress.thy`
- Safety: `thys/MFODL_Monitor_Devel/Safety.thy`
- Typing: `thys/MFODL_Monitor_Devel/Typing.thy`
- Runtime monitor: `thys/MFODL_Monitor_Devel/Monitor.thy`
- Invariants and correctness: `thys/MFODL_Monitor_Devel/Correctness.thy`
