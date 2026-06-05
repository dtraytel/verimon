# The MonPoly Monitoring Algorithm

This document gives a high-level, researcher-oriented overview of how MonPoly
monitors **Metric First-Order Temporal Logic (MFOTL)** properties over a stream
of timestamped events. It describes the *unverified native* engine
(`src/algorithm.ml` and friends); the formally verified kernel
(`src/verified.ml`, extracted from Isabelle) implements the same specification
with a different, proof-carrying data structure.

The core algorithm is the one of Basin, Klaedtke, Müller, and Zălinescu,
*"Runtime Monitoring of Metric First-order Temporal Properties"* (FSTTCS'08) and
*"Monitoring Metric First-order Temporal Properties"* (J. ACM 2015).

---

## 1. What is being monitored

### Input: a temporal structure (the log)

The input is a stream of **time-points**. Each time-point `i` carries

- a **time-stamp** `τ_i ∈ ℕ` (monotonically non-decreasing, possibly repeating), and
- a **database** `D_i`: a finite set of ground facts `p(d₁,…,dₙ)` over the
  signature's predicate symbols.

A time-point is an index into the stream; a time-stamp is wall-clock-ish time.
Several time-points may share a time-stamp, and metric intervals constrain
*time-stamp* differences, not time-point counts. This distinction is central:
`ALWAYS[0,5] φ` constrains all future time-points whose time-stamp lies within 5
units, which may be an unbounded number of time-points.

### Property: an MFOTL formula

Formulas combine

- **first-order** structure: predicates `p(t̄)`, equality/order on terms,
  `∃`/`∀`, the usual Boolean connectives;
- **metric temporal** structure: past operators `PREV_I`, `ONCE_I`, `SINCE_I`
  (and `PAST_ALWAYS`, `TRIGGER`) and future operators `NEXT_I`, `EVENTUALLY_I`,
  `ALWAYS_I`, `UNTIL_I` (and `RELEASE`), each annotated with a metric interval
  `I = [a,b]` (or `[a,∞)`) over time-stamp differences;
- **aggregations** (`CNT`, `SUM`, `AVG`, `MIN`, `MAX`, …) and **let**-style
  predicate definitions (`LET`, `LETPAST`), and the **freeze** quantifier `FRZ`
  (see §7).

The **semantics** `(D̄, τ̄), v, i ⊨ φ` is the standard MFOTL satisfaction
relation: a valuation `v` of the free variables satisfies `φ` at time-point `i`.
The monitor's job is, for each time-point `i`, to output the **finite relation**
of satisfying valuations — i.e. the set of assignments to `φ`'s free variables
that make `φ` true at `i`.

> Everything the monitor manipulates is a **finite relation** (a set of tuples).
> A closed formula yields the empty/non-empty relation encoding `true`/`false`.

---

## 2. Pipeline overview

```
  formula source
        │   parse
        ▼
   MFOTL.formula ──► rewrite/normalize ──► monitorability check
        │                                        │
        │ add_ext (annotate each subformula      │
        ▼          with incremental state)        │
   extformula  ◄───────────────────────────────── ┘
        │
        │   for each log time-point i:
        │     1. add_index   — push D_i into the leaves
        │     2. neval.append i
        │     3. process_index — evaluate as far as possible
        ▼
   stream of (time-point, time-stamp, relation) verdicts
```

The two ideas that make this *online and incremental* are:

1. A shared **`neval` queue** of time-points that have been read but not yet
   fully evaluated.
2. An **extended formula (`extformula`)** that carries, at every node, the
   mutable auxiliary state needed to produce that node's next output without
   recomputing the past.

---

## 3. Preprocessing: rewriting and monitorability

Before monitoring, the formula passes through `Rewriting`:

- **Normalization** — eliminate syntactic sugar (`IMPLIES`, `EQUIV`,
  `FORALL`, `EVENTUALLY`/`ONCE` as derived from `UNTIL`/`SINCE`, …), push
  negations inward, simplify terms, eliminate double negation.
- **Monitorability check** (`is_monitorable`) — MFOTL is undecidable in general
  and produces infinite relations for arbitrary formulas, so MonPoly restricts
  to a **safe fragment** in which every subformula yields a *finite* relation.
  Examples of the discipline:
  - `NOT ψ` is only allowed where it can be evaluated as a finite difference,
    e.g. in `φ AND NOT ψ` with `fv(ψ) ⊆ fv(φ)`;
  - `φ OR ψ` requires `fv(φ) = fv(ψ)`;
  - the bodies of `SINCE`/`UNTIL` obey a subset condition on free variables.
  If the formula is outside the fragment, the monitor refuses it ("not
  monitorable").

The result is then handed to `add_ext`.

---

## 4. The extended formula

`add_ext` walks the formula and produces an `extformula` (constructors `ERel`,
`EPred`, `EAnd`, `EOr`, `EExists`, `ENeg`, `EAggreg`/`EAggOnce`, `EPrev`,
`ENext`, `ESince`, `EUntil`, `ELet`, `EFrz`, …). Two things happen here:

1. **Compilation of the relational operations.** Each node stores a closure
   (`comp`) that performs its *non-temporal* relational work: projection,
   join, selection, anti-join, aggregation, variable renaming. For instance an
   `EAnd` stores the join function for its two operands; an `EPred` stores the
   projection/filter from the raw fact tuples to the subformula's free
   variables.

2. **Allocation of incremental auxiliary state**, one per node:
   - `EPred` holds a **queue** `pqueue` of `(tp, ts, relation)` triples — the
     matching facts delivered for each time-point, consumed in order.
   - `EPrev`/`ENext` hold a one-cell pointer into `neval` and an `init` flag.
   - `ESince` holds an `msaux` (metric *since* auxiliary); `EUntil` holds an
     `muaux` (metric *until* auxiliary). These are the sliding-window data
     structures that make temporal evaluation incremental (see §6).
   - `EAnd`/`EOr` hold a buffer `arel` for an already-computed left operand
     when the right operand is not yet evaluable.
   - `ELet` holds the cell up to which the defined predicate has been produced.

The extformula is therefore both the *plan* (closures) and the *running state*
(queues, sliding windows, cursors) of evaluation.

---

## 5. The driver loop

For each parsed time-point `(i, τ_i, D_i)` (`Monitor.eval_tp` →
`process_index`):

1. **`add_index`** traverses the extformula and pushes the new data to the
   leaves: for every `EPred p`, it looks up `p`'s facts in `D_i`, applies the
   node's projection, and **enqueues** `(i, τ_i, rel)` onto that predicate's
   `pqueue`. Special predicates `tp`, `ts`, `tpts` synthesize the index/time-stamp.
2. The time-point is **appended to `neval`**, the shared queue of read-but-unevaluated indices.
3. **`process_index`** repeatedly calls **`eval`** on the next un-evaluated cell
   (`s_last` + 1):
   - if `eval` returns `Some rel`, the verdict for that time-point is emitted
     (`show_results`), `s_last` advances, and the loop tries the next cell;
   - if `eval` returns `None`, the formula **cannot yet be decided** at that
     time-point (a future operator is waiting for more data); the loop stops and
     control returns to read the next log entry.

This is the crux of the **online** behavior: future operators block, the engine
reads more input, and previously blocked time-points become decidable and are
flushed out — possibly several at once. Verdicts are emitted **in time-point
order**, but with **bounded latency** determined by the formula's future reach.

The monitor state (`state` record) is small: the extformula `s_extf`, the shared
`s_neval`, the cursor `s_last` of the last evaluated cell, the most recent
log position, and a scratch DB. This whole state can be **marshalled** to disk
and restored, and **split/merged** for parallel slicing.

---

## 6. How `eval` works — bottom-up, demand-driven

`eval f crt discard` evaluates node `f` at the `neval` cell `crt`, returning
`Some rel` (the relation of satisfying tuples) or `None` (not yet decidable). It
recurses bottom-up. The `discard` flag is a hint that the result will not be
used downstream, so the node may skip materializing it (it must still advance
temporal state correctly).

**Non-temporal nodes** are immediate:
- `EPred` pops the head of its `pqueue` (asserting it matches the requested
  `(tp, ts)`) and returns it.
- `EAnd`/`EOr`/`EExists`/`ENeg`/`EAggreg` evaluate their children at `crt` and
  apply the stored relational closure. If one operand is ready but the other is
  not, the ready relation is buffered (`arel`) so it is not recomputed.

**Past operators** look backward and never block on the future:
- `EPrev_I` returns the child's relation at the *previous* cell, gated by the
  interval test on `τ_i − τ_{i-1}`; empty at time-point 0.
- `ESince_I` maintains an **`msaux`** sliding window keyed by time-stamp: each
  step adds the new `(τ, rel)`, drops entries that have fallen out of the left
  end of the interval, joins/accumulates, and reads off the current result. The
  per-step work is amortized over the window rather than recomputed.

**Future operators** may block:
- `ENext_I` needs the *next* cell to exist; it returns `None` until then.
- `EUntil_I` (and `EVENTUALLY`/`ALWAYS`, which compile to it) maintains an
  **`muaux`** with a *lookahead* discipline. Its internal cursor `ulast`
  advances through `neval` consuming `(f₁,f₂)` results for future cells; a
  compressed queue tracks, per candidate output time-point, when its verdict
  becomes final (i.e. once enough time-stamp has elapsed to cover the interval's
  right end). `take_result` emits the output for the next output time-point as
  soon as it is determined, and returns `None` otherwise.

The key invariant for future operators is **lockstep**: the operator emits its
result for inner time-point `k` exactly when evaluation reaches cell `k`. The
output time-point counter advances by one with each emitted verdict, staying in
sync with the driver's cursor. This is what lets the same incremental machinery
work whether a verdict is available immediately (past operators) or only after
lookahead (future operators).

**`ELet p = φ IN ψ`** evaluates `φ`, feeds its per-time-point relations into the
`pqueue` of the bound predicate `p` inside `ψ` (`add_let_index`), then evaluates
`ψ`. The defined predicate is thus indistinguishable from a base predicate to
the rest of the engine.

---

## 7. The freeze quantifier `FRZ`

`FRZ q(x̄) = φ IN ψ` binds `q` to the **constant relation** that `φ` denotes at
the *outer* time-point `i`, and evaluates `ψ` at `i` with `q` held fixed at that
snapshot for **all inner time-points** that `ψ`'s temporal operators inspect.
Semantically:

```
sat σ V v i (FRZ q φ ψ) = sat σ (V[q ↦ λw j. sat σ V w i φ]) v i ψ
```

Note the `i` (not `j`) inside: `q`'s meaning is frozen at the outer time `i`,
independent of the inner time `j`.

The native engine implements this with two compile-time modes, chosen by whether
`ψ` contains a temporal operator:

- **Static mode (non-temporal `ψ`).** `ψ` lives once in the formula tree.
  `q`'s leaf nodes are *shielded* from `add_index` (so their queues stay empty)
  and instead fed a **constant** relation `pconst` set/cleared around each
  evaluation of `ψ`. Because there are no temporal operators, no per-time-point
  history is needed, and the frozen snapshot can be served at every inner step
  for free. This is the efficient common case.

- **Per-instance mode (temporal `ψ`).** Correct constant-`q` semantics requires
  that each outer time-point sees a *fresh* temporal evaluator with no leakage of
  state across snapshots. For each outer time-point `j` with a non-empty `φ`, the
  engine compiles a **fresh clone** of `ψ`, pins `q`'s leaves to the snapshot via
  `pconst`, and drives the clone from the start of the stream cell-by-cell — just
  like the top-level driver loop. The clone's accumulated history of live
  predicates is replayed at creation (`inject_history`) and extended thereafter by
  `add_index`. The **diagonal** verdict — the clone's output at its own outer
  time-point `j` — is the answer for `j`; it is collected naturally, after
  lookahead for future operators, thanks to the same lockstep invariant.

The verified kernel realizes the same specification differently: it keeps a
single evaluator and uses a `replicate j α` representation of the frozen relation
together with a constant-relation propagation optimization (`mres`/`xres`); the
native per-instance "clone and drive forward" avoids replicating the entire
prefix.

---

## 8. Properties of the algorithm

- **Soundness/completeness (within the safe fragment).** For every monitorable
  formula and time-point, the emitted relation is exactly the set of satisfying
  valuations under the MFOTL semantics. The verified kernel proves this in
  Isabelle; the native engine targets the same specification and is checked
  against it by differential testing.
- **Online & incremental.** Each time-point is processed once on arrival; past
  results are reused via the sliding-window aux structures rather than
  recomputed.
- **Bounded latency.** A verdict for time-point `i` is emitted as soon as all
  future operators reaching past `i` are determined — i.e. once enough later
  time-stamps have been read. Past-only formulas have zero latency.
- **Finite memory in the windowed case.** For bounded intervals the auxiliary
  windows are bounded by the metric horizon (in time-stamp units) and the active
  relation sizes; unbounded past operators retain only the accumulated result,
  not the raw history.
- **State is serializable and sliceable**, enabling checkpoint/restore and
  data-parallel monitoring (hypercube slicing).

---

## 9. Map of the relevant source files

| File | Role |
|------|------|
| `src/algorithm.ml` | The native engine: `add_ext`, `add_index`, `eval`, `process_index`, the driver `Monitor`, marshalling, FRZ. |
| `src/extformula.ml(i)` | The `extformula` type and per-node auxiliary state records. |
| `src/optimized_mtl.ml(i)` | Sliding-window data structures `msaux` (SINCE) and `muaux` (UNTIL) with lookahead. |
| `src/neval.ml` | The shared time-point queue (`neval`) and cells. |
| `src/rewriting.ml` | Normalization and the monitorability check. |
| `src/relation.ml`, `src/table.ml`, `src/tuple.ml` | Finite relations and relational algebra (join, project, select, anti-join). |
| `src/aggreg.ml` | Incremental aggregation operators. |
| `src/verified.ml` | Isabelle-extracted verified kernel (`-verified` flag); same spec, proof-carrying. |
| `src/log_parser.ml` | Streaming log reader that drives `Monitor`. |

---

### One-paragraph summary

MonPoly compiles a safe-fragment MFOTL formula into an **extended formula** whose
every node carries the incremental state needed to produce its next output. A
shared **`neval` queue** records read-but-unevaluated time-points. As each
timestamped database arrives, new facts are pushed to the predicate leaves and the
engine evaluates the formula **bottom-up, on demand**: non-temporal nodes apply
relational algebra to finite relations; past operators read off **sliding
windows**; future operators **block** until enough later time-stamps make their
verdict final, then emit in time-point order with bounded latency. The **freeze**
quantifier pins a subformula's relation to its outer-time snapshot — served as a
constant for non-temporal bodies, or by cloning-and-driving a fresh evaluator per
outer time-point for temporal bodies. The result is an online monitor that emits,
for every time-point, the exact relation of satisfying valuations.
