# Performance suite: the verified dense evaluator against MonPoly

285 hand-picked formulas in 30 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run under MonPoly and under the verified dense evaluator
(`-verified`: `Dense_Eval.thy` over the short tuples of `Dense_Unbox_Exec.thy`; the system is
called `verimon` in the reports, `vdense` in earlier ones) on the same log, with a 5-second timeout per run, best of three repetitions, in 1 to 10 minutes
depending on the machine and the number of workers.

```
python3 gen_logs.py                 # eleven synthetic logs (about 47 MB), a few seconds
python3 run_suite.py                # results/{results.json,results.csv,report.md}
python3 plot.py                     # results/ratios.svg, the ratios per group
```

`run_both.sh` does the comparison the reports below are: it pulls the current branch
(fast-forward only), builds the checkout and master (025a1423, in a temporary worktree),
generates the logs if any are missing, runs the suite on master and then on the checkout,
installs `report0.md`/`ratios0.svg` (master) and `report.md`/`ratios.svg` (the checkout) with a
provenance line, commits those four files alone and pushes the branch (rebasing and retrying if
the push is rejected).  It refuses to start with other uncommitted changes unless `PUSH=0`.
`run_refine.sh` does the same for the checkout alone, for experiments against an existing
`report0.md`.  Both take `JOBS`, `REPS`, `TIMEOUT`, `BUDGET`, `PULL` and `PUSH` (0 to skip)
from the environment, and `NAMES=a,b,c` for a smoke test that installs, commits and pushes
nothing.

The groups cover the operators the verified monitor supports: joins, anti-joins, constraints,
assignments and the arithmetic of terms (`terms`, with `tp` and `ts`), disjunction and the
quantifiers, the derived connectives (`derived`), Prev and Next, the past and future windows,
Since and Until with bounded and unbounded intervals (`past_inf`), the aggregations at one time
point, over past and future windows and over Since and Until (`agg_once`, `agg_fut`, `agg_more`),
Let, the temporal regexes, FRZ (`frz`, and `frz_rw` for the freezes the rewriter introduces), and, in `andtrigger` and `vm_only`, the operators MonPoly
does not monitor (TRIGGER, RELEASE, LETPAST, an unguarded HISTORICALLY or ALWAYS, EQUIV), for which
the reports record the verified monitor's times alone.  The verified monitor's cost of FRZ grows
with the square of the log's length, so the `frz` group runs on the short logs `tp250`, `tp500`
and `tp1000` (base's shape), and MonPoly runs FRZ with `-nofilteremptytp`, since its filter of
empty time points rejects FRZ.

`run_suite.py` takes `--bin` (default: the tree's `_build/default/src/main.exe`), `--suite`
(`suite.txt`), `--reps` (default 3, at most 3), `--timeout` (5 s), `--jobs` (2 workers),
`--budget` (1800 s of wall time), `--systems` (`monpoly,verimon`) and `--families`/`--names`
to run a subset.  Runs before EFFICIENCY.md 21.26 had a third system, `dense`, the
heap-resident dense monitor that `-verified` ran then; it is no longer in the binary.  Repetitions are interleaved across
the systems.  When the projected wall time exceeds the budget the remaining formulas get one
repetition, and if even that would exceed it they are skipped; the report says which happened.

`report.md` and `ratios.svg` in this directory are a run of 2026-09-29 on refine 8c15b7af, after
EFFICIENCY.md 22.2, and `report0.md` and `ratios0.svg` the starting point: a build of master
(025a1423), where `-verified` is the original VeriMon.  Both ran on the same machine, with the
whole suite of 285 formulas, the same logs and the same settings (8 workers), so their numbers
compare.  The refine suite took 73 s of wall time, master's 198 s.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 25 | 0 |
| MonPoly timeouts | 0 | 0 |
| MonPoly does not monitor | 21 | 21 |
| both finish | 240 | 264 |
| geometric mean VeriMon/MonPoly | 3.69 | 0.82 |
| median VeriMon/MonPoly | 3.35 | 0.83 |
| VeriMon faster / more than 2x slower | 0 / 196 | 222 / 0 |

The verified monitor is faster than MonPoly on the geometric mean and on 222 of the 264 formulas
both finish, and no formula is more than 2x slower.  The largest ratios are `frz-agg` (1.39),
`frz-sincelag` (1.30), `frz-neglag` (1.26), `frz-sincelag30` (1.25) and `pol-sincefutb` (1.17);
every other formula is at most 1.16x (`frz-once5`, `der-guardalw`).  The fastest formulas are
`frz-nested` (0.05) and `onceex-not50` (0.26).  There are no verdict disagreements; master's run
has one, `match-pcnt`, an end-of-stream difference that the original VeriMon has.

22.1 (the initial state compiled from the formula by `udinit`, without the kernel's `mformula`)
and 22.2 (monomorphic copies of the generic operations a profile still found on the inner loops,
and the short tables' intersection specialised on their comparator) change the per-event code
only by the second, which cuts the instruction counts of the aggregation, FRZ, ONCE and `complex`
benchmarks by 1 to 4.5%.  That is below what this suite resolves: on the 264 formulas both runs
finish, the geometric mean is 0.819 against 0.822 on b4f4ca14, VeriMon's own times are 0.9%
shorter on the geometric mean and MonPoly's 0.3%, no family moved by more than 0.02, and 222
formulas are faster against 219.  Three formulas moved by 0.10 or more, both ways, on runs of
0.03 to 0.06 s: `frz-once20` 1.15 to 1.03 and the other way `frz-outer` 0.83 to 0.96 and
`frz-agg` 1.23 to 1.39.  The two runs in between, on 7427e589 (22.1) and 6576fc0e (22.2 without
the intersection), had geometric means of 0.826 and 0.822.

The run before (2026-09-28, b4f4ca14, after 22, the same machine and 285 formulas) had a
geometric mean of 0.82 against master's 3.69, 219 of 264 formulas faster and none above 2x;
22 (the executable kernel `meformula` and the queue-buffered `edformula` removed, `udformula`
refining `dformula` directly) had changed the proofs and the code of the initial state only.
The run before (2026-09-28, b2394a8c, after 21.57, the same machine and 285 formulas) had a
geometric mean of 0.82 against master's 3.69, 222 of 264 formulas faster and none above 2x;
21.57 (the frozen conjunct taken out of an existential quantifier, the quantifier moved into the
windows under a Let, and ALWAYS without the until node that never holds) had taken `frz-exists`
from 1.20 to 0.85 and `der-guardalw` from 1.23 to 1.16.
The run before (2026-09-28, 02686f21, after 21.56, the same machine and 285 formulas) had a
geometric mean of 0.82 against master's 3.69, 219 of 264 formulas faster and none above 2x;
21.56 (the Since node's bucket update in one descent without the old value, and the join's deleted
entries collected by a fold) had cut the allocation of `frz-sincelag30` by 9% without a
measurable change in time.
The `andtrigger` and `vm_only` groups (TRIGGER, RELEASE, LETPAST, an unguarded HISTORICALLY or
ALWAYS, EQUIV) have no ratio, since MonPoly does not monitor them.

The run before (2026-09-28, 51f91819, after 21.55, the same machine and 285 formulas) had a
geometric mean of 0.83 against master's 3.69, 217 of 264 formulas faster and none above 2x;
21.54 and 21.55 (the FRZ copies replay one time point fewer, are cut at their own anchors, and the
window moves between them) had taken `frz-sincelag30` from 2.79 to 1.33, `frz-neglag30` from 2.13
to 1.06, `frz-neglag` from 1.60 to 1.25 and `frz-sincelag` from 1.59 to 1.31.
The run before (2026-09-27, 9ab43937, after 21.51, the same machine and 285 formulas) had a
geometric mean of 0.83 against master's 3.69, 219 of 264 formulas faster and `frz-sincelag30`
(2.79) and `frz-neglag30` (2.13) the only two above 2x; 21.51 (the live FRZ copy) had taken
`frzrw-untilr` from 1.25 to 0.99 and the `frz_rw` group from 0.87 to 0.83.
The run before (2026-09-27, e8f0872a, after 21.50, the same machine and 285 formulas) had a
geometric mean of 0.84 against master's 3.71, 214 of 264 formulas faster and `frz-sincelag30`
(2.69) and `frz-neglag30` (2.11) the only two above 2x; 21.50 (the copies stop at the last pending
verdict) had taken `frz-sincelag` from 2.45 to 1.60 and `frz-neglag` from 2.12 to 1.59.
The run before (2026-09-27, 0af2c4ee, after 21.49, the same machine and 283 formulas) had a
geometric mean of 0.83 against master's 3.68, 216 of 262 formulas faster and `frz-sincelag` (2.45)
and `frz-neglag` (2.12) the only two above 2x.
The previous refine run (2026-09-26, f52e017d, after 21.46, the same machine and 267 formulas) had a
geometric mean of 0.84 against master's 3.60, 206 of 248 formulas faster and `frz-oncelb` and
`frz-prev` the only two above 2x.  The run before that, on the same machine at 8 workers, had shown
that this machine favours MonPoly more than the earlier 2-worker machine did: on 196 common
formulas master's geometric mean rose from 2.55 to 2.98 there.  The two machines' runs compare only
within themselves.

The previous refine run, on another machine with 2 workers and the 201 formulas of the suite then
(4192d9d6, after 21.41), had a geometric mean of 0.80 against master's 2.63, 176 of 196 formulas
faster and none above 1.15x; 21.40 (the count set by group) had taken `pol-threshold` from 1.25
to 1.04 and the `aggonce` counts and sums from about 0.85 to about 0.75.
The earlier refine runs had taken the geometric mean from 1.13 to 1.06 after 21.29 and 21.30 (the
red-black trees' rebalancing), the `match` group from 1.39 to 1.00 after 21.31, the `until` group
from 1.31 to 1.16 after 21.32, the `since` group from 1.23 to 0.94 after 21.33, and, on the
2-worker machine, the geometric mean from 0.95 after 21.34 to 0.93 after 21.37 (the one-descent lookup and
update of 21.35, the Since node's trees of 21.36 and the Until add step of 21.37) and to 0.81 after
21.39 (the verified log parser of session `Log_Parser`, merged at 27ea1aaf, which took the shortest
formulas from about 0.9 to about 0.65, and the aggregations' per-tuple descents and result upkeep of
21.38 and 21.39: `pol-sumfilter` 1.35 to 0.82, `aggonce-min50` and `aggonce-max50` 1.25 to 0.99 and
0.98).

## The report

`report.md` gives, per system: the counts of finished, timed-out, refused and erroneous runs;
the geometric mean and median of the runtime ratio over the formulas both finish; the ratio per
family with its extremes; the fifteen formulas where the verified evaluator is slowest relative
to MonPoly and the ten where it is fastest; every timeout, refusal and error; and the full table
with each formula's reason.
The verdicts of the two systems are hashed and compared, and disagreements are listed.
