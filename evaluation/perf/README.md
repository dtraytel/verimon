# Performance suite: the verified dense evaluator against MonPoly

283 hand-picked formulas in 30 groups, each there for a stated reason (`suite.txt`, one
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

`report.md` and `ratios.svg` in this directory are a run of 2026-09-27 on refine 0af2c4ee, after
21.49, and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  Both ran with `run_both.sh` on the same machine, one after the
other, with the whole suite of 283 formulas, the same logs and the same settings (8 workers), so
their numbers compare.  The refine suite took 74 s of wall time, master's 197 s.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 22 | 0 |
| MonPoly timeouts | 0 | 0 |
| MonPoly does not monitor | 21 | 21 |
| both finish | 241 | 262 |
| geometric mean VeriMon/MonPoly | 3.68 | 0.83 |
| median VeriMon/MonPoly | 3.34 | 0.85 |
| VeriMon faster / more than 2x slower | 0 / 197 | 216 / 2 |

The verified monitor is faster than MonPoly on the geometric mean and on 216 of the 262 formulas
both finish.  None is more than 2.45x slower.  The two above 2x are `frz-sincelag` (2.45) and
`frz-neglag` (2.12), where the frozen formula lags (`EVENTUALLY[0,3] C(x)`) and the frozen predicate
sits under a negation or in a Since's left operand, so every frozen table has its own replay of the
window (21.48).  On master both time out.  `frz-oncelb` and `frz-prev`, the two formulas above 2x in
the previous run (6.7x and 6.0x), are now at 1.13 and 0.71 (21.47).  Every other formula is at
most 1.26x (`frz-agg`); then come `der-guardalw` (1.25), `frz-exists` (1.24), `frzrw-untilr` (1.21)
and `pol-sincefutb` (1.20).  The fastest formulas are `frz-nested` (0.05) and `onceex-not50` (0.26).
There are no verdict disagreements; master's run has one, `match-pcnt`, an end-of-stream
difference that the original VeriMon has.

The new group `frz_rw` (21.49) holds eight freezes as the rewriter introduces them, with the guard's
frozen predicate under the temporal operator, on the full `base` log.  Its geometric mean is 0.86
(0.63 to 1.21); master's is 3.21 over seven, with `frzrw-once2` timing out.  Without 21.49 the
refine binary was quadratic on six of the eight (19 s on `tp1000` alone for a variant of
`frzrw-once2`).  The `frz` group is at 0.88.  Of the 16 formulas added since the previous run (six
in `frz`, eight in `frz_rw`, two in `vm_only`), the 14 with a ratio have a geometric mean of 0.96.
On the 248 formulas the two runs have in common, the geometric mean went from 0.845 to 0.827, and
master's is 3.60 in both runs, so the machine was the same.  Apart from `frz-oncelb` and `frz-prev`,
no formula moved by more than 0.15.
The `andtrigger` and `vm_only` groups (TRIGGER, RELEASE, LETPAST, an unguarded HISTORICALLY or
ALWAYS, EQUIV) have no ratio, since MonPoly does not monitor them.  There the verified monitor takes
0.10 to 0.59 s, against 0.26 to 1.73 s, one timeout (`lp-chain`) and one refusal (`der-equiv`) for
master's.

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
