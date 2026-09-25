# Performance suite: the verified dense evaluator against MonPoly

267 hand-picked formulas in 29 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run under MonPoly and under the verified dense evaluator
(`-verified`: `Dense_Eval.thy` over the short tuples of `Dense_Unbox_Exec.thy`; the system is
called `verimon` in the reports, `vdense` in earlier ones) on the same log, with a 5-second timeout per run, best of three repetitions, in 4 to 15 minutes on
four cores depending on the machine.

```
python3 gen_logs.py                 # eleven synthetic logs (about 47 MB), a few seconds
python3 run_suite.py                # results/{results.json,results.csv,report.md}
python3 plot.py                     # results/ratios.svg, the ratios per group
```

The groups cover the operators the verified monitor supports: joins, anti-joins, constraints,
assignments and the arithmetic of terms (`terms`, with `tp` and `ts`), disjunction and the
quantifiers, the derived connectives (`derived`), Prev and Next, the past and future windows,
Since and Until with bounded and unbounded intervals (`past_inf`), the aggregations at one time
point, over past and future windows and over Since and Until (`agg_once`, `agg_fut`, `agg_more`),
Let, the temporal regexes, FRZ (`frz`), and, in `andtrigger` and `vm_only`, the operators MonPoly
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

`report.md` and `ratios.svg` in this directory are a run of 2026-09-25 after 21.41 (4192d9d6),
and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  Both ran on the same local machine, with the same suite,
logs and settings, so their numbers compare; master did not change, so its run was not repeated
for the refine runs after 21.34.  That machine is about twice as fast as the container of the runs
up to 21.33 (the refine suite takes 216 s against 505 s there), so earlier runs compare with these
only through their ratios.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 5 | 0 |
| MonPoly timeouts | 0 | 0 |
| both finish | 191 | 196 |
| geometric mean VeriMon/MonPoly | 2.63 | 0.80 |
| median VeriMon/MonPoly | 2.76 | 0.82 |
| VeriMon faster / more than 2x slower | 0 / 136 | 176 / 0 |

The verified monitor is faster than MonPoly on the geometric mean and on 176 of the 196 formulas;
every group is below 1x (the highest are `once_scale` at 0.97, then `agg` at 0.89 and `let` at
0.88), and no formula is above 1.15x.  The master run has one verdict disagreement, `match-pcnt`,
an end-of-stream difference between MonPoly and the verified monitor that the original VeriMon
shares; the refine run has none since EFFICIENCY.md 21.31.  The `andtrigger` group has no ratio
against MonPoly, which does not monitor TRIGGER; the reports record the verified monitor's times
alone.  The reports give times to 10 ms, which at this machine's speed (typically 0.1 s to 0.6 s per
formula) makes a single formula's ratio uncertain by a few percent, and on the shortest formulas by
up to 10%.

Against the previous refine run on this machine (27ea1aaf, after 21.39, geometric mean 0.81),
MonPoly's times are unchanged (1.003x over the 196 formulas) and the verified monitor's are 0.98x.
The change is concentrated where 21.40 applies, the counts and sums over a past window, whose count
set is now kept by group: `pol-threshold` went from 1.25 to 1.04, `pol-sumfilter` from 0.82 to
0.67, `aggguard-sum` from 1.00 to 0.87, and the `aggonce` counts and sums from about 0.85 to about
0.75 (`agg_once` 0.88 to 0.82, `policy` 0.88 to 0.84).  21.41, the deletions' rebalancing, shows as
a few percent on the Since and Until formulas: `pol-sincefutb` 1.18 to 1.14, `pol-sincefut` 1.10 to
1.07, `once-g500` 1.10 to 1.06, `since-nu5` 1.08 to 1.06.  The largest ratios left are
`pol-sincefutb` (1.14; more than half of its allocation is the front end, about a third the Since
node's three trees, 21.41), `aggonce-med20` (1.10) and `ev-g500`, `pol-sincefut` (1.07); `ev-g500`
and `aggonce-med20` moved up by 0.05, which 21.40 and 21.41 do not touch and which is within this
machine's run-to-run spread on single formulas.

The earlier refine runs had taken the geometric mean from 1.13 to 1.06 after 21.29 and 21.30 (the
red-black trees' rebalancing), the `match` group from 1.39 to 1.00 after 21.31, the `until` group
from 1.31 to 1.16 after 21.32, the `since` group from 1.23 to 0.94 after 21.33, and, on this
machine, the geometric mean from 0.95 after 21.34 to 0.93 after 21.37 (the one-descent lookup and
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
