# Performance suite: the verified dense evaluator against MonPoly

201 hand-picked formulas in 23 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run under MonPoly and under the verified dense evaluator
(`-verified`: `Dense_Eval.thy` over the short tuples of `Dense_Unbox_Exec.thy`; the system is
called `verimon` in the reports, `vdense` in earlier ones) on the same log, with a 5-second timeout per run, best of three repetitions, in 4 to 15 minutes on
four cores depending on the machine.

```
python3 gen_logs.py                 # eight synthetic logs (about 45 MB), a few seconds
python3 run_suite.py                # results/{results.json,results.csv,report.md}
python3 plot.py                     # results/ratios.svg, the ratios per group
```

`run_suite.py` takes `--bin` (default: the tree's `_build/default/src/main.exe`), `--suite`
(`suite.txt`), `--reps` (default 3, at most 3), `--timeout` (5 s), `--jobs` (2 workers),
`--budget` (1800 s of wall time), `--systems` (`monpoly,verimon`) and `--families`/`--names`
to run a subset.  Runs before EFFICIENCY.md 21.26 had a third system, `dense`, the
heap-resident dense monitor that `-verified` ran then; it is no longer in the binary.  Repetitions are interleaved across
the systems.  When the projected wall time exceeds the budget the remaining formulas get one
repetition, and if even that would exceed it they are skipped; the report says which happened.

`report.md` and `ratios.svg` in this directory are a run of 2026-09-24 after 21.37 (e795b516),
and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  Both ran on the same local machine, with the same suite,
logs and settings, so their numbers compare; master did not change, so its run was not repeated
for the refine runs after 21.34.  That machine is about twice as fast as the container of the runs
up to 21.33 (the refine suite takes 228 s against 505 s there), so earlier runs compare with these
only through their ratios.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 5 | 0 |
| MonPoly timeouts | 0 | 0 |
| both finish | 191 | 196 |
| geometric mean VeriMon/MonPoly | 2.63 | 0.93 |
| median VeriMon/MonPoly | 2.76 | 0.96 |
| VeriMon faster / more than 2x slower | 0 / 136 | 126 / 0 |

The verified monitor is faster than MonPoly on the geometric mean and on 126 of the 196 formulas,
and no group is slower than 1.06x (`once_scale`, then `agg` and `let` at 1.02).  Over the formulas
the original VeriMon finishes, the verified monitor of refine takes 0.34x its time.  MonPoly takes
0.88x its master time over the formulas it finishes in both; the branch changes `tuple.ml` and
`predicate.ml`, which MonPoly shares, and the rest is the machine's run-to-run drift, which is why
the ratios, not the times, compare across runs.  The master run has one verdict disagreement,
`match-pcnt`, an end-of-stream difference between MonPoly and the verified monitor that the
original VeriMon shares; the refine run has none since EFFICIENCY.md 21.31.  The `andtrigger` group
has no ratio against MonPoly, which does not monitor TRIGGER; the reports record the verified
monitor's times alone.  The reports give times to 10 ms, which at this machine's speed (typically
0.2 s to 0.6 s per formula) makes a single formula's ratio uncertain by a few percent.

Against the previous refine run on this machine (2955f7f5, after 21.36, geometric mean 0.94), the
`until` group went from 1.10 to 0.91 -- 21.37, the Until add step's per-tuple work, whose worst
formula `until-nu20` went from 1.17 to 1.06 -- and `burst`, which holds Until formulas too, from
0.99 to 0.94; the other groups moved by 0.02 or less.  `once_scale` executes as many instructions as
MonPoly (1.035 on `once-rate80`); its gap is first-level cache misses on the trees' rebuilt paths
(21.37).  The largest ratios left are the aggregations over a past window and the Since node with a
negated left operand: `pol-threshold` (1.40), `pol-sumfilter` (1.35), `aggonce-min50` and
`aggonce-max50` (1.25), `pol-sincefutb` (1.22).  The earlier refine runs had taken the geometric
mean from 1.13 to 1.06 after 21.29 and 21.30 (the red-black trees' rebalancing), the `match` group
from 1.39 to 1.00 after 21.31, the `until` group from 1.31 to 1.16 after 21.32, the `since` group
from 1.23 to 0.94 after 21.33, and, on this machine, the geometric mean from 0.95 after 21.34 to
0.94 after 21.36 (the one-descent lookup and update of 21.35 and the Since node's trees of 21.36).

## The logs

One signature, `A(int,int) B(int,int) C(int) D(int,int,int)`, values uniform in a domain.
`base` is 6000 time points, one per second, 40 A, 40 B, 10 C and 10 D per time point, domain
200.  The others vary one dimension: `rate10/20/80` the events per time point, `dom50/1000` the
domain (join selectivity, number of groups), `burst` sixty time points per timestamp (what a
bounded future operator has to buffer), `long` 30000 time points with 8 A and B each (long
windows).

## The groups

`suite.txt` says, per formula, what it is there for.  The groups: joins by shape and as the
rate and domain grow; anti-joins; constraints and assignments; disjunction and quantifiers;
Prev and Next; the past window by its bound, with a positive lower bound, unbounded, and under
a quantifier the guard cannot pass; Since by the shape of its left operand; the bounded future
and Until likewise, and both on the bursty log; nested temporal operators; aggregations at a
time point, over a past window (grouped, ungrouped, every operator), over a future window and
under guards; Let; ternary predicates under the temporal operators; long windows on the long
thin log; policy-shaped formulas; the temporal regex nodes, by the shape of the regex and
in the past and the future; and the conjunction with a trigger whose interval misses zero.  Bounds are chosen at the scales that matter on the log:
a handful of time points, a few tens, a few hundreds (where a window of binary tuples over a
domain of 200 by 200 saturates), and thousands on the thin log.

Wide temporal subformulas are guarded (`A(x,y) AND ONCE[0,b] B(x,y)`, `A(x,y) AND NOT
ONCE[1,b] A(x,y)`) so that the verdict stays a few tuples per time point and the measured time
is the operator's, not the printer's.

## The report

`report.md` gives, per system: the counts of finished, timed-out, refused and erroneous runs;
the geometric mean and median of the runtime ratio over the formulas both finish; the ratio per
family with its extremes; the fifteen formulas where the verified evaluator is slowest relative
to MonPoly and the ten where it is fastest; every timeout, refusal and error; and the full table
with each formula's reason.
The verdicts of the two systems are hashed and compared, and disagreements are listed.
