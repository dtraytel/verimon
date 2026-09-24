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

`report.md` and `ratios.svg` in this directory are a run of 2026-09-24 after 21.39 (27ea1aaf),
and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  Both ran on the same local machine, with the same suite,
logs and settings, so their numbers compare; master did not change, so its run was not repeated
for the refine runs after 21.34.  That machine is about twice as fast as the container of the runs
up to 21.33 (the refine suite takes 218 s against 505 s there), so earlier runs compare with these
only through their ratios.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 5 | 0 |
| MonPoly timeouts | 0 | 0 |
| both finish | 191 | 196 |
| geometric mean VeriMon/MonPoly | 2.63 | 0.81 |
| median VeriMon/MonPoly | 2.76 | 0.83 |
| VeriMon faster / more than 2x slower | 0 / 136 | 172 / 0 |

The verified monitor is faster than MonPoly on the geometric mean and on 172 of the 196 formulas;
every group is below 1x (the highest are `once_scale` at 0.96, then `agg`, `agg_once`, `let` and
`policy` at 0.88 or 0.89), and no formula is above 1.25x.  The master run has one verdict
disagreement, `match-pcnt`, an end-of-stream difference between MonPoly and the verified monitor
that the original VeriMon shares; the refine run has none since EFFICIENCY.md 21.31.  The
`andtrigger` group has no ratio against MonPoly, which does not monitor TRIGGER; the reports record
the verified monitor's times alone.  The reports give times to 10 ms, which at this machine's speed
(typically 0.1 s to 0.6 s per formula) makes a single formula's ratio uncertain by a few percent,
and on the shortest formulas by up to 10%.

Against the previous refine run on this machine (e795b516, after 21.37, geometric mean 0.93),
MonPoly's times are unchanged (0.998x over the 196 formulas) and the verified monitor's are 0.88x.
Most of that is common to all groups, which each dropped by 0.05 to 0.20: `-verified` now reads the
log with the verified log parser of session `Log_Parser` (merged into refine at 27ea1aaf), while
MonPoly keeps its own parser, and on the shortest formulas, where reading the log is most of the
run, the ratio went from about 0.9 to about 0.65 (`prev-unary`, `join-self3`, `once-raw5`).  On top
of that are 21.38 and 21.39, the per-tuple descents and the result upkeep of the aggregations over
a past window: `pol-sumfilter` went from 1.35 to 0.82 (the comparison now reaches the window
aggregate as its guard), `aggonce-min50` and `aggonce-max50` from 1.25 to 0.99 and 0.98 (MIN and
MAX keep their result table), `aggguard-sum` from 1.16 to 1.00 and `once-rate80` from 1.09 to 0.98.
The largest ratios left are `pol-threshold` (1.25; a count over a window, where the per-tuple work
is two tree descents against MonPoly's two hash-table lookups, 21.39), `pol-sincefutb` (1.18) and
`pol-sincefut`, `once-g500` (1.10).  The earlier refine runs had taken the geometric mean from 1.13
to 1.06 after 21.29 and 21.30 (the red-black trees' rebalancing), the `match` group from 1.39 to
1.00 after 21.31, the `until` group from 1.31 to 1.16 after 21.32, the `since` group from 1.23 to
0.94 after 21.33, and, on this machine, the geometric mean from 0.95 after 21.34 to 0.93 after 21.37
(the one-descent lookup and update of 21.35, the Since node's trees of 21.36 and the Until add step
of 21.37).

## The report

`report.md` gives, per system: the counts of finished, timed-out, refused and erroneous runs;
the geometric mean and median of the runtime ratio over the formulas both finish; the ratio per
family with its extremes; the fifteen formulas where the verified evaluator is slowest relative
to MonPoly and the ten where it is fastest; every timeout, refusal and error; and the full table
with each formula's reason.
The verdicts of the two systems are hashed and compared, and disagreements are listed.
