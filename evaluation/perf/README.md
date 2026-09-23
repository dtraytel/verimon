# Performance suite: the verified dense evaluator against MonPoly

201 hand-picked formulas in 23 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run under MonPoly and under the verified dense evaluator
(`-verified`: `Dense_Eval.thy` over the short tuples of `Dense_Unbox_Exec.thy`; the system is
called `verimon` in the reports, `vdense` in earlier ones) on the same log, with a 5-second timeout per run, best of three repetitions, in about a quarter of an
hour on four cores.

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

`report.md` and `ratios.svg` in this directory are a run of 2026-09-23 after 21.27 (574862ac),
and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  The two ran on the same otherwise idle four-core
container, with the same suite, logs and settings, so their numbers compare; that container is neither the machine of EFFICIENCY.md Section 21 nor the one of the 21.26 run it
reports (geometric mean 1.25, no timeouts), so they compare with neither.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 79 | 3 |
| MonPoly timeouts | 2 | 1 |
| both finish | 117 | 193 |
| geometric mean VeriMon/MonPoly | 2.68 | 1.33 |
| VeriMon faster / more than 2x slower | 0 / 91 | 22 / 13 |

MonPoly itself takes 0.87x its master time in the refine run, over the 194 formulas it finishes
in both (an earlier refine run on the same container, after 21.26, put it at 0.86x and VeriMon
at 0.99x its time here, with `aggonce-med20` a timeout that the rank trees of 21.27 bring to
4.1 s); the branch changes `tuple.ml` and `predicate.ml`, which MonPoly shares, so not all of
that is noise.  Both runs have one verdict disagreement, `match-pcnt`, an end-of-stream
difference between MonPoly and the verified monitor that the original VeriMon shares.  The
`andtrigger` group has no ratio against MonPoly, which does not monitor TRIGGER; the reports
record the verified monitor's times alone.

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
