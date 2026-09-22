# Performance suite: the verified dense evaluator against MonPoly

185 hand-picked formulas in 21 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run under MonPoly and under the verified dense evaluator
(`-verified -vdense`, `Dense_Eval.thy` through the queue buffers of `Dense_Exec.thy`) on the
same log, with a 5-second timeout per run, best of three repetitions, in about a quarter of an
hour on four cores.

```
python3 gen_logs.py                 # eight synthetic logs (about 45 MB), a few seconds
python3 run_suite.py                # results/{results.json,results.csv,report.md}
python3 plot.py                     # results/ratios.svg, the ratios per group
```

`run_suite.py` takes `--bin` (default: the tree's `_build/default/src/main.exe`), `--suite`
(`suite.txt`), `--reps` (default 3, at most 3), `--timeout` (5 s), `--jobs` (2 workers),
`--budget` (1800 s of wall time), `--systems` (`monpoly,vdense`; add `dense` for the shipping
dense monitor) and `--families`/`--names` to run a subset.  Repetitions are interleaved across
the systems.  When the projected wall time exceeds the budget the remaining formulas get one
repetition, and if even that would exceed it they are skipped; the report says which happened.

`report.md` and `ratios.svg` in this directory are the run of 2026-09-22 on the machine of
EFFICIENCY.md Section 21 (four cores).

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
thin log; and policy-shaped formulas.  Bounds are chosen at the scales that matter on the log:
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
