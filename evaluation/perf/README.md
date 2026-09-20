# Performance suite: the verified dense evaluator against MonPoly

A few hundred formulas, organised in families with parameter sweeps, each run under MonPoly and
under the verified dense evaluator (`-verified -vdense`, `Dense_Eval.thy` through the queue
buffers of `Dense_Exec.thy`) on the same log, with a 5-second timeout per run, best of a few
repetitions, in about 20 minutes on four cores.

```
python3 gen_logs.py                 # eight synthetic logs (about 45 MB), a few seconds
python3 gen_formulas.py             # formulas/*.mfotl and formulas/suite.json (committed)
python3 run_suite.py                # results/{results.json,results.csv,report.md}
```

`run_suite.py` takes `--bin` (default: the tree's `_build/default/src/main.exe`), `--reps`
(default 2, at most 3), `--timeout` (5 s), `--jobs` (2 workers), `--budget` (1800 s of wall
time), `--systems` (`monpoly,vdense`; add `dense` for the shipping dense monitor) and
`--families`/`--names` to run a subset.  Repetitions are interleaved across the systems.  When
the projected wall time exceeds the budget the remaining formulas get one repetition, and if
even that would exceed it they are skipped; the report says which happened.

## The logs

One signature, `A(int,int) B(int,int) C(int) D(int,int,int)`, values uniform in a domain.
`base` is 6000 time points, one per second, 40 A, 40 B, 10 C and 10 D per time point, domain
200.  The others vary one dimension: `rate10/20/80` the events per time point, `dom50/1000` the
domain (join selectivity, number of groups), `burst` sixty time points per timestamp (what a
bounded future operator has to buffer), `long` 30000 time points with 8 A and B each (long
windows).

## The families

| family | shape | sweep |
|---|---|---|
| join, join_rate, join_dom | conjunctions of 2-4 predicates | shared variables; rate; domain |
| andnot, andnot_dom, rel, or, exists | negation, constraints, disjunction, quantifiers | |
| prevnext | Prev and Next | |
| once_raw, once_guard, once_first, once_lb, once_inf, once_exists, once_rate, once_dom | ONCE | window bound 0..2000, lower bound, unbounded; rate; domain |
| since | SINCE, unary/binary/negated left operand | window bound |
| eventually, eventually_raw, eventually_burst, until, until_burst | bounded futures | window bound, on one-per-second and bursty logs |
| nested | temporal operators under temporal operators | bounds |
| agg, agg_once, agg_once_cnt, agg_dom, agg_rate, agg_ev, agg_guard | aggregations, alone and over ONCE/EVENTUALLY | operator, window bound; rate; domain |
| let | LET-bound predicates | |
| wide | ternary predicates under the temporal operators | window bound |
| long | long windows on the long thin log | 10..10000 |
| policy | policy-shaped formulas (P2/P3 and relatives) | |

Wide temporal subformulas are guarded (`A(x,y) AND ONCE[0,b] B(x,y)`, `A(x,y) AND NOT
ONCE[1,b] A(x,y)`) so that the verdict stays a few tuples per time point and the measured time
is the operator's, not the printer's.

## The report

`report.md` gives, per system: the counts of finished, timed-out, refused and erroneous runs;
the geometric mean and median of the runtime ratio over the formulas both finish; the ratio per
family with its extremes; the fifteen formulas where the verified evaluator is slowest relative
to MonPoly and the ten where it is fastest; every timeout, refusal and error; and the full table.
The verdicts of the two systems are hashed and compared, and disagreements are listed.
