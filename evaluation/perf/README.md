# Performance suite: the verified dense evaluator against MonPoly

271 hand-picked formulas in 29 groups, each there for a stated reason (`suite.txt`, one
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

`report.md` and `ratios.svg` in this directory are a run of 2026-09-26 on refine f52e017d, after
21.46, and `report0.md` and `ratios0.svg` the starting point: a build of master (025a1423), where
`-verified` is the original VeriMon.  Both ran with `run_both.sh` on the same machine, one after the
other, with the whole suite of 267 formulas, the same logs and the same settings (8 workers), so
their numbers compare.  The refine suite took 71 s of wall time, master's 187 s.

| | master | refine |
|---|---|---|
| VeriMon timeouts (5 s) | 17 | 0 |
| MonPoly timeouts | 0 | 0 |
| MonPoly does not monitor | 19 | 19 |
| both finish | 232 | 248 |
| geometric mean VeriMon/MonPoly | 3.60 | 0.84 |
| median VeriMon/MonPoly | 3.32 | 0.85 |
| VeriMon faster / more than 2x slower | 0 / 187 | 206 / 2 |

The verified monitor is faster than MonPoly on the geometric mean and on 206 of the 248 formulas
both finish.  Every group is at or below 1.00x (the highest are `once_scale` at 1.00 and `frz` at
0.97), but `frz` only on average: of its 21 formulas, `frz-oncelb` (6.7x) and `frz-prev` (6.0x) are the two formulas more than 2x slower.  There
the frozen predicate sits under a Since with a lower bound or under a Prev, where taking it out of
the window would change the first verdicts (21.43), so the monitor still replays the window.
Every other formula is at most 1.27x (`frz-agg`); then come `der-guardalw` (1.25, 21.44),
`frz-exists` (1.24) and `frz-once5` (1.21).  After them, the largest ratios outside `frz` are
`pol-sincefutb` (1.18), `since-nu5` and `pol-sincefut`, `once-g500` and `once-inf` (1.12 to 1.13;
`once-inf` keeps the whole history, 21.46).  The fastest formulas are `frz-nested` (0.05), which
master's VeriMon times out on, and `onceex-not50` (0.26).
There are no verdict disagreements; master's run has one, `match-pcnt`, an end-of-stream
difference that the original VeriMon has.  The `andtrigger` and `vm_only` groups (TRIGGER,
RELEASE, LETPAST, an unguarded HISTORICALLY or ALWAYS, EQUIV) have no ratio, since MonPoly does
not monitor them.  There the verified monitor takes 0.10 to 0.60 s, against 0.25 to 1.73 s and one
timeout (`lp-chain`) for master's; `rel-neg` went from 1.73 to 0.35 s, `der-always5` from 1.32 to
0.23 s.

The 66 formulas added since the last runs (the groups `frz`, `past_inf`, `derived`, `terms`,
`agg_more` and `vm_only`, and a few in the older groups) have a geometric mean of 0.87 over the 52
with a ratio.  On master they stood at 41x for `frz` (three timeouts), 2.2x to 3.2x for the others,
with three more timeouts (`agg-avgonce`, `agg-avgev`, `lp-chain`).  On the 196 formulas the previous refine run had in common with this one, the
geometric mean is 0.84 here against 0.80 there.  Master's rose on the same formulas from 2.55 to
2.98, so this machine and its 8 workers favour MonPoly more than the previous machine and its 2
workers did; the two runs compare only within themselves.  Within that shift, the aggregations
that 21.45 changed moved against the rest: `agg-nogroup` 1.04 to 0.78, `agg-max` 0.86 to 0.79 and
`agg-min` 0.84 to 0.79.  The largest increases (`join-self3` 0.63 to 0.76, `once-raw20` 0.51 to 0.61,
`next-burst` 0.78 to 0.92) are in code that nothing since then has touched.

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
