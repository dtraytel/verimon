# Performance suite

285 hand-picked formulas in 30 groups, each there for a stated reason (`suite.txt`, one
annotated line per formula), run on synthetic logs under VeriMon (`verimon`) and, for
comparison, under an installed [MonPoly](https://bitbucket.org/jshs/monpoly), with a 5-second
timeout per run and the best of three repetitions.

```
python3 gen_logs.py                          # eleven synthetic logs (about 47 MB), a few seconds
dune build                                   # in the repository's root: _build/default/src/verimon.exe
python3 run_suite.py --monpoly PATH/monpoly  # results/{results.json,results.csv,report.md}
python3 plot.py                              # results/ratios.svg, the ratios per group
```

## Systems

| system | what runs |
|---|---|
| `verimon` | this repository's program (`--bin`, default `_build/default/src/verimon.exe`) |
| `monpoly` | MonPoly's own algorithm: the external binary without flags |
| `monpoly-verified` | VeriMon 1: the external binary with `-verified` |

MonPoly is not part of this repository. `--monpoly PATH` (default: `$MONPOLY`, else `monpoly` on
the PATH) names its binary; without one, `--systems verimon` runs VeriMon alone. The first system
of `--systems` (default `monpoly,verimon`) is the reference of the report's ratios. The verdicts
of the systems are hashed and compared, and disagreements are listed.

`run_suite.py` also takes `--suite` (`suite.txt`), `--reps` (default 3, at most 3), `--timeout`
(5 s), `--jobs` (2 workers), `--budget` (1800 s of wall time) and `--families`/`--names` to run a
subset. Repetitions are interleaved across the systems. When the projected wall time exceeds the
budget the remaining formulas get one repetition, and if even that would exceed it they are
skipped; the report says which happened.

## The groups

The groups cover the operators VeriMon supports: joins, anti-joins, constraints, assignments and
the arithmetic of terms (`terms`, with `tp` and `ts`), disjunction and the quantifiers, the
derived connectives (`derived`), Prev and Next, the past and future windows, Since and Until with
bounded and unbounded intervals (`past_inf`), the aggregations at one time point, over past and
future windows and over Since and Until (`agg_once`, `agg_fut`, `agg_more`), Let, the temporal
regexes, FRZ (`frz`, and `frz_rw` for the freezes the rewriter introduces), and, in `andtrigger`
and `vm_only`, the operators MonPoly does not monitor (TRIGGER, RELEASE, LETPAST, an unguarded
HISTORICALLY or ALWAYS, EQUIV), for which the report records VeriMon's times alone. VeriMon's
cost of FRZ grows with the square of the log's length, so the `frz` group runs on the short logs
`tp250`, `tp500` and `tp1000` (base's shape), and MonPoly runs FRZ with `-nofilteremptytp`,
since its filter of empty time points rejects FRZ.

## Results

`report.md`, `ratios.svg` (verimon/monpoly) and `ratios_v1.svg` (verimon/monpoly-verified) are
a run of VeriMon 2.0 (b4d17739) against MonPoly and VeriMon 1 as built from the branch
`refine-parser` (11815690), all three with OCaml 4.14.1 without flambda, the whole suite, 2
workers on a 4-core machine (`--systems monpoly,verimon,monpoly-verified`). The machine was
noisier than in earlier runs (the suite took 1561 s; single formulas varied by up to 1.6x between
repetitions), so the ratios are of one run, not of a stable baseline.

| | verimon / monpoly-verified | verimon / monpoly | monpoly / monpoly-verified |
|---|---|---|---|
| formulas both finish | 282 | 262 | 261 |
| geometric mean | 0.98 | 1.03 | 0.95 |
| median | 0.98 | 1.05 | 0.94 |
| first faster | 153 | 101 | 172 |
| more than 2x slower | 0 | 0 | 4 |
| verdict disagreements | none | none | none |

MonPoly does not monitor 21 of the formulas. Timeouts (5 s): `verimon` on `long-sum100`
(also MonPoly) and `lp-chain` (about 5 to 8 s here, against 2.7 to 3.3 s for VeriMon 1; its run
prints 100 MB of verdicts, and printing is where VeriMon 2.0 spends more than VeriMon 1);
`monpoly` on `once-first500` and `long-sum100`; `monpoly-verified` on `agg-medonce`. Against
VeriMon 1 the largest ratio is `since-u5` (1.45) and the smallest `frz-once5` (0.65); against
MonPoly the largest is `pol-sincefutb` (1.97) and the smallest `frz-nested` (0.04).

`report.md` gives, per system against the reference: the counts of finished, timed-out, refused
and erroneous runs; the geometric mean and median of the runtime ratio over the formulas both
finish; the ratio per family with its extremes; the fifteen formulas where the system is slowest
relative to the reference and the ten where it is fastest; every timeout, refusal and error; and
the full table with each formula's reason.
