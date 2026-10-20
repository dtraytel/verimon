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
The `probe` group joins a guard with a large past, future or Let-bound window on the log `miss`
(1000 time points of base's shape, with the values of B, C and D shifted out of A's range), so
that the guard matches nothing and the join's cost is that of probing the window; its control
`probe-once-eq` binds all of the window's columns.

## Results

`report.md` and `ratios.svg` are a run of VeriMon 2.0 (b4d17739) against MonPoly's own algorithm,
with the whole suite, 8 workers (`--monpoly PATH --jobs 8`, the default systems
`monpoly,verimon`). The suite took 75 s of wall time.

| | verimon / monpoly |
|---|---|
| formulas both finish | 264 |
| geometric mean | 0.81 |
| median | 0.83 |
| verimon faster | 236 |
| within 10% | 81 |
| more than 2x slower | 0 |
| timeouts (5 s) | none |
| verdict disagreements | none |

MonPoly does not monitor 21 of the formulas (the `andtrigger` and `vm_only` groups, among them
`der-equiv` and `lp-chain`), which VeriMon runs in 0.2 to 0.8 s. The largest ratios are
`frz-neglag` (1.37), `frz-agg` (1.24), `frz-sincelag` (1.23) and `pol-sincefutb` (1.20); every
other formula is at most 1.13x. The fastest formulas relative to MonPoly are `frz-nested` (0.04),
`onceex-not50` (0.21) and `onceex-50` (0.27).

`ratios_v1.svg` (verimon/monpoly-verified) is from an earlier run of the same code against
VeriMon 1, on a noisier 2-worker machine (the suite took 1561 s there): a geometric mean of 0.98
over the 282 formulas both finish, none more than 2x slower, no verdict disagreements.

`report.md` gives, per system against the reference: the counts of finished, timed-out, refused
and erroneous runs; the geometric mean and median of the runtime ratio over the formulas both
finish; the ratio per family with its extremes; the fifteen formulas where the system is slowest
relative to the reference and the ten where it is fastest; every timeout, refusal and error; and
the full table with each formula's reason.
