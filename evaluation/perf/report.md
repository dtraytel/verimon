# Performance suite: monpoly vs verimon

Both systems from refine (66d9b447).  Run on 2026-09-24 on the same machine as `report0.md`, the starting point on master, so the two compare.

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 231 s (budget 2400 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 196 | 201 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 196 formulas both finish: geometric mean of verimon/monpoly = **0.95**, median 0.98, 116 where verimon is faster, 102 within 10%, 0 where verimon is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.00 | 0.92 | 1.08 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 0.95 | 0.85 | 1.01 | 0 | 0 | 0 |
| andnot | 8 | 8 | 0.90 | 0.84 | 1.06 | 0 | 0 | 0 |
| rel | 8 | 8 | 0.93 | 0.81 | 0.99 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 0.92 | 0.77 | 1.06 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 0.92 | 0.80 | 0.98 | 0 | 0 | 0 |
| once | 16 | 16 | 0.95 | 0.75 | 1.14 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 0.50 | 0.28 | 0.82 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.10 | 1.07 | 1.13 | 0 | 0 | 0 |
| since | 13 | 13 | 0.92 | 0.61 | 1.18 | 0 | 0 | 0 |
| eventually | 8 | 8 | 0.92 | 0.50 | 1.11 | 0 | 0 | 0 |
| until | 6 | 6 | 1.09 | 1.06 | 1.17 | 0 | 0 | 0 |
| burst | 9 | 9 | 0.99 | 0.88 | 1.17 | 0 | 0 | 0 |
| nested | 11 | 11 | 0.94 | 0.79 | 1.18 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.04 | 0.99 | 1.23 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.02 | 0.75 | 1.29 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 0.91 | 0.62 | 1.19 | 0 | 0 | 0 |
| let | 4 | 4 | 1.03 | 0.87 | 1.12 | 0 | 0 | 0 |
| wide | 8 | 8 | 0.95 | 0.85 | 1.04 | 0 | 0 | 0 |
| long | 12 | 12 | 0.97 | 0.68 | 1.15 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.02 | 0.69 | 1.48 | 0 | 0 | 0 |
| match | 11 | 11 | 0.93 | 0.78 | 1.13 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.27 | 0.40 | 1.48 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.44 | 0.61 | 1.39 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.56 | 0.71 | 1.29 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.55 | 0.71 | 1.29 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.46 | 0.57 | 1.25 |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.18 | 0.23 | 1.23 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.46 | 0.55 | 1.19 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.37 | 0.44 | 1.18 |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 0.61 | 0.71 | 1.18 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.47 | 0.56 | 1.18 |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.52 | 0.61 | 1.17 |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.46 | 0.54 | 1.17 |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.52 | 0.60 | 1.15 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 0.63 | 0.72 | 1.15 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.33 | 0.38 | 1.15 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 0.83 | 0.24 | 0.28 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.75 | 0.27 | 0.36 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.57 | 0.28 | 0.50 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.53 | 0.28 | 0.52 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.50 | 0.30 | 0.61 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.02 | 0.63 | 0.62 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 1.95 | 1.32 | 0.68 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 0.84 | 0.58 | 0.69 |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.43 | 0.30 | 0.70 |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.49 | 0.37 | 0.74 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.32 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.33 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.56 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.33 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.30 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.21 | 0.20 | 0.98 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.24 | 0.24 | 0.97 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.20 | 0.22 | 1.08 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.24 | 0.25 | 1.03 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.22 | 0.22 | 1.03 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.23 | 0.22 | 0.96 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.20 | 0.19 | 0.96 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.13 | 0.12 | 0.92 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.20 | 0.21 | 1.06 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.06 | 0.06 | 1.01 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.25 | 0.24 | 0.96 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.53 | 0.50 | 0.96 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.29 | 0.24 | 0.85 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.22 | 0.22 | 1.00 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.27 | 0.22 | 0.84 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.23 | 0.20 | 0.85 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.27 | 0.25 | 0.90 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.26 | 0.26 | 0.98 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.20 | 0.18 | 0.93 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.25 | 0.26 | 1.06 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.25 | 0.21 | 0.86 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.25 | 0.21 | 0.84 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.20 | 0.18 | 0.90 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.17 | 0.16 | 0.97 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.18 | 0.17 | 0.96 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.20 | 0.18 | 0.89 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.24 | 0.20 | 0.81 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.25 | 0.24 | 0.95 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.24 | 0.24 | 0.99 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.18 | 0.18 | 0.97 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.31 | 0.24 | 0.77 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.27 | 0.23 | 0.84 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.20 | 0.20 | 1.02 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.25 | 0.22 | 0.90 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.22 | 0.23 | 1.06 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.20 | 0.19 | 0.98 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.15 | 0.14 | 0.94 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.15 | 0.14 | 0.96 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.20 | 0.18 | 0.90 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.18 | 0.18 | 0.98 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.24 | 0.19 | 0.80 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.23 | 0.20 | 0.86 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.19 | 0.17 | 0.92 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.18 | 0.17 | 0.98 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.16 | 0.15 | 0.97 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.19 | 0.17 | 0.88 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.25 | 0.18 | 0.75 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.27 | 0.28 | 1.03 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.31 | 0.34 | 1.11 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.44 | 0.49 | 1.11 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 0.57 | 0.65 | 1.14 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 0.55 | 0.58 | 1.06 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.43 | 0.36 | 0.84 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 0.60 | 0.49 | 0.82 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 0.74 | 0.61 | 0.83 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 0.66 | 0.57 | 0.85 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 0.71 | 0.54 | 0.76 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.41 | 0.46 | 1.11 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.41 | 0.40 | 0.99 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.45 | 0.51 | 1.13 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.37 | 0.30 | 0.82 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.53 | 0.28 | 0.52 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.75 | 0.27 | 0.36 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.43 | 0.30 | 0.70 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 0.83 | 0.24 | 0.28 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.08 | 0.09 | 1.07 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.80 | 0.90 | 1.13 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.39 | 0.42 | 1.07 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.35 | 0.40 | 1.13 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.35 | 0.27 | 0.77 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.36 | 0.28 | 0.79 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.35 | 0.28 | 0.79 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.29 | 0.27 | 0.93 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.29 | 0.28 | 0.97 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.29 | 0.28 | 0.95 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.37 | 0.44 | 1.18 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.43 | 0.49 | 1.14 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.44 | 0.50 | 1.14 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.45 | 0.44 | 0.96 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 0.63 | 0.62 | 0.98 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.50 | 0.30 | 0.61 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.24 | 0.24 | 0.99 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.29 | 0.27 | 0.95 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.42 | 0.46 | 1.11 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 0.61 | 0.68 | 1.11 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.37 | 0.33 | 0.88 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.49 | 0.49 | 1.01 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 0.63 | 0.69 | 1.10 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.20 | 0.17 | 0.88 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.57 | 0.28 | 0.50 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.33 | 0.35 | 1.06 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.34 | 0.37 | 1.07 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.35 | 0.37 | 1.07 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.26 | 0.28 | 1.06 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.28 | 0.31 | 1.11 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.46 | 0.54 | 1.17 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.47 | 0.43 | 0.90 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 0.59 | 0.56 | 0.95 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 0.66 | 0.64 | 0.97 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.19 | 0.19 | 1.00 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.31 | 0.31 | 1.00 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.31 | 0.31 | 1.01 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.28 | 0.29 | 1.07 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.52 | 0.61 | 1.17 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.31 | 0.27 | 0.88 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.33 | 0.33 | 0.99 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.74 | 0.66 | 0.89 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.34 | 1.07 | 0.79 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.49 | 0.45 | 0.91 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.77 | 0.67 | 0.87 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.78 | 0.69 | 0.88 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.52 | 0.60 | 1.15 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.39 | 0.34 | 0.87 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.37 | 0.33 | 0.89 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.36 | 0.35 | 0.99 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 0.61 | 0.71 | 1.18 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.25 | 0.25 | 1.00 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.25 | 0.25 | 1.00 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.25 | 0.25 | 1.00 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.25 | 0.25 | 0.99 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.30 | 0.31 | 1.03 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.30 | 0.31 | 1.04 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.18 | 0.23 | 1.23 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.25 | 0.26 | 1.02 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.49 | 0.47 | 0.96 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 0.63 | 0.59 | 0.94 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 0.63 | 0.66 | 1.04 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.48 | 0.47 | 0.98 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.62 | 0.59 | 0.94 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 0.64 | 0.66 | 1.04 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.45 | 0.51 | 1.13 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.56 | 0.71 | 1.29 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.55 | 0.71 | 1.29 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.63 | 0.68 | 1.09 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.83 | 0.91 | 1.09 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 0.67 | 0.73 | 1.10 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 0.94 | 1.06 | 1.13 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.16 | 0.16 | 1.01 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.16 | 0.17 | 1.04 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.16 | 0.16 | 1.03 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.16 | 0.16 | 1.01 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.29 | 0.23 | 0.80 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.29 | 0.22 | 0.75 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.86 | 0.95 | 1.10 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.33 | 0.38 | 1.15 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.31 | 0.98 | 0.75 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 0.64 | 0.51 | 0.79 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.02 | 0.63 | 0.62 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.29 | 0.31 | 1.08 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.46 | 0.55 | 1.19 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 0.63 | 0.62 | 0.99 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.27 | 0.23 | 0.87 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.19 | 0.21 | 1.06 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.23 | 0.25 | 1.09 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.24 | 0.26 | 1.12 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.19 | 0.18 | 0.94 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.22 | 0.21 | 0.97 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.25 | 0.25 | 1.02 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.25 | 0.21 | 0.85 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.21 | 0.20 | 0.94 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.19 | 0.17 | 0.89 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.18 | 0.18 | 0.99 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.25 | 0.26 | 1.04 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.31 | 0.33 | 1.04 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.42 | 0.47 | 1.12 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 0.63 | 0.72 | 1.15 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 0.65 | 0.71 | 1.09 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.65 | 0.54 | 0.83 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 0.70 | 0.63 | 0.89 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 0.61 | 0.61 | 1.01 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 0.74 | 0.78 | 1.06 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.38 | 0.32 | 0.84 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.24 | 0.25 | 1.05 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.23 | 0.24 | 1.04 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 1.95 | 1.32 | 0.68 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.25 | 0.23 | 0.92 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.34 | 0.28 | 0.82 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 0.84 | 0.58 | 0.69 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.49 | 0.37 | 0.74 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.27 | 0.40 | 1.48 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.44 | 0.61 | 1.39 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.27 | 0.29 | 1.07 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.47 | 0.56 | 1.18 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.46 | 0.57 | 1.25 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.25 | 0.24 | 0.97 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.21 | 0.20 | 0.95 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.22 | 0.22 | 0.98 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.28 | 0.24 | 0.89 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.21 | 0.20 | 0.91 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.30 | 0.23 | 0.78 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.21 | 0.19 | 0.90 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.31 | 0.25 | 0.83 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.25 | 0.20 | 0.81 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.31 | 0.36 | 1.13 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.20 | 0.22 | 1.10 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.17 | 0.16 | 0.98 | yes | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.32 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.33 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.56 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.33 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.30 | - | yes | the trigger narrower than the conjunct |
