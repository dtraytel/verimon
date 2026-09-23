# Performance suite: monpoly vs verimon

Both systems from refine after EFFICIENCY.md 21.32 (701a880).  Run on 2026-09-23 on the same container as `report0.md`, the starting point on master, so the two compare.

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 510 s (budget 2400 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 196 | 201 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 196 formulas both finish: geometric mean of verimon/monpoly = **1.05**, median 1.04, 74 where verimon is faster, 85 within 10%, 0 where verimon is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.05 | 0.97 | 1.14 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.01 | 0.93 | 1.08 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.01 | 0.92 | 1.16 | 0 | 0 | 0 |
| rel | 8 | 8 | 0.99 | 0.88 | 1.07 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.03 | 0.89 | 1.18 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 0.95 | 0.86 | 1.04 | 0 | 0 | 0 |
| once | 16 | 16 | 0.98 | 0.71 | 1.28 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 0.56 | 0.32 | 0.89 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.09 | 1.01 | 1.19 | 0 | 0 | 0 |
| since | 13 | 13 | 1.23 | 0.53 | 1.89 | 0 | 0 | 0 |
| eventually | 8 | 8 | 0.95 | 0.55 | 1.23 | 0 | 0 | 0 |
| until | 6 | 6 | 1.16 | 1.06 | 1.27 | 0 | 0 | 0 |
| burst | 9 | 9 | 0.99 | 0.85 | 1.20 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.05 | 0.89 | 1.38 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.15 | 1.06 | 1.21 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.21 | 0.88 | 1.71 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 1.11 | 0.76 | 1.33 | 0 | 0 | 0 |
| let | 4 | 4 | 1.16 | 0.99 | 1.24 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.02 | 0.86 | 1.14 | 0 | 0 | 0 |
| long | 12 | 12 | 1.05 | 0.84 | 1.20 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.16 | 0.72 | 1.90 | 0 | 0 | 0 |
| match | 11 | 11 | 0.97 | 0.82 | 1.22 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.01 | 1.92 | 1.90 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.76 | 1.44 | 1.89 |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.64 | 1.11 | 1.73 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.95 | 1.62 | 1.71 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.93 | 1.57 | 1.69 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.98 | 1.63 | 1.66 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.94 | 1.54 | 1.64 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.11 | 1.79 | 1.62 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.02 | 1.56 | 1.53 |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.54 | 0.81 | 1.50 |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.56 | 0.84 | 1.50 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.26 | 1.81 | 1.44 |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.63 | 0.88 | 1.39 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.78 | 1.07 | 1.38 |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.16 | 1.59 | 1.38 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.67 | 0.53 | 0.32 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.46 | 0.65 | 0.45 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.12 | 0.59 | 0.53 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.16 | 0.64 | 0.55 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.11 | 0.63 | 0.57 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.39 | 0.99 | 0.71 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.62 | 1.17 | 0.72 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.96 | 1.50 | 0.76 |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.82 | 0.64 | 0.77 |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.05 | 0.83 | 0.80 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.71 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.74 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.23 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.73 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.68 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.36 | 0.35 | 0.97 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.52 | 0.53 | 1.01 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.39 | 0.44 | 1.14 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.49 | 0.55 | 1.11 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.44 | 0.46 | 1.04 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.49 | 0.47 | 0.97 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.37 | 0.40 | 1.08 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.22 | 0.24 | 1.08 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.36 | 0.37 | 1.02 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.12 | 0.13 | 1.08 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.46 | 0.47 | 1.03 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.89 | 0.89 | 0.99 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.52 | 0.48 | 0.93 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.42 | 0.43 | 1.03 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.47 | 0.44 | 0.92 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.44 | 0.41 | 0.94 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.48 | 0.51 | 1.05 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.49 | 0.54 | 1.09 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.38 | 0.37 | 0.98 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.46 | 0.53 | 1.16 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.45 | 0.44 | 0.96 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.46 | 0.44 | 0.97 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.38 | 0.37 | 0.97 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.28 | 0.28 | 1.01 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.35 | 0.37 | 1.07 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.38 | 0.37 | 0.98 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.44 | 0.39 | 0.88 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.47 | 0.47 | 1.00 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.45 | 0.46 | 1.02 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.36 | 0.36 | 1.00 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.52 | 0.46 | 0.89 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.50 | 0.45 | 0.90 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.39 | 0.46 | 1.18 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.48 | 0.47 | 0.97 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.35 | 0.42 | 1.18 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.40 | 0.43 | 1.08 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.30 | 0.30 | 1.02 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.29 | 0.29 | 1.01 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.38 | 0.33 | 0.88 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.33 | 0.35 | 1.04 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.43 | 0.38 | 0.89 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.46 | 0.40 | 0.86 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.36 | 0.34 | 0.94 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.33 | 0.33 | 1.00 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.32 | 0.31 | 0.95 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.39 | 0.35 | 0.90 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.44 | 0.37 | 0.85 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.48 | 0.53 | 1.09 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.60 | 0.60 | 1.00 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.89 | 0.94 | 1.06 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.21 | 1.44 | 1.19 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.17 | 1.31 | 1.13 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.81 | 0.65 | 0.80 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.17 | 0.98 | 0.83 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 1.64 | 1.46 | 0.89 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.31 | 1.18 | 0.90 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.39 | 0.99 | 0.71 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.78 | 1.00 | 1.28 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.79 | 0.89 | 1.13 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.89 | 1.07 | 1.19 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.74 | 0.66 | 0.89 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.11 | 0.63 | 0.57 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.46 | 0.65 | 0.45 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.82 | 0.64 | 0.77 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.67 | 0.53 | 0.32 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.15 | 0.17 | 1.13 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.54 | 1.83 | 1.19 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.73 | 0.76 | 1.05 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.69 | 0.69 | 1.01 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.65 | 0.62 | 0.96 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.67 | 0.74 | 1.11 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.68 | 0.74 | 1.08 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.54 | 0.81 | 1.50 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.56 | 0.84 | 1.50 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.63 | 0.88 | 1.39 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.76 | 1.44 | 1.89 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.02 | 1.56 | 1.53 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.98 | 1.63 | 1.66 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.95 | 1.10 | 1.16 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.41 | 1.88 | 1.33 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.12 | 0.59 | 0.53 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.50 | 0.52 | 1.05 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.58 | 0.59 | 1.00 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.88 | 0.89 | 1.01 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.46 | 1.80 | 1.23 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.76 | 0.68 | 0.90 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.03 | 1.01 | 0.98 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.46 | 1.73 | 1.19 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.39 | 0.36 | 0.91 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.16 | 0.64 | 0.55 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.62 | 0.75 | 1.20 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.70 | 0.74 | 1.06 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.66 | 0.71 | 1.09 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.52 | 0.58 | 1.12 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.59 | 0.75 | 1.27 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.97 | 1.20 | 1.24 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.94 | 0.83 | 0.88 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.29 | 1.10 | 0.85 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.53 | 1.51 | 0.99 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.37 | 0.37 | 1.03 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.63 | 0.63 | 1.01 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.64 | 0.63 | 0.98 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.52 | 0.63 | 1.20 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.21 | 1.42 | 1.18 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.59 | 0.51 | 0.86 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.66 | 0.68 | 1.03 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.49 | 1.34 | 0.90 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 2.55 | 2.29 | 0.90 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.94 | 0.96 | 1.02 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.54 | 1.37 | 0.89 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.54 | 1.39 | 0.90 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.16 | 1.59 | 1.38 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.74 | 0.86 | 1.15 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.77 | 0.96 | 1.24 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.72 | 0.80 | 1.10 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.26 | 1.44 | 1.15 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.54 | 0.60 | 1.10 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.53 | 0.63 | 1.18 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.53 | 0.60 | 1.15 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.51 | 0.60 | 1.18 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.61 | 0.70 | 1.14 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.59 | 0.72 | 1.21 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.41 | 0.47 | 1.15 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.58 | 0.61 | 1.06 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.89 | 1.01 | 1.14 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.14 | 1.31 | 1.14 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.26 | 1.81 | 1.44 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.87 | 1.14 | 1.31 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.18 | 1.41 | 1.19 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.29 | 1.77 | 1.38 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.78 | 1.07 | 1.38 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.93 | 1.57 | 1.69 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.95 | 1.62 | 1.71 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.14 | 1.50 | 1.32 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.59 | 2.12 | 1.34 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.33 | 1.71 | 1.29 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.88 | 2.15 | 1.14 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.37 | 0.36 | 0.97 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.38 | 0.39 | 1.01 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.35 | 0.36 | 1.03 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.36 | 0.40 | 1.11 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.56 | 0.51 | 0.91 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.54 | 0.48 | 0.88 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.79 | 2.28 | 1.27 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.67 | 0.89 | 1.33 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.33 | 2.33 | 1.00 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.19 | 1.32 | 1.11 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.96 | 1.50 | 0.76 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.63 | 0.75 | 1.19 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.95 | 1.26 | 1.33 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.23 | 1.52 | 1.23 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.54 | 0.53 | 0.99 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.38 | 0.46 | 1.24 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.47 | 0.56 | 1.21 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.49 | 0.59 | 1.21 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.40 | 0.41 | 1.03 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.45 | 0.45 | 0.98 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.54 | 0.59 | 1.10 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.53 | 0.45 | 0.86 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.45 | 0.46 | 1.03 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.42 | 0.42 | 1.01 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.36 | 0.41 | 1.14 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.51 | 0.53 | 1.04 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.62 | 0.70 | 1.12 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.87 | 0.93 | 1.07 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.54 | 1.75 | 1.13 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 1.74 | 2.07 | 1.19 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.60 | 1.38 | 0.86 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 1.72 | 1.66 | 0.97 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.45 | 1.47 | 1.01 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 1.85 | 2.21 | 1.20 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.01 | 1.20 | 1.18 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.68 | 0.67 | 0.98 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.66 | 0.78 | 1.18 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.55 | 2.98 | 0.84 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.54 | 0.53 | 0.98 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.65 | 0.54 | 0.83 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.62 | 1.17 | 0.72 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.05 | 0.83 | 0.80 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.64 | 1.11 | 1.73 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.94 | 1.54 | 1.64 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.59 | 0.64 | 1.09 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.11 | 1.79 | 1.62 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.01 | 1.92 | 1.90 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.52 | 0.51 | 0.98 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.39 | 0.38 | 0.97 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.43 | 0.40 | 0.94 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.56 | 0.54 | 0.97 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.43 | 0.41 | 0.97 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.63 | 0.52 | 0.82 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.43 | 0.40 | 0.95 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.65 | 0.59 | 0.91 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.48 | 0.41 | 0.85 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.66 | 0.72 | 1.10 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.43 | 0.52 | 1.22 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.37 | 0.40 | 1.08 | yes | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.71 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.74 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.23 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.73 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.68 | - | yes | the trigger narrower than the conjunct |
