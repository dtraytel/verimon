# Performance suite: monpoly vs verimon

Both systems from refine (27ea1aaf).  Run on 2026-09-24 on the same machine as `report0.md`, the starting point on master, so the two compare.

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 218 s (budget 2400 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 196 | 201 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 196 formulas both finish: geometric mean of verimon/monpoly = **0.81**, median 0.83, 172 where verimon is faster, 58 within 10%, 0 where verimon is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 0.83 | 0.65 | 0.94 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 0.83 | 0.73 | 0.87 | 0 | 0 | 0 |
| andnot | 8 | 8 | 0.77 | 0.68 | 0.92 | 0 | 0 | 0 |
| rel | 8 | 8 | 0.76 | 0.65 | 0.91 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 0.78 | 0.66 | 0.91 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 0.72 | 0.65 | 0.82 | 0 | 0 | 0 |
| once | 16 | 16 | 0.82 | 0.57 | 1.10 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 0.44 | 0.25 | 0.73 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 0.96 | 0.92 | 1.00 | 0 | 0 | 0 |
| since | 13 | 13 | 0.83 | 0.54 | 1.08 | 0 | 0 | 0 |
| eventually | 8 | 8 | 0.80 | 0.46 | 1.03 | 0 | 0 | 0 |
| until | 6 | 6 | 0.83 | 0.74 | 1.01 | 0 | 0 | 0 |
| burst | 9 | 9 | 0.86 | 0.74 | 1.08 | 0 | 0 | 0 |
| nested | 11 | 11 | 0.86 | 0.77 | 1.05 | 0 | 0 | 0 |
| agg | 8 | 8 | 0.89 | 0.83 | 1.02 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 0.88 | 0.66 | 1.05 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 0.81 | 0.55 | 1.00 | 0 | 0 | 0 |
| let | 4 | 4 | 0.88 | 0.74 | 0.95 | 0 | 0 | 0 |
| wide | 8 | 8 | 0.74 | 0.65 | 0.90 | 0 | 0 | 0 |
| long | 12 | 12 | 0.85 | 0.62 | 1.01 | 0 | 0 | 0 |
| policy | 10 | 10 | 0.88 | 0.65 | 1.25 | 0 | 0 | 0 |
| match | 11 | 11 | 0.79 | 0.68 | 1.08 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.27 | 0.34 | 1.25 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.46 | 0.54 | 1.18 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.47 | 0.52 | 1.10 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 0.57 | 0.62 | 1.10 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.36 | 0.39 | 1.08 |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.31 | 0.33 | 1.08 |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.52 | 0.56 | 1.08 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.44 | 0.46 | 1.05 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.43 | 0.45 | 1.05 |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 0.96 | 1.01 | 1.05 |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.53 | 0.55 | 1.05 |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 0.67 | 0.69 | 1.03 |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 0.66 | 0.68 | 1.03 |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.42 | 0.43 | 1.03 |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.19 | 0.19 | 1.02 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 0.82 | 0.21 | 0.25 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.72 | 0.24 | 0.33 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.54 | 0.25 | 0.46 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.52 | 0.24 | 0.47 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.50 | 0.27 | 0.54 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.03 | 0.56 | 0.55 |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.25 | 0.15 | 0.57 |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.41 | 0.25 | 0.61 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 1.93 | 1.20 | 0.62 |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.20 | 0.13 | 0.63 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.29 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.30 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.52 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.30 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.26 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.21 | 0.17 | 0.81 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.25 | 0.21 | 0.82 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.22 | 0.19 | 0.89 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.25 | 0.22 | 0.89 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.22 | 0.19 | 0.86 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.24 | 0.20 | 0.83 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.19 | 0.15 | 0.77 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.12 | 0.08 | 0.65 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.18 | 0.17 | 0.94 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.06 | 0.05 | 0.87 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.25 | 0.21 | 0.84 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.53 | 0.44 | 0.83 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.29 | 0.21 | 0.73 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.22 | 0.19 | 0.87 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.27 | 0.19 | 0.73 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.23 | 0.16 | 0.68 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.27 | 0.22 | 0.81 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.27 | 0.23 | 0.84 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.20 | 0.15 | 0.73 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.26 | 0.24 | 0.92 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.25 | 0.18 | 0.73 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.25 | 0.19 | 0.74 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.20 | 0.14 | 0.72 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.17 | 0.12 | 0.74 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.18 | 0.13 | 0.74 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.20 | 0.14 | 0.70 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.25 | 0.16 | 0.65 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.24 | 0.21 | 0.88 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.23 | 0.21 | 0.91 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.18 | 0.14 | 0.77 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.32 | 0.21 | 0.66 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.27 | 0.20 | 0.74 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.20 | 0.17 | 0.83 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.25 | 0.19 | 0.77 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.22 | 0.20 | 0.91 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.20 | 0.15 | 0.77 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.15 | 0.10 | 0.65 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.15 | 0.10 | 0.65 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.19 | 0.14 | 0.75 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.17 | 0.14 | 0.81 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.24 | 0.16 | 0.66 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.22 | 0.16 | 0.75 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.18 | 0.14 | 0.74 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.17 | 0.14 | 0.82 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.16 | 0.11 | 0.68 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.20 | 0.13 | 0.63 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.25 | 0.15 | 0.57 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.26 | 0.23 | 0.88 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.30 | 0.28 | 0.95 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.45 | 0.44 | 1.00 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 0.57 | 0.62 | 1.10 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 0.57 | 0.57 | 1.00 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.43 | 0.32 | 0.75 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 0.61 | 0.43 | 0.70 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 0.74 | 0.58 | 0.78 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 0.67 | 0.51 | 0.76 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 0.72 | 0.48 | 0.67 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.42 | 0.43 | 1.03 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.41 | 0.36 | 0.88 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.46 | 0.46 | 1.00 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.35 | 0.26 | 0.73 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.52 | 0.24 | 0.47 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.72 | 0.24 | 0.33 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.41 | 0.25 | 0.61 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 0.82 | 0.21 | 0.25 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.08 | 0.08 | 0.94 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.79 | 0.77 | 0.98 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.39 | 0.36 | 0.92 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.34 | 0.35 | 1.00 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.35 | 0.25 | 0.71 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.36 | 0.26 | 0.72 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.36 | 0.26 | 0.71 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.27 | 0.23 | 0.82 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.28 | 0.23 | 0.84 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.28 | 0.24 | 0.84 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.36 | 0.39 | 1.08 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.43 | 0.45 | 1.05 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.44 | 0.46 | 1.05 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.45 | 0.41 | 0.91 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 0.63 | 0.58 | 0.92 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.50 | 0.27 | 0.54 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.24 | 0.20 | 0.85 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.28 | 0.23 | 0.82 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.41 | 0.39 | 0.96 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 0.62 | 0.64 | 1.02 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.37 | 0.29 | 0.79 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.47 | 0.42 | 0.89 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 0.66 | 0.68 | 1.03 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.20 | 0.13 | 0.64 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.54 | 0.25 | 0.46 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.31 | 0.23 | 0.74 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.33 | 0.25 | 0.76 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.33 | 0.25 | 0.77 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.26 | 0.22 | 0.83 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.28 | 0.24 | 0.87 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.45 | 0.46 | 1.01 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.47 | 0.38 | 0.82 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 0.57 | 0.52 | 0.90 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 0.67 | 0.60 | 0.90 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.19 | 0.15 | 0.83 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.30 | 0.23 | 0.76 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.31 | 0.23 | 0.74 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.27 | 0.26 | 0.95 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.52 | 0.56 | 1.08 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.30 | 0.24 | 0.81 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.32 | 0.29 | 0.91 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.75 | 0.62 | 0.84 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.33 | 1.02 | 0.77 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.49 | 0.42 | 0.87 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.77 | 0.63 | 0.82 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.78 | 0.64 | 0.82 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.53 | 0.55 | 1.05 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.39 | 0.32 | 0.82 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.38 | 0.30 | 0.81 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.35 | 0.30 | 0.84 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 0.62 | 0.63 | 1.02 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.25 | 0.22 | 0.86 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.25 | 0.21 | 0.83 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.26 | 0.22 | 0.84 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.25 | 0.22 | 0.85 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.30 | 0.28 | 0.93 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.31 | 0.28 | 0.92 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.19 | 0.19 | 1.02 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.26 | 0.23 | 0.88 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.49 | 0.42 | 0.85 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 0.62 | 0.53 | 0.85 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 0.64 | 0.62 | 0.97 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.48 | 0.42 | 0.87 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.62 | 0.53 | 0.85 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 0.64 | 0.62 | 0.97 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.44 | 0.45 | 1.02 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.55 | 0.54 | 0.99 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.53 | 0.52 | 0.98 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.62 | 0.62 | 1.01 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.85 | 0.85 | 1.01 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 0.67 | 0.69 | 1.03 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 0.96 | 1.01 | 1.05 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.16 | 0.12 | 0.73 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.16 | 0.12 | 0.78 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.16 | 0.12 | 0.76 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.15 | 0.12 | 0.76 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.29 | 0.19 | 0.66 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.30 | 0.20 | 0.68 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.85 | 0.83 | 0.97 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.33 | 0.33 | 1.02 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.29 | 0.93 | 0.72 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 0.64 | 0.45 | 0.70 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.03 | 0.56 | 0.55 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.29 | 0.28 | 0.98 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.47 | 0.47 | 1.00 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 0.63 | 0.58 | 0.92 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.27 | 0.20 | 0.74 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.19 | 0.17 | 0.90 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.23 | 0.22 | 0.95 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.24 | 0.23 | 0.95 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.19 | 0.14 | 0.71 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.22 | 0.17 | 0.77 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.25 | 0.21 | 0.83 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.25 | 0.17 | 0.67 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.21 | 0.16 | 0.73 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.19 | 0.12 | 0.65 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.18 | 0.13 | 0.69 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.25 | 0.23 | 0.90 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.31 | 0.28 | 0.90 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.43 | 0.42 | 0.97 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 0.63 | 0.64 | 1.01 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 0.66 | 0.66 | 1.00 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.65 | 0.46 | 0.72 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 0.70 | 0.59 | 0.85 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 0.60 | 0.53 | 0.87 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 0.73 | 0.71 | 0.96 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.38 | 0.27 | 0.71 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.23 | 0.20 | 0.87 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.23 | 0.20 | 0.84 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 1.93 | 1.20 | 0.62 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.24 | 0.19 | 0.76 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.33 | 0.26 | 0.79 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 0.83 | 0.54 | 0.65 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.48 | 0.34 | 0.71 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.27 | 0.34 | 1.25 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.43 | 0.35 | 0.82 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.27 | 0.25 | 0.95 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.47 | 0.52 | 1.10 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.46 | 0.54 | 1.18 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.24 | 0.20 | 0.82 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.20 | 0.17 | 0.81 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.21 | 0.18 | 0.84 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.27 | 0.21 | 0.76 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.21 | 0.17 | 0.79 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.30 | 0.20 | 0.68 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.21 | 0.16 | 0.76 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.30 | 0.22 | 0.74 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.24 | 0.17 | 0.69 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.31 | 0.33 | 1.08 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.19 | 0.18 | 0.93 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.16 | 0.11 | 0.70 | yes | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.29 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.30 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.52 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.30 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.26 | - | yes | the trigger narrower than the conjunct |
