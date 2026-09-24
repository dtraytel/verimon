# Performance suite: monpoly vs verimon

The starting point: both systems from a build of master (025a1423), where `-verified` is the original VeriMon, on the same suite and logs as `report.md`.  Run on 2026-09-24 on the same machine as `report.md`, one run after the other, so the two compare.

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 512 s (budget 2400 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 196 | 196 |
| timeout | 0 | 5 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 191 formulas both finish: geometric mean of verimon/monpoly = **2.63**, median 2.76, 0 where verimon is faster, 6 within 10%, 136 where verimon is more than 2x slower, 26 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 2.17 | 1.08 | 16.34 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 2.61 | 2.04 | 3.57 | 0 | 0 | 0 |
| andnot | 8 | 8 | 2.87 | 2.47 | 4.00 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.60 | 1.30 | 2.74 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.46 | 1.14 | 1.86 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.39 | 1.00 | 2.85 | 0 | 0 | 0 |
| once | 16 | 16 | 3.04 | 1.92 | 4.22 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 3.42 | 2.80 | 3.89 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 3.43 | 3.00 | 3.80 | 0 | 0 | 0 |
| since | 13 | 13 | 2.64 | 1.23 | 3.28 | 0 | 0 | 0 |
| eventually | 8 | 8 | 2.86 | 1.97 | 3.48 | 0 | 0 | 0 |
| until | 6 | 6 | 1.80 | 1.58 | 2.47 | 0 | 0 | 0 |
| burst | 9 | 9 | 2.35 | 1.74 | 3.62 | 0 | 0 | 0 |
| nested | 11 | 9 | 4.73 | 2.76 | 7.99 | 0 | 2 | 0 |
| agg | 8 | 8 | 1.94 | 1.76 | 2.78 | 0 | 0 | 0 |
| agg_once | 22 | 21 | 3.43 | 1.96 | 5.31 | 0 | 1 | 0 |
| agg_fut | 5 | 5 | 3.24 | 2.02 | 5.55 | 0 | 0 | 0 |
| let | 4 | 4 | 2.26 | 1.51 | 3.47 | 0 | 0 | 0 |
| wide | 8 | 8 | 3.22 | 1.89 | 4.40 | 0 | 0 | 0 |
| long | 12 | 11 | 2.95 | 2.15 | 3.59 | 0 | 1 | 0 |
| policy | 10 | 9 | 3.87 | 1.90 | 9.01 | 0 | 1 | 0 |
| match | 11 | 11 | 1.88 | 1.09 | 3.30 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.23 | 3.77 | 16.34 |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.28 | 2.48 | 9.01 |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.56 | 4.49 | 7.99 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.50 | 3.57 | 7.17 |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.29 | 2.02 | 7.05 |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.81 | 4.87 | 5.99 |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.80 | 4.57 | 5.68 |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 0.72 | 3.98 | 5.55 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.58 | 3.08 | 5.31 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.58 | 3.05 | 5.24 |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.89 | 4.60 | 5.18 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.33 | 1.60 | 4.80 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 0.95 | 4.56 | 4.78 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 0.66 | 3.12 | 4.74 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 0.66 | 3.11 | 4.72 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.19 | 0.19 | 1.00 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.20 | 0.20 | 1.03 |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.19 | 0.20 | 1.08 |
| join-both | base | `A(x,y) AND B(x,y)` | 0.20 | 0.22 | 1.08 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.19 | 0.21 | 1.09 |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.20 | 0.22 | 1.09 |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.18 | 0.20 | 1.11 |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.22 | 0.25 | 1.13 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.28 | 0.32 | 1.14 |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.22 | 0.26 | 1.17 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.78 s | timeout |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.38 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.88 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 2.07 s | timeout |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.50 s | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.50 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.50 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.81 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.51 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.44 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.20 | 0.22 | 1.08 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.26 | 0.65 | 2.45 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.20 | 0.30 | 1.45 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.27 | 0.69 | 2.55 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.23 | 0.36 | 1.54 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.23 | 3.77 | 16.34 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.20 | 0.46 | 2.30 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.11 | 0.20 | 1.74 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.19 | 0.21 | 1.09 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.06 | 0.13 | 2.06 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.27 | 0.65 | 2.45 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.52 | 1.71 | 3.31 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.31 | 1.10 | 3.57 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.23 | 0.46 | 2.04 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.28 | 0.77 | 2.69 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.25 | 0.74 | 3.00 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.29 | 0.85 | 2.90 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.29 | 0.76 | 2.60 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.21 | 0.57 | 2.76 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.27 | 1.07 | 4.00 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.27 | 0.67 | 2.47 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.27 | 0.75 | 2.81 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.20 | 0.28 | 1.38 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.16 | 0.21 | 1.30 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.18 | 0.24 | 1.31 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.21 | 0.28 | 1.35 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.25 | 0.36 | 1.44 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.27 | 0.74 | 2.74 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.26 | 0.68 | 2.62 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.19 | 0.25 | 1.34 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.32 | 0.40 | 1.25 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.28 | 0.32 | 1.14 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.21 | 0.38 | 1.84 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.28 | 0.39 | 1.37 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.23 | 0.33 | 1.43 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.21 | 0.38 | 1.86 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.15 | 0.24 | 1.56 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.15 | 0.24 | 1.60 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.20 | 0.20 | 1.03 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.19 | 0.20 | 1.08 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.25 | 0.71 | 2.85 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.25 | 0.39 | 1.57 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.19 | 0.19 | 1.00 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.18 | 0.20 | 1.11 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.16 | 0.30 | 1.92 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.20 | 0.42 | 2.10 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.25 | 0.49 | 1.96 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.28 | 0.74 | 2.66 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.32 | 0.99 | 3.08 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.48 | 1.72 | 3.57 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 0.59 | 2.28 | 3.84 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 0.55 | 2.05 | 3.74 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.47 | 1.57 | 3.36 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 0.66 | 2.31 | 3.51 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 0.78 | 2.54 | 3.24 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 0.80 | 2.20 | 2.74 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 0.84 | 2.27 | 2.72 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.43 | 1.81 | 4.22 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.42 | 1.54 | 3.64 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.48 | 1.77 | 3.71 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.40 | 1.37 | 3.39 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.62 | 2.27 | 3.66 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.89 | 3.47 | 3.89 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.49 | 1.37 | 2.80 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.00 | 3.48 | 3.47 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.09 | 0.26 | 3.00 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.85 | 3.23 | 3.80 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.42 | 1.35 | 3.23 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.38 | 1.41 | 3.76 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.37 | 0.92 | 2.48 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.37 | 0.95 | 2.55 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.38 | 0.95 | 2.53 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.32 | 0.83 | 2.62 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.30 | 0.84 | 2.79 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.30 | 0.89 | 2.92 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.39 | 1.27 | 3.25 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.46 | 1.48 | 3.23 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.46 | 1.50 | 3.28 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.49 | 1.57 | 3.16 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 0.75 | 2.44 | 3.24 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.52 | 0.65 | 1.23 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.26 | 0.52 | 2.04 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.31 | 0.71 | 2.30 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.45 | 1.18 | 2.62 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 0.65 | 2.14 | 3.32 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.40 | 1.25 | 3.16 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.51 | 1.69 | 3.33 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 0.65 | 2.27 | 3.48 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.20 | 0.39 | 1.97 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.66 | 2.07 | 3.13 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.35 | 0.58 | 1.66 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.36 | 0.62 | 1.71 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.36 | 0.66 | 1.83 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.29 | 0.46 | 1.58 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.30 | 0.51 | 1.71 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.47 | 1.17 | 2.47 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.49 | 1.49 | 3.03 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 0.61 | 1.88 | 3.08 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 0.67 | 2.09 | 3.11 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.20 | 0.40 | 2.03 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.32 | 0.55 | 1.74 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.32 | 0.57 | 1.80 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.28 | 0.51 | 1.84 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.56 | 2.04 | 3.62 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.31 | 0.55 | 1.77 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.36 | 1.44 | 4.05 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.78 | timeout | - | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.38 | timeout | - | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.50 | 3.57 | 7.17 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.80 | 4.57 | 5.68 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.81 | 4.87 | 5.99 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.56 | 4.49 | 7.99 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.42 | 1.53 | 3.63 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.39 | 1.40 | 3.62 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.37 | 1.02 | 2.76 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 0.66 | 2.72 | 4.14 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.27 | 0.49 | 1.83 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.27 | 0.48 | 1.82 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.27 | 0.48 | 1.82 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.26 | 0.48 | 1.82 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.31 | 0.54 | 1.76 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.31 | 0.55 | 1.77 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.19 | 0.40 | 2.08 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.27 | 0.75 | 2.78 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.52 | 1.86 | 3.60 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 0.66 | 2.84 | 4.33 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 0.66 | 3.12 | 4.74 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.50 | 1.83 | 3.64 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.63 | 2.79 | 4.40 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 0.66 | 3.11 | 4.72 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.46 | 1.89 | 4.08 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.58 | 3.05 | 5.24 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.58 | 3.08 | 5.31 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.65 | 2.66 | 4.10 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.88 | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 0.69 | 2.11 | 3.07 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 0.96 | 2.96 | 3.08 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.16 | 0.36 | 2.23 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.16 | 0.33 | 2.07 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.16 | 0.31 | 1.96 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.16 | 0.31 | 1.96 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.31 | 0.67 | 2.20 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.32 | 0.78 | 2.47 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.89 | 4.60 | 5.18 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.33 | 1.60 | 4.80 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.37 | 3.96 | 2.90 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 0.68 | 1.70 | 2.48 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.08 | 2.18 | 2.02 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.30 | 0.85 | 2.80 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.51 | 2.36 | 4.59 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 0.72 | 3.98 | 5.55 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.28 | 0.99 | 3.47 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.20 | 0.31 | 1.51 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.24 | 0.39 | 1.58 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.25 | 0.79 | 3.12 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.20 | 0.73 | 3.64 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.23 | 0.93 | 4.11 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.26 | 1.12 | 4.40 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.26 | 0.94 | 3.61 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.22 | 0.76 | 3.51 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.19 | 0.41 | 2.12 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.17 | 0.33 | 1.89 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.27 | 0.93 | 3.47 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.33 | 0.93 | 2.80 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.45 | 1.59 | 3.53 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 0.68 | 2.42 | 3.59 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 0.70 | 2.43 | 3.49 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.71 | 2.43 | 3.44 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 0.75 | 2.25 | 3.02 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 0.64 | 1.94 | 3.03 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 0.78 | 2.47 | 3.16 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.39 | 0.95 | 2.42 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.24 | 0.55 | 2.33 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.24 | 0.51 | 2.15 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 2.07 | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.25 | 0.55 | 2.20 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.36 | 0.68 | 1.90 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 0.95 | 4.56 | 4.78 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.55 | 2.39 | 4.36 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.28 | 2.48 | 9.01 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.50 | timeout | - | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.29 | 2.02 | 7.05 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.50 | 1.69 | 3.36 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.49 | 1.73 | 3.54 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.27 | 0.81 | 2.95 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.20 | 0.22 | 1.09 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.22 | 0.25 | 1.13 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.28 | 0.79 | 2.76 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.24 | 0.79 | 3.30 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.32 | 0.95 | 2.93 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.22 | 0.26 | 1.17 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.31 | 0.81 | 2.58 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.25 | 0.53 | 2.17 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.31 | 0.55 | 1.77 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.20 | 0.34 | 1.69 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.17 | 0.26 | 1.58 | NO | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.50 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.50 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.81 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.51 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.44 | - | yes | the trigger narrower than the conjunct |
