# Performance suite: monpoly vs verimon

The starting point: both systems from a build of master (025a1423), where `-verified` is the original VeriMon, on the same suite and logs as `report.md`.  Run on 2026-09-23 on the same container as `report.md`, one run after the other, so the two compare.

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 996 s (budget 2400 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 194 | 122 |
| timeout | 2 | 79 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 117 formulas both finish: geometric mean of verimon/monpoly = **2.68**, median 2.81, 0 where verimon is faster, 2 within 10%, 91 where verimon is more than 2x slower, 19 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 8 | 2.16 | 1.04 | 4.31 | 0 | 1 | 0 |
| join_scale | 5 | 4 | 3.36 | 2.69 | 4.24 | 0 | 1 | 0 |
| andnot | 8 | 8 | 4.17 | 3.21 | 5.91 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.92 | 1.45 | 3.70 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.88 | 1.29 | 2.85 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.58 | 1.03 | 2.87 | 0 | 0 | 0 |
| once | 16 | 5 | 2.90 | 2.42 | 3.52 | 0 | 11 | 0 |
| once_exists | 5 | 1 | 4.18 | 4.18 | 4.18 | 0 | 4 | 0 |
| once_scale | 4 | 1 | 3.57 | 3.57 | 3.57 | 0 | 3 | 0 |
| since | 13 | 8 | 2.82 | 1.30 | 3.83 | 0 | 5 | 0 |
| eventually | 8 | 4 | 3.17 | 2.68 | 4.46 | 0 | 4 | 0 |
| until | 6 | 6 | 2.36 | 1.91 | 3.04 | 0 | 0 | 0 |
| burst | 9 | 5 | 2.24 | 2.08 | 2.48 | 0 | 4 | 0 |
| nested | 11 | 1 | 3.53 | 3.53 | 3.53 | 1 | 10 | 0 |
| agg | 8 | 8 | 2.56 | 2.15 | 3.89 | 0 | 0 | 0 |
| agg_once | 22 | 6 | 2.98 | 2.53 | 3.26 | 0 | 16 | 0 |
| agg_fut | 5 | 1 | 3.91 | 3.91 | 3.91 | 0 | 4 | 0 |
| let | 4 | 4 | 2.97 | 1.83 | 4.99 | 0 | 0 | 0 |
| wide | 8 | 7 | 4.45 | 2.45 | 6.75 | 0 | 1 | 0 |
| long | 12 | 4 | 3.26 | 3.05 | 3.66 | 1 | 8 | 0 |
| policy | 10 | 3 | 2.90 | 2.19 | 3.64 | 0 | 7 | 0 |
| match | 11 | 11 | 2.65 | 1.26 | 5.49 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.58 | 3.95 | 6.75 |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.46 | 2.86 | 6.22 |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.66 | 3.91 | 5.91 |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.67 | 3.69 | 5.49 |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.72 | 3.76 | 5.24 |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.71 | 3.54 | 4.99 |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.71 | 3.52 | 4.93 |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.87 | 4.23 | 4.85 |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.60 | 2.76 | 4.60 |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.98 | 4.37 | 4.46 |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.57 | 2.47 | 4.34 |
| join-first | base | `A(x,y) AND B(z,x)` | 0.62 | 2.66 | 4.31 |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.66 | 2.85 | 4.31 |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.62 | 2.65 | 4.27 |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.95 | 4.05 | 4.24 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.59 | 0.61 | 1.03 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.82 | 0.85 | 1.04 |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.55 | 0.65 | 1.19 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.57 | 0.70 | 1.22 |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.61 | 0.77 | 1.26 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.68 | 0.88 | 1.29 |
| join-both | base | `A(x,y) AND B(x,y)` | 0.49 | 0.63 | 1.30 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.93 | 2.51 | 1.30 |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.53 | 0.70 | 1.32 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.74 | 1.06 | 1.44 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.65 s | timeout |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.59 s | timeout |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.46 s | timeout |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 2.33 s | timeout |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 2.31 s | timeout |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 1.25 s | timeout |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 2.11 s | timeout |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 3.41 s | timeout |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 2.68 s | timeout |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 3.23 s | timeout |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.48 s | timeout |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.40 s | timeout |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 1.42 s | timeout |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.91 s | timeout |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 3.06 s | timeout |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 1.42 s | timeout |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 3.75 s | timeout |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 2.71 s | timeout |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.22 s | timeout |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.21 s | timeout |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.84 s | timeout |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.38 s | timeout |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.67 s | timeout |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.42 s | timeout |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 2.54 s | timeout |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 2.77 s | timeout |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.47 s | timeout |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.72 s | timeout |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.97 s | timeout |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.34 s | timeout |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 2.12 s | timeout |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 2.65 s | timeout |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 2.18 s | timeout |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.95 s | timeout |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 2.43 s | timeout |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | timeout | timeout |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.53 s | timeout |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 2.50 s | timeout |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 2.69 s | timeout |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.86 s | timeout |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 1.21 s | timeout |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 1.06 s | timeout |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 2.32 s | timeout |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.34 s | timeout |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 2.02 s | timeout |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 2.30 s | timeout |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.36 s | timeout |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.85 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 2.10 s | timeout |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 1.21 s | timeout |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.78 s | timeout |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.77 s | timeout |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.87 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.88 s | timeout |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 2.09 s | timeout |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.91 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.65 s | timeout |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.90 s | timeout |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 3.63 s | timeout |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.96 s | timeout |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 3.16 s | timeout |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.56 s | timeout |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.94 s | timeout |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.90 s | timeout |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.29 s | timeout |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 2.39 s | timeout |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 3.21 s | timeout |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 2.27 s | timeout |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 3.40 s | timeout |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 2.14 s | timeout |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 3.43 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | timeout | timeout |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 3.18 s | timeout |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.57 s | timeout |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.82 s | timeout |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.66 s | timeout |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.90 s | timeout |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 2.03 s | timeout |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 2.09 s | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 1.51 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.66 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 2.37 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.58 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 1.61 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.49 | 0.63 | 1.30 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.66 | 2.30 | 3.50 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.62 | 1.16 | 1.87 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.62 | 2.66 | 4.31 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.70 | 1.20 | 1.72 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.65 | timeout | - | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.51 | 1.67 | 3.28 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.30 | 0.66 | 2.22 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.82 | 0.85 | 1.04 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.15 | 0.46 | 3.01 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.65 | 2.40 | 3.71 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.59 | timeout | - | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.95 | 4.05 | 4.24 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.61 | 1.64 | 2.69 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.65 | 2.63 | 4.05 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.57 | 2.47 | 4.34 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.66 | 2.79 | 4.21 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.68 | 2.52 | 3.72 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.51 | 2.07 | 4.06 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.66 | 3.91 | 5.91 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.69 | 2.20 | 3.21 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.62 | 2.65 | 4.27 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.53 | 0.84 | 1.58 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.40 | 0.63 | 1.60 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.46 | 0.69 | 1.48 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.52 | 0.75 | 1.45 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.55 | 0.96 | 1.74 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.68 | 2.43 | 3.56 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.67 | 2.47 | 3.70 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.50 | 0.74 | 1.48 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.74 | 1.06 | 1.44 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.68 | 0.88 | 1.29 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.50 | 1.14 | 2.29 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.69 | 1.26 | 1.82 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.72 | 1.45 | 2.01 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.48 | 1.36 | 2.85 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.40 | 0.73 | 1.83 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.38 | 0.72 | 1.88 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.57 | 0.70 | 1.22 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.53 | 0.70 | 1.32 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.84 | 2.40 | 2.87 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.65 | 1.31 | 2.01 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.59 | 0.61 | 1.03 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.55 | 0.65 | 1.19 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.38 | 0.93 | 2.42 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.47 | 1.26 | 2.68 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.54 | 1.59 | 2.96 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.82 | 2.46 | 3.00 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.98 | 3.44 | 3.52 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.46 | timeout | - | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 2.33 | timeout | - | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 2.31 | timeout | - | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 1.25 | timeout | - | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 2.11 | timeout | - | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 3.41 | timeout | - | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 2.68 | timeout | - | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 3.23 | timeout | - | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.48 | timeout | - | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.40 | timeout | - | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 1.42 | timeout | - | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 1.13 | 4.71 | 4.18 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.91 | timeout | - | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 3.06 | timeout | - | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 1.42 | timeout | - | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 3.75 | timeout | - | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.24 | 0.87 | 3.57 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 2.71 | timeout | - | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.22 | timeout | - | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.21 | timeout | - | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 1.03 | 3.16 | 3.08 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 1.09 | 3.29 | 3.02 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 1.04 | 3.74 | 3.61 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.81 | 3.10 | 3.83 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.98 | 2.88 | 2.94 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.84 | timeout | - | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 1.14 | 4.27 | 3.74 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.38 | timeout | - | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.67 | timeout | - | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.42 | timeout | - | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 2.54 | timeout | - | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.93 | 2.51 | 1.30 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.83 | 1.82 | 2.20 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.83 | 2.28 | 2.73 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 1.36 | 4.17 | 3.08 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 2.77 | timeout | - | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.98 | 4.37 | 4.46 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.47 | timeout | - | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.72 | timeout | - | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.46 | 1.23 | 2.68 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.97 | timeout | - | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.85 | 1.96 | 2.32 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.95 | 2.24 | 2.36 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.98 | 2.45 | 2.51 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.85 | 1.63 | 1.91 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.82 | 1.80 | 2.19 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.34 | 4.06 | 3.04 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.34 | timeout | - | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 2.12 | timeout | - | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 2.65 | timeout | - | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.62 | 1.53 | 2.48 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.89 | 2.00 | 2.25 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 1.02 | 2.17 | 2.11 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.82 | 1.89 | 2.31 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 2.18 | timeout | - | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.91 | 1.88 | 2.08 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.95 | timeout | - | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 2.43 | timeout | - | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | timeout | timeout | - | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.53 | timeout | - | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 2.50 | timeout | - | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 2.69 | timeout | - | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.86 | timeout | - | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 1.21 | timeout | - | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 1.06 | timeout | - | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 1.02 | 3.61 | 3.53 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 2.32 | timeout | - | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.83 | 1.87 | 2.26 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.70 | 1.76 | 2.51 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.70 | 1.85 | 2.65 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.73 | 1.80 | 2.45 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.85 | 1.84 | 2.15 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.83 | 1.91 | 2.30 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.48 | 1.24 | 2.62 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.72 | 2.78 | 3.89 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.34 | timeout | - | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 2.02 | timeout | - | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 2.30 | timeout | - | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.36 | timeout | - | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.85 | timeout | - | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 2.10 | timeout | - | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 1.21 | timeout | - | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.78 | timeout | - | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.77 | timeout | - | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.87 | timeout | - | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.88 | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 2.09 | timeout | - | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.91 | timeout | - | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.37 | 1.17 | 3.15 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.39 | 1.10 | 2.81 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.46 | 1.17 | 2.53 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.38 | 1.19 | 3.15 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.77 | 2.35 | 3.06 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.80 | 2.61 | 3.26 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.65 | timeout | - | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.90 | timeout | - | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 3.63 | timeout | - | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.96 | timeout | - | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 3.16 | timeout | - | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.81 | 3.18 | 3.91 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.56 | timeout | - | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.94 | timeout | - | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.71 | 3.54 | 4.99 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.56 | 1.02 | 1.83 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.68 | 1.34 | 1.99 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.66 | 2.85 | 4.31 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.46 | 2.86 | 6.22 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.58 | 3.95 | 6.75 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.90 | timeout | - | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.71 | 3.52 | 4.93 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.60 | 2.76 | 4.60 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.47 | 1.31 | 2.82 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.43 | 1.06 | 2.45 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.72 | 3.76 | 5.24 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.94 | 3.04 | 3.22 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.29 | timeout | - | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 2.39 | timeout | - | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 3.21 | timeout | - | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 2.27 | timeout | - | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 3.40 | timeout | - | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 2.14 | timeout | - | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 3.43 | timeout | - | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.11 | 3.48 | 3.13 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.56 | 2.03 | 3.66 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.73 | 2.24 | 3.05 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | timeout | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.64 | 1.93 | 3.04 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.95 | 2.09 | 2.19 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 3.18 | timeout | - | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.57 | timeout | - | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.82 | timeout | - | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.66 | timeout | - | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.90 | timeout | - | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 2.03 | timeout | - | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 2.09 | timeout | - | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.81 | 2.94 | 3.64 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.61 | 0.77 | 1.26 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.59 | 0.88 | 1.49 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.68 | 2.67 | 3.90 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.67 | 3.69 | 5.49 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.87 | 4.23 | 4.85 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.59 | 0.91 | 1.56 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.83 | 2.75 | 3.33 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.62 | 2.14 | 3.45 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.87 | 2.26 | 2.61 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.51 | 1.16 | 2.29 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.39 | 0.83 | 2.13 | NO | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 1.51 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.66 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 2.37 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.58 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 1.61 | - | yes | the trigger narrower than the conjunct |
