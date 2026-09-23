# Performance suite: monpoly vs vdense vs dense

201 formulas, 23 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 1155 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 196 | 199 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 194 formulas both finish: geometric mean of vdense/monpoly = **1.35**, median 1.30, 16 where vdense is faster, 37 within 10%, 16 where vdense is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.24 | 0.92 | 2.04 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.08 | 0.94 | 1.17 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.22 | 1.04 | 1.53 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.18 | 0.92 | 1.47 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.09 | 0.93 | 1.29 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.16 | 0.89 | 1.77 | 0 | 0 | 0 |
| once | 16 | 16 | 1.25 | 0.66 | 1.71 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 1.89 | 1.18 | 2.40 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.16 | 1.09 | 1.31 | 0 | 0 | 0 |
| since | 13 | 13 | 1.39 | 0.61 | 2.20 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.34 | 0.92 | 2.28 | 0 | 0 | 0 |
| until | 6 | 6 | 1.50 | 1.36 | 1.94 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.15 | 1.01 | 1.37 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.18 | 0.97 | 1.89 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.31 | 1.16 | 1.52 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.71 | 1.14 | 2.49 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 1.38 | 0.98 | 1.69 | 0 | 0 | 0 |
| let | 4 | 4 | 1.21 | 1.03 | 1.37 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.37 | 1.10 | 1.61 | 0 | 0 | 0 |
| long | 12 | 11 | 1.34 | 1.05 | 1.54 | 0 | 1 | 0 |
| policy | 10 | 9 | 1.60 | 0.98 | 2.74 | 0 | 1 | 0 |
| match | 11 | 11 | 1.62 | 1.30 | 2.06 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.18 | 3.22 | 2.74 |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.69 | 1.79 | 2.60 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.17 | 2.91 | 2.49 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.16 | 2.88 | 2.48 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.87 | 4.48 | 2.40 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.86 | 4.43 | 2.39 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.02 | 2.40 | 2.36 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.49 | 3.52 | 2.36 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.30 | 2.96 | 2.28 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.22 | 2.70 | 2.22 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.96 | 2.11 | 2.20 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.15 | 2.44 | 2.12 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.21 | 2.55 | 2.11 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 | 3.30 | 2.09 |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.70 | 1.44 | 2.06 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.29 | 0.78 | 0.61 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 2.02 | 1.32 | 0.66 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.60 | 0.54 | 0.89 |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.62 | 0.57 | 0.92 |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.84 | 0.78 | 0.92 |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.61 | 0.57 | 0.92 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.69 | 0.65 | 0.93 |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.72 | 0.67 | 0.94 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.60 | 0.57 | 0.94 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.41 | 0.39 | 0.95 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | vdense |
|---|---|---|---|---|
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 4.34 s | timeout |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 2.09 s | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.81 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.81 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.43 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.01 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.84 s |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 196 | 192 |
| timeout | 0 | 9 |
| refused | 0 | 0 |
| unmonitorable | 5 | 0 |
| error | 0 | 0 |

Over the 187 formulas both finish: geometric mean of dense/monpoly = **1.36**, median 1.30, 19 where dense is faster, 42 within 10%, 23 where dense is more than 2x slower, 1 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.20 | 0.96 | 2.03 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.14 | 0.96 | 1.47 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.10 | 0.85 | 1.47 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.24 | 1.01 | 1.57 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.11 | 0.93 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.18 | 0.93 | 1.64 | 0 | 0 | 0 |
| once | 16 | 16 | 1.29 | 0.68 | 1.80 | 0 | 0 | 0 |
| once_exists | 5 | 4 | 1.90 | 1.35 | 2.60 | 0 | 1 | 0 |
| once_scale | 4 | 4 | 1.21 | 1.07 | 1.46 | 0 | 0 | 0 |
| since | 13 | 13 | 1.46 | 0.58 | 2.32 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.34 | 0.95 | 2.10 | 0 | 0 | 0 |
| until | 6 | 6 | 1.50 | 1.28 | 1.82 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.12 | 0.86 | 1.37 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.18 | 0.95 | 1.68 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.32 | 1.16 | 1.45 | 0 | 0 | 0 |
| agg_once | 22 | 16 | 2.06 | 1.35 | 2.87 | 0 | 6 | 0 |
| agg_fut | 5 | 5 | 1.96 | 1.50 | 2.76 | 0 | 0 | 0 |
| let | 4 | 4 | 1.23 | 1.04 | 1.43 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.35 | 1.14 | 1.64 | 0 | 0 | 0 |
| long | 12 | 11 | 1.39 | 1.07 | 1.74 | 0 | 1 | 0 |
| policy | 10 | 9 | 1.86 | 0.94 | 4.98 | 0 | 1 | 0 |
| match | 11 | 11 | 1.09 | 0.83 | 1.40 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.69 | 3.42 | 4.98 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.02 | 3.87 | 3.80 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.82 | 2.36 | 2.87 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.18 | 3.36 | 2.86 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.31 | 3.70 | 2.84 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.09 | 3.01 | 2.76 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.86 | 4.83 | 2.60 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.90 | 2.31 | 2.58 |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.93 | 2.37 | 2.54 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.49 | 3.69 | 2.48 |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.93 | 2.24 | 2.42 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.22 | 2.91 | 2.39 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.96 | 2.22 | 2.32 |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.59 | 3.65 | 2.30 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.22 | 2.74 | 2.25 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.29 | 0.75 | 0.58 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 2.02 | 1.37 | 0.68 |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.70 | 0.58 | 0.83 |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.60 | 0.51 | 0.85 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.21 | 1.04 | 0.86 |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.57 | 0.53 | 0.92 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.60 | 0.56 | 0.93 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.69 | 0.65 | 0.93 |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.66 | 0.62 | 0.94 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.81 | 0.77 | 0.95 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.87 s | timeout |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.49 s | timeout |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.17 s | timeout |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.16 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.05 s | timeout |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.80 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 4.34 s | timeout |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 2.09 s | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.85 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.04 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.62 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.98 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.98 s |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.38 | 0.47 | 0.40 | 1.24 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.52 | 0.58 | 0.58 | 1.10 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.40 | 0.57 | 0.56 | 1.40 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.62 | 0.78 | 0.72 | 1.27 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.57 | 0.64 | 0.61 | 1.11 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.61 | 0.57 | 0.59 | 0.92 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.51 | 0.62 | 0.66 | 1.23 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.23 | 0.48 | 0.47 | 2.04 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.38 | 0.43 | 0.38 | 1.15 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.17 | 0.18 | 0.18 | 1.08 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.72 | 0.67 | 0.69 | 0.94 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.22 | 1.41 | 1.42 | 1.15 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.60 | 0.70 | 0.67 | 1.17 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.49 | 0.51 | 0.72 | 1.06 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.57 | 0.66 | 0.53 | 1.16 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.49 | 0.52 | 0.60 | 1.07 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.61 | 0.69 | 0.62 | 1.13 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.59 | 0.79 | 0.65 | 1.35 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.42 | 0.65 | 0.62 | 1.53 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.65 | 0.91 | 0.73 | 1.40 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.60 | 0.70 | 0.51 | 1.15 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.51 | 0.53 | 0.61 | 1.04 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.42 | 0.50 | 0.50 | 1.21 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.32 | 0.42 | 0.46 | 1.30 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.40 | 0.48 | 0.50 | 1.19 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.50 | 0.57 | 0.60 | 1.14 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.62 | 0.57 | 0.67 | 0.92 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.56 | 0.59 | 0.57 | 1.05 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.52 | 0.66 | 0.69 | 1.27 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.40 | 0.58 | 0.63 | 1.47 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.69 | 0.65 | 0.65 | 0.93 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.60 | 0.57 | 0.60 | 0.94 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.46 | 0.60 | 0.60 | 1.29 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.55 | 0.56 | 0.54 | 1.02 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.38 | 0.45 | 0.53 | 1.21 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.47 | 0.57 | 0.53 | 1.21 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.33 | 0.58 | 0.54 | 1.77 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.40 | 0.59 | 0.59 | 1.46 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.40 | 0.44 | 0.51 | 1.10 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.43 | 0.47 | 0.45 | 1.08 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.62 | 0.65 | 0.73 | 1.04 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.60 | 0.54 | 0.56 | 0.89 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.41 | 0.39 | 0.42 | 0.95 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.37 | 0.44 | 0.37 | 1.19 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.33 | 0.49 | 0.55 | 1.47 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.40 | 0.56 | 0.56 | 1.39 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.52 | 0.61 | 0.63 | 1.18 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.56 | 0.63 | 0.66 | 1.14 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.71 | 0.83 | 0.81 | 1.17 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.01 | 1.37 | 1.55 | 1.36 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.83 | 3.13 | 2.74 | 1.71 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.71 | 2.72 | 2.80 | 1.59 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.93 | 0.99 | 1.02 | 1.06 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.48 | 1.63 | 1.62 | 1.10 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.45 | 2.48 | 2.71 | 1.01 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.50 | 1.58 | 1.64 | 1.05 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 2.02 | 1.32 | 1.37 | 0.66 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.12 | 1.84 | 2.01 | 1.64 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.02 | 1.68 | 1.66 | 1.65 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.95 | 1.23 | 1.41 | 1.29 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.86 | 1.47 | 1.45 | 1.70 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.21 | 2.55 | 2.66 | 2.11 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.86 | 4.43 | 4.83 | 2.39 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.98 | 1.15 | 1.32 | 1.18 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.87 | 4.48 | timeout | 2.40 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.18 | 0.20 | 0.21 | 1.09 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.99 | 2.60 | 2.91 | 1.31 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.94 | 1.05 | 1.01 | 1.11 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.82 | 0.94 | 0.97 | 1.15 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.77 | 0.84 | 0.84 | 1.10 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.94 | 1.02 | 1.00 | 1.08 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.92 | 1.01 | 1.14 | 1.10 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.64 | 0.95 | 0.96 | 1.49 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.65 | 1.04 | 1.04 | 1.61 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.67 | 1.02 | 1.09 | 1.52 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.86 | 1.64 | 1.63 | 1.89 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.96 | 2.11 | 2.22 | 2.20 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.15 | 2.44 | 2.55 | 2.12 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.05 | 1.58 | 1.72 | 1.50 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.59 | 2.26 | 3.65 | 1.42 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.29 | 0.78 | 0.75 | 0.61 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.57 | 0.74 | 0.68 | 1.30 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.64 | 0.72 | 0.70 | 1.13 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.98 | 1.26 | 1.17 | 1.28 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 2.09 | 3.23 | 3.11 | 1.55 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.84 | 0.78 | 0.81 | 0.92 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.19 | 1.40 | 1.45 | 1.17 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.30 | 3.66 | 3.65 | 1.60 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.47 | 0.55 | 0.63 | 1.16 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.30 | 2.96 | 2.73 | 2.28 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.67 | 0.97 | 1.10 | 1.45 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.79 | 1.19 | 1.21 | 1.51 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.85 | 1.17 | 1.09 | 1.37 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.63 | 0.85 | 0.84 | 1.36 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.72 | 1.04 | 1.03 | 1.46 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.15 | 2.24 | 2.10 | 1.94 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.21 | 1.22 | 1.04 | 1.01 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.58 | 1.63 | 1.60 | 1.03 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 2.09 | 2.53 | 2.51 | 1.21 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.41 | 0.51 | 0.48 | 1.25 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.72 | 0.84 | 0.89 | 1.16 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.72 | 0.84 | 0.76 | 1.17 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.62 | 0.75 | 0.85 | 1.21 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.51 | 2.06 | 1.98 | 1.37 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.68 | 0.70 | 0.67 | 1.02 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.78 | 0.77 | 0.79 | 0.99 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.69 | 1.88 | 1.87 | 1.11 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 2.98 | 3.05 | 2.93 | 1.02 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.09 | 1.12 | 1.13 | 1.03 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.94 | 1.90 | 1.97 | 0.98 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 2.01 | 1.95 | 1.90 | 0.97 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.18 | 2.23 | 1.98 | 1.89 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.96 | 1.26 | 1.12 | 1.31 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.84 | 1.13 | 1.31 | 1.34 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.88 | 1.08 | 1.19 | 1.23 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.45 | 2.03 | 2.04 | 1.40 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.59 | 0.81 | 0.79 | 1.38 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.61 | 0.75 | 0.83 | 1.22 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.64 | 0.75 | 0.74 | 1.16 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.58 | 0.79 | 0.83 | 1.37 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.65 | 0.90 | 0.90 | 1.38 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.75 | 0.98 | 0.92 | 1.30 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.45 | 0.69 | 0.66 | 1.52 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.62 | 0.74 | 0.75 | 1.19 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.93 | 1.66 | 2.37 | 1.77 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.31 | 2.30 | 3.70 | 1.76 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 | 3.30 | timeout | 2.09 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.93 | 1.72 | 2.24 | 1.86 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.49 | 2.34 | 3.69 | 1.57 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.49 | 3.52 | timeout | 2.36 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.90 | 1.69 | 2.31 | 1.88 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.17 | 2.91 | timeout | 2.49 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.16 | 2.88 | timeout | 2.48 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.22 | 2.15 | 2.74 | 1.77 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.04 | 3.03 | 4.53 | 1.49 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.47 | 2.49 | 3.03 | 1.69 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.13 | 3.28 | 4.37 | 1.54 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.35 | 0.61 | 0.66 | 1.73 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.37 | 0.54 | 0.65 | 1.45 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.37 | 0.59 | 0.55 | 1.61 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.39 | 0.57 | 0.64 | 1.46 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.65 | 0.80 | 0.91 | 1.24 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.69 | 0.78 | 0.93 | 1.14 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.05 | 3.84 | timeout | 1.88 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.82 | 1.49 | 2.36 | 1.81 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.80 | 3.55 | timeout | 1.27 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.46 | 1.81 | 2.72 | 1.24 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.16 | 2.11 | 3.63 | 0.98 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.69 | 1.03 | 1.03 | 1.49 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.09 | 1.84 | 3.01 | 1.69 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.24 | 2.01 | 2.77 | 1.63 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.59 | 0.60 | 0.66 | 1.03 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.36 | 0.46 | 0.50 | 1.27 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.57 | 0.68 | 0.60 | 1.19 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.51 | 0.70 | 0.73 | 1.37 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.43 | 0.57 | 0.54 | 1.32 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.49 | 0.76 | 0.80 | 1.58 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.59 | 0.95 | 0.87 | 1.60 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.57 | 0.69 | 0.71 | 1.21 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.55 | 0.67 | 0.67 | 1.22 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.46 | 0.66 | 0.62 | 1.44 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.41 | 0.66 | 0.64 | 1.61 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.53 | 0.59 | 0.61 | 1.10 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.69 | 0.78 | 0.78 | 1.14 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.02 | 1.35 | 1.32 | 1.33 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.75 | 2.58 | 2.58 | 1.47 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 2.24 | 3.30 | 3.41 | 1.47 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.67 | 1.76 | 1.80 | 1.05 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 2.30 | 3.13 | 3.07 | 1.36 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.66 | 1.93 | 2.11 | 1.17 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 2.54 | 3.72 | 3.73 | 1.46 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.25 | 1.66 | 1.89 | 1.32 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.78 | 1.17 | 1.37 | 1.50 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.86 | 1.33 | 1.39 | 1.54 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 4.34 | timeout | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.66 | 0.66 | 0.62 | 1.00 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.81 | 0.80 | 0.77 | 0.98 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 2.09 | timeout | timeout | - | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.11 | 1.72 | 2.00 | 1.55 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.69 | 1.79 | 3.42 | 2.60 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.02 | 2.40 | 3.87 | 2.36 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.67 | 0.73 | 0.75 | 1.09 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.22 | 2.70 | 2.91 | 2.22 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.18 | 3.22 | 3.36 | 2.74 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.59 | 0.66 | 0.68 | 1.11 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.42 | 0.54 | 0.42 | 1.31 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.46 | 0.60 | 0.45 | 1.30 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.63 | 1.02 | 0.73 | 1.63 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.52 | 0.94 | 0.53 | 1.82 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.70 | 1.44 | 0.58 | 2.06 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.50 | 0.65 | 0.56 | 1.31 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.67 | 1.28 | 0.74 | 1.90 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.54 | 1.06 | 0.57 | 1.97 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.83 | 1.36 | 0.87 | 1.64 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.47 | 0.88 | 0.66 | 1.87 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.47 | 0.62 | 0.61 | 1.31 | NO | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.81 | 0.85 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.81 | 1.04 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.43 | 1.62 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.01 | 0.98 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.84 | 0.98 | - | yes | the trigger narrower than the conjunct |
