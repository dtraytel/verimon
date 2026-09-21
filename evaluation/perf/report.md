# Performance suite: monpoly vs vdense vs dense

185 formulas, 21 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 1089 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 185 | 177 |
| timeout | 0 | 8 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 177 formulas both finish: geometric mean of vdense/monpoly = **1.39**, median 1.30, 19 where vdense is faster, 45 within 10%, 25 where vdense is more than 2x slower, 1 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 1.00 | 1.60 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.97 | 1.16 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.08 | 0.97 | 1.23 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.13 | 1.04 | 1.23 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.10 | 0.92 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.07 | 0.86 | 1.40 | 0 | 0 | 0 |
| once | 16 | 16 | 1.23 | 0.74 | 1.73 | 0 | 0 | 0 |
| once_exists | 5 | 3 | 1.67 | 1.34 | 2.09 | 0 | 2 | 0 |
| once_scale | 4 | 4 | 1.21 | 1.18 | 1.29 | 0 | 0 | 0 |
| since | 13 | 13 | 1.70 | 0.63 | 2.94 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.31 | 1.04 | 1.97 | 0 | 0 | 0 |
| until | 6 | 6 | 1.59 | 1.32 | 2.09 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.28 | 0.98 | 1.92 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.19 | 0.99 | 1.73 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.34 | 1.21 | 1.37 | 0 | 0 | 0 |
| agg_once | 22 | 18 | 2.26 | 1.51 | 3.83 | 0 | 4 | 0 |
| agg_fut | 5 | 4 | 2.03 | 1.30 | 2.95 | 0 | 1 | 0 |
| let | 4 | 4 | 1.22 | 1.09 | 1.28 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.31 | 1.08 | 1.52 | 0 | 0 | 0 |
| long | 12 | 11 | 1.32 | 1.02 | 1.60 | 0 | 1 | 0 |
| policy | 10 | 10 | 1.98 | 0.93 | 4.90 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 3.33 | 4.90 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.10 | 4.27 | 3.86 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.13 | 4.32 | 3.83 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.14 | 4.15 | 3.63 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.49 | 3.35 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.55 | 4.85 | 3.13 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.04 | 3.06 | 2.95 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.09 | 3.19 | 2.94 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.22 | 3.53 | 2.89 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.26 | 3.64 | 2.89 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.56 | 2.86 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.85 | 2.35 | 2.75 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.35 | 3.57 | 2.65 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.34 | 3.42 | 2.55 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.43 | 3.48 | 2.43 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.82 | 0.63 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.92 | 1.43 | 0.74 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.46 | 0.86 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.63 | 0.58 | 0.92 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.75 | 0.70 | 0.93 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.42 | 0.95 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.43 | 0.42 | 0.96 |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.55 | 0.54 | 0.97 |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.61 | 0.97 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.59 | 0.57 | 0.97 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | vdense |
|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.95 s | timeout |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.04 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.53 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.15 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.96 s | timeout |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.65 s | timeout |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.36 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.87 s | timeout |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 185 | 178 |
| timeout | 0 | 7 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 178 formulas both finish: geometric mean of dense/monpoly = **1.40**, median 1.31, 15 where dense is faster, 41 within 10%, 25 where dense is more than 2x slower, 1 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.14 | 0.99 | 1.60 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.97 | 1.12 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.09 | 0.98 | 1.26 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.14 | 1.05 | 1.24 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.10 | 0.91 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.07 | 0.87 | 1.41 | 0 | 0 | 0 |
| once | 16 | 16 | 1.23 | 0.76 | 1.69 | 0 | 0 | 0 |
| once_exists | 5 | 4 | 1.83 | 1.36 | 2.37 | 0 | 1 | 0 |
| once_scale | 4 | 4 | 1.24 | 1.19 | 1.31 | 0 | 0 | 0 |
| since | 13 | 13 | 1.71 | 0.61 | 2.98 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.31 | 1.04 | 1.97 | 0 | 0 | 0 |
| until | 6 | 6 | 1.58 | 1.33 | 2.08 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.29 | 0.98 | 1.92 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.21 | 1.00 | 1.76 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.35 | 1.23 | 1.42 | 0 | 0 | 0 |
| agg_once | 22 | 17 | 2.21 | 1.51 | 3.98 | 0 | 5 | 0 |
| agg_fut | 5 | 5 | 1.91 | 1.32 | 2.90 | 0 | 0 | 0 |
| let | 4 | 4 | 1.23 | 1.10 | 1.30 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.33 | 1.06 | 1.53 | 0 | 0 | 0 |
| long | 12 | 11 | 1.35 | 1.03 | 1.71 | 0 | 1 | 0 |
| policy | 10 | 10 | 2.00 | 0.96 | 4.92 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 3.35 | 4.92 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.13 | 4.48 | 3.98 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.14 | 4.42 | 3.87 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.10 | 4.25 | 3.85 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.72 | 3.57 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.09 | 3.24 | 2.98 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.22 | 3.62 | 2.97 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.04 | 3.00 | 2.90 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.26 | 3.54 | 2.81 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.85 | 2.39 | 2.79 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.46 | 2.75 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.76 | 2.03 | 2.66 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.43 | 3.78 | 2.64 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.35 | 3.53 | 2.62 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.34 | 3.45 | 2.58 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.79 | 0.61 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.92 | 1.46 | 0.76 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.47 | 0.87 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.63 | 0.57 | 0.91 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.75 | 0.72 | 0.96 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.43 | 0.42 | 0.96 |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.62 | 0.97 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.59 | 0.58 | 0.98 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.13 | 1.10 | 0.98 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.44 | 0.98 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.95 s | timeout |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.55 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.53 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.15 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.96 s | timeout |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.65 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.87 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.41 | 0.41 | 0.42 | 1.01 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.57 | 0.59 | 0.60 | 1.04 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.41 | 0.51 | 0.53 | 1.24 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.57 | 0.69 | 0.70 | 1.22 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.51 | 0.53 | 0.53 | 1.04 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.55 | 0.56 | 0.55 | 1.02 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.46 | 0.51 | 0.51 | 1.12 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.26 | 0.42 | 0.42 | 1.60 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.42 | 0.42 | 0.42 | 1.00 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.15 | 0.18 | 0.17 | 1.16 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.56 | 0.59 | 0.59 | 1.05 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.11 | 1.15 | 1.15 | 1.04 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.61 | 0.62 | 0.97 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.53 | 0.55 | 0.56 | 1.04 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.56 | 0.55 | 0.56 | 0.98 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.51 | 0.54 | 0.54 | 1.07 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.57 | 0.66 | 0.67 | 1.17 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.57 | 0.69 | 0.69 | 1.20 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.46 | 0.50 | 0.51 | 1.09 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.57 | 0.71 | 0.72 | 1.23 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.56 | 0.54 | 0.55 | 0.98 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.55 | 0.54 | 0.55 | 0.97 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.46 | 0.52 | 0.53 | 1.15 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.34 | 0.42 | 0.42 | 1.23 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.42 | 0.50 | 0.51 | 1.19 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.46 | 0.53 | 0.52 | 1.14 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.52 | 0.57 | 0.58 | 1.10 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.58 | 0.61 | 0.62 | 1.05 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.56 | 0.58 | 0.58 | 1.04 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.43 | 0.51 | 0.51 | 1.18 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.63 | 0.58 | 0.57 | 0.92 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.59 | 0.57 | 0.58 | 0.97 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.46 | 0.64 | 0.64 | 1.40 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.57 | 0.56 | 0.57 | 0.99 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.43 | 0.51 | 0.51 | 1.20 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.46 | 0.53 | 0.54 | 1.17 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.35 | 0.49 | 0.49 | 1.40 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.35 | 0.49 | 0.50 | 1.39 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.42 | 0.44 | 0.95 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.42 | 0.43 | 0.43 | 1.03 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.53 | 0.55 | 0.56 | 1.04 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.46 | 0.47 | 0.86 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.43 | 0.42 | 0.42 | 0.96 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.40 | 0.41 | 0.41 | 1.03 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.37 | 0.51 | 0.52 | 1.38 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.44 | 0.57 | 0.57 | 1.29 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.51 | 0.60 | 0.60 | 1.17 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.62 | 0.68 | 0.70 | 1.11 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.74 | 0.84 | 0.85 | 1.14 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.07 | 1.50 | 1.43 | 1.40 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.72 | 2.71 | 2.72 | 1.57 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.68 | 2.39 | 2.32 | 1.42 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.95 | 0.97 | 0.98 | 1.02 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.41 | 1.47 | 1.46 | 1.04 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.32 | 2.55 | 2.58 | 1.10 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.52 | 1.54 | 1.54 | 1.01 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.92 | 1.43 | 1.46 | 0.74 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.06 | 1.83 | 1.79 | 1.73 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.03 | 1.67 | 1.73 | 1.62 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 1.07 | 1.45 | 1.43 | 1.35 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.84 | 1.40 | 1.40 | 1.67 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.31 | 2.74 | 2.71 | 2.09 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.95 | timeout | timeout | - | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.99 | 1.33 | 1.35 | 1.34 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.04 | timeout | 4.82 | - | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.19 | 0.23 | 0.23 | 1.18 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.99 | 2.57 | 2.61 | 1.29 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.94 | 1.14 | 1.15 | 1.21 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.80 | 0.95 | 0.99 | 1.18 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.79 | 0.89 | 0.91 | 1.14 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.80 | 0.97 | 0.98 | 1.22 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.85 | 1.12 | 1.12 | 1.33 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.66 | 1.20 | 1.21 | 1.83 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.67 | 1.26 | 1.26 | 1.89 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.70 | 1.37 | 1.38 | 1.94 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.85 | 2.35 | 2.39 | 2.75 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.09 | 3.19 | 3.24 | 2.94 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.22 | 3.53 | 3.62 | 2.89 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.06 | 1.82 | 1.81 | 1.72 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.55 | 3.43 | 3.82 | 2.21 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.82 | 0.79 | 0.63 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.57 | 0.80 | 0.79 | 1.39 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.67 | 0.69 | 0.69 | 1.04 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 1.05 | 1.21 | 1.22 | 1.16 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.98 | 3.11 | 3.06 | 1.57 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.82 | 0.86 | 0.87 | 1.04 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.14 | 1.32 | 1.31 | 1.16 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.02 | 2.92 | 3.00 | 1.45 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.44 | 0.58 | 0.58 | 1.30 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.38 | 2.71 | 2.72 | 1.97 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.73 | 1.05 | 1.04 | 1.42 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.78 | 1.14 | 1.15 | 1.47 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.80 | 1.67 | 1.66 | 2.09 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.62 | 0.82 | 0.82 | 1.32 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.67 | 0.98 | 0.97 | 1.47 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.07 | 2.04 | 2.00 | 1.92 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.13 | 1.10 | 1.10 | 0.98 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.56 | 1.64 | 1.60 | 1.05 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 2.00 | 2.23 | 2.29 | 1.11 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.45 | 0.54 | 0.55 | 1.20 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.74 | 1.04 | 1.02 | 1.40 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.74 | 1.27 | 1.28 | 1.72 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.63 | 1.22 | 1.22 | 1.92 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.40 | 2.01 | 2.08 | 1.43 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.66 | 0.66 | 0.66 | 0.99 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.76 | 0.80 | 0.81 | 1.05 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.70 | 1.78 | 1.80 | 1.05 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 3.04 | 3.01 | 3.05 | 0.99 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.22 | 1.22 | 1.30 | 1.00 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.79 | 1.87 | 1.88 | 1.05 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.90 | 1.87 | 1.89 | 0.99 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.27 | 1.87 | 1.85 | 1.48 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.90 | 1.17 | 1.15 | 1.29 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.82 | 1.41 | 1.44 | 1.73 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.83 | 1.09 | 1.08 | 1.32 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.46 | 2.08 | 2.10 | 1.43 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.61 | 0.83 | 0.83 | 1.37 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.61 | 0.83 | 0.83 | 1.37 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.61 | 0.83 | 0.84 | 1.36 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.60 | 0.83 | 0.86 | 1.37 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.72 | 0.98 | 0.98 | 1.35 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.76 | 1.01 | 1.03 | 1.32 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.50 | 0.68 | 0.68 | 1.37 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.61 | 0.74 | 0.75 | 1.21 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.03 | 2.41 | 2.26 | 2.34 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.34 | 3.42 | 3.45 | 2.55 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.55 | 4.85 | timeout | 3.13 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.00 | 2.32 | 2.27 | 2.31 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.35 | 3.57 | 3.53 | 2.65 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.53 | timeout | timeout | - | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.56 | 2.46 | 2.86 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.14 | 4.15 | 4.42 | 3.63 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.13 | 4.32 | 4.48 | 3.83 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.43 | 3.48 | 3.78 | 2.43 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.15 | timeout | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.52 | 3.33 | 3.10 | 2.19 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.20 | 4.69 | 4.45 | 2.14 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.38 | 0.60 | 0.64 | 1.58 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.39 | 0.59 | 0.64 | 1.54 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.38 | 0.58 | 0.61 | 1.52 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.39 | 0.59 | 0.62 | 1.51 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.61 | 1.03 | 0.93 | 1.69 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.58 | 1.15 | 0.93 | 1.97 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.96 | timeout | timeout | - | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.76 | 1.80 | 2.03 | 2.36 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.65 | timeout | timeout | - | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.44 | 2.67 | 2.56 | 1.85 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.36 | timeout | 3.84 | - | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.71 | 0.92 | 0.94 | 1.30 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.04 | 3.06 | 3.00 | 2.95 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.37 | 3.27 | 3.19 | 2.38 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.59 | 0.64 | 0.65 | 1.09 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.41 | 0.53 | 0.53 | 1.28 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.53 | 0.65 | 0.65 | 1.24 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.54 | 0.69 | 0.70 | 1.27 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.45 | 0.59 | 0.61 | 1.30 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.51 | 0.68 | 0.70 | 1.33 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.60 | 0.89 | 0.90 | 1.47 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.58 | 0.68 | 0.68 | 1.17 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.49 | 0.63 | 0.64 | 1.30 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.44 | 0.62 | 0.63 | 1.41 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.43 | 0.66 | 0.66 | 1.52 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.58 | 0.62 | 0.61 | 1.08 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.73 | 0.82 | 0.83 | 1.13 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.04 | 1.29 | 1.31 | 1.24 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.81 | 2.52 | 2.55 | 1.39 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 2.06 | 2.79 | 2.94 | 1.35 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.74 | 1.77 | 1.79 | 1.02 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 2.22 | 2.74 | 2.71 | 1.23 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.68 | 1.91 | 1.92 | 1.14 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 2.25 | 3.25 | 3.17 | 1.44 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.10 | 1.71 | 1.74 | 1.56 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.78 | 1.25 | 1.34 | 1.60 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.79 | 1.20 | 1.36 | 1.52 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.87 | timeout | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.56 | 0.61 | 0.62 | 1.08 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.75 | 0.70 | 0.72 | 0.93 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.94 | 4.51 | 4.52 | 2.32 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.11 | 1.73 | 1.76 | 1.55 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 3.33 | 3.35 | 4.90 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.49 | 3.72 | 3.35 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.62 | 0.75 | 0.75 | 1.20 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.26 | 3.64 | 3.54 | 2.89 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.10 | 4.27 | 4.25 | 3.86 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.58 | 0.67 | 0.69 | 1.15 | yes | a Let-bound condition used positively and negatively |
