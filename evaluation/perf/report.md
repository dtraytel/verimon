# Performance suite: monpoly vs vdense vs dense

185 formulas, 21 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 1070 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 185 | 175 |
| timeout | 0 | 10 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 175 formulas both finish: geometric mean of vdense/monpoly = **1.40**, median 1.29, 20 where vdense is faster, 44 within 10%, 25 where vdense is more than 2x slower, 3 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.95 | 1.59 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.03 | 0.98 | 1.09 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.08 | 0.96 | 1.22 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.13 | 1.05 | 1.23 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.10 | 0.93 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.06 | 0.86 | 1.40 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.76 | 1.60 | 0 | 0 | 0 |
| once_exists | 5 | 3 | 1.72 | 1.37 | 2.18 | 0 | 2 | 0 |
| once_scale | 4 | 4 | 1.23 | 1.16 | 1.30 | 0 | 0 | 0 |
| since | 13 | 13 | 1.68 | 0.64 | 2.94 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.31 | 1.04 | 2.07 | 0 | 0 | 0 |
| until | 6 | 6 | 1.58 | 1.34 | 2.06 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.29 | 0.96 | 1.87 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.19 | 0.98 | 1.71 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.36 | 1.21 | 1.40 | 0 | 0 | 0 |
| agg_once | 22 | 16 | 2.44 | 1.51 | 4.29 | 0 | 6 | 0 |
| agg_fut | 5 | 4 | 2.17 | 1.31 | 3.37 | 0 | 1 | 0 |
| let | 4 | 4 | 1.22 | 1.09 | 1.28 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.31 | 1.03 | 1.51 | 0 | 0 | 0 |
| long | 12 | 11 | 1.33 | 1.00 | 1.61 | 0 | 1 | 0 |
| policy | 10 | 10 | 2.06 | 0.96 | 5.92 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 4.02 | 5.92 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.12 | 4.80 | 4.29 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.11 | 4.69 | 4.23 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.12 | 4.40 | 3.94 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.89 | 3.74 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.03 | 3.48 | 3.37 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.75 | 3.11 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.36 | 4.08 | 3.00 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.33 | 3.95 | 2.97 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.15 | 3.39 | 2.94 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.24 | 3.61 | 2.92 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.08 | 3.12 | 2.89 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.86 | 2.33 | 2.72 |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.39 | 3.74 | 2.70 |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.02 | 2.74 | 2.68 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.83 | 0.64 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.91 | 1.45 | 0.76 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.47 | 0.86 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.41 | 0.92 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.62 | 0.58 | 0.93 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.42 | 0.40 | 0.95 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.44 | 0.42 | 0.95 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.12 | 1.07 | 0.96 |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.57 | 0.55 | 0.96 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.74 | 0.71 | 0.96 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | vdense |
|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.96 s | timeout |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.05 s | timeout |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.52 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.06 s | timeout |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.14 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.97 s | timeout |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.69 s | timeout |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.38 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.95 s | timeout |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 185 | 178 |
| timeout | 0 | 7 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 178 formulas both finish: geometric mean of dense/monpoly = **1.40**, median 1.31, 16 where dense is faster, 41 within 10%, 25 where dense is more than 2x slower, 1 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.97 | 1.61 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.97 | 1.12 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.08 | 0.95 | 1.23 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.14 | 1.05 | 1.22 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.11 | 0.92 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.07 | 0.87 | 1.39 | 0 | 0 | 0 |
| once | 16 | 16 | 1.22 | 0.76 | 1.59 | 0 | 0 | 0 |
| once_exists | 5 | 3 | 1.73 | 1.39 | 2.16 | 0 | 2 | 0 |
| once_scale | 4 | 4 | 1.24 | 1.18 | 1.31 | 0 | 0 | 0 |
| since | 13 | 13 | 1.70 | 0.61 | 3.03 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.32 | 1.04 | 2.10 | 0 | 0 | 0 |
| until | 6 | 6 | 1.59 | 1.35 | 2.06 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.28 | 0.96 | 1.88 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.19 | 0.98 | 1.74 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.35 | 1.22 | 1.40 | 0 | 0 | 0 |
| agg_once | 22 | 18 | 2.22 | 1.57 | 3.99 | 0 | 4 | 0 |
| agg_fut | 5 | 5 | 1.91 | 1.31 | 2.98 | 0 | 0 | 0 |
| let | 4 | 4 | 1.24 | 1.10 | 1.32 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.33 | 1.03 | 1.56 | 0 | 0 | 0 |
| long | 12 | 11 | 1.36 | 1.02 | 1.77 | 0 | 1 | 0 |
| policy | 10 | 10 | 2.04 | 0.96 | 5.14 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 3.50 | 5.14 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.12 | 4.46 | 3.99 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.12 | 4.41 | 3.95 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.11 | 4.31 | 3.88 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.67 | 3.53 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.15 | 3.49 | 3.03 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.03 | 3.08 | 2.98 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.08 | 3.14 | 2.91 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.24 | 3.54 | 2.86 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.86 | 2.37 | 2.77 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.44 | 2.76 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.33 | 3.62 | 2.72 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.78 | 2.05 | 2.63 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.36 | 3.58 | 2.63 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.43 | 3.72 | 2.60 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.79 | 0.61 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.91 | 1.45 | 0.76 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.47 | 0.87 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.62 | 0.57 | 0.92 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.42 | 0.93 |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.57 | 0.55 | 0.95 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.44 | 0.41 | 0.95 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.12 | 1.07 | 0.96 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.74 | 0.71 | 0.96 |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.61 | 0.97 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.96 s | timeout |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.05 s | timeout |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 s | timeout |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.52 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.06 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.97 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.95 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.40 | 0.41 | 0.41 | 1.02 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.56 | 0.58 | 0.58 | 1.05 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.40 | 0.51 | 0.51 | 1.26 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.56 | 0.67 | 0.68 | 1.21 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.50 | 0.52 | 0.52 | 1.03 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.54 | 0.55 | 0.55 | 1.02 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.45 | 0.50 | 0.51 | 1.12 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.26 | 0.41 | 0.41 | 1.59 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.42 | 0.40 | 0.41 | 0.95 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.15 | 0.16 | 0.17 | 1.09 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.56 | 0.58 | 0.59 | 1.03 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.08 | 1.11 | 1.12 | 1.03 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.62 | 0.61 | 0.98 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.51 | 0.54 | 0.54 | 1.05 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.57 | 0.55 | 0.55 | 0.96 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.50 | 0.53 | 0.53 | 1.07 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.58 | 0.66 | 0.66 | 1.14 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.56 | 0.69 | 0.70 | 1.22 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.46 | 0.49 | 0.50 | 1.09 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.57 | 0.69 | 0.70 | 1.22 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.55 | 0.54 | 0.54 | 0.98 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.54 | 0.53 | 0.53 | 0.97 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.44 | 0.50 | 0.51 | 1.14 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.33 | 0.41 | 0.41 | 1.23 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.41 | 0.48 | 0.48 | 1.18 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.45 | 0.51 | 0.51 | 1.13 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.51 | 0.57 | 0.57 | 1.12 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.57 | 0.60 | 0.60 | 1.05 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.55 | 0.59 | 0.59 | 1.07 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.44 | 0.50 | 0.51 | 1.16 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.62 | 0.58 | 0.57 | 0.93 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.59 | 0.57 | 0.57 | 0.96 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.45 | 0.63 | 0.63 | 1.40 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.56 | 0.56 | 0.56 | 1.00 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.41 | 0.51 | 0.51 | 1.22 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.45 | 0.53 | 0.54 | 1.19 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.35 | 0.48 | 0.48 | 1.37 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.35 | 0.49 | 0.48 | 1.40 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.41 | 0.42 | 0.92 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.41 | 0.42 | 0.42 | 1.02 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.53 | 0.56 | 0.56 | 1.06 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.47 | 0.47 | 0.86 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.44 | 0.42 | 0.41 | 0.95 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.40 | 0.42 | 0.42 | 1.06 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.37 | 0.51 | 0.51 | 1.39 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.43 | 0.55 | 0.56 | 1.29 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.50 | 0.60 | 0.60 | 1.19 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.61 | 0.68 | 0.69 | 1.11 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.71 | 0.83 | 0.84 | 1.17 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.09 | 1.43 | 1.45 | 1.32 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.74 | 2.62 | 2.67 | 1.51 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.71 | 2.42 | 2.37 | 1.42 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.94 | 0.97 | 0.97 | 1.03 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.42 | 1.49 | 1.48 | 1.05 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.34 | 2.51 | 2.64 | 1.07 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.55 | 1.53 | 1.58 | 0.99 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.91 | 1.45 | 1.45 | 0.76 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.08 | 1.73 | 1.72 | 1.60 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.04 | 1.55 | 1.58 | 1.49 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 1.06 | 1.38 | 1.41 | 1.31 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.84 | 1.42 | 1.45 | 1.69 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.29 | 2.82 | 2.79 | 2.18 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.96 | timeout | timeout | - | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.99 | 1.35 | 1.37 | 1.37 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.05 | timeout | timeout | - | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.19 | 0.22 | 0.23 | 1.16 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.99 | 2.59 | 2.60 | 1.30 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.92 | 1.14 | 1.14 | 1.25 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.80 | 0.99 | 0.99 | 1.24 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.79 | 0.89 | 0.91 | 1.13 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.80 | 0.97 | 0.97 | 1.21 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.83 | 1.09 | 1.08 | 1.31 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.65 | 1.20 | 1.19 | 1.85 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.67 | 1.27 | 1.23 | 1.88 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.69 | 1.33 | 1.37 | 1.92 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.86 | 2.33 | 2.37 | 2.72 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.08 | 3.12 | 3.14 | 2.89 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.15 | 3.39 | 3.49 | 2.94 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.04 | 1.77 | 1.81 | 1.70 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.60 | 3.41 | 3.77 | 2.13 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.83 | 0.79 | 0.64 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.57 | 0.78 | 0.80 | 1.35 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.66 | 0.70 | 0.70 | 1.07 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 1.03 | 1.19 | 1.21 | 1.15 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.88 | 2.86 | 2.91 | 1.52 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.81 | 0.84 | 0.84 | 1.04 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.14 | 1.29 | 1.29 | 1.13 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.01 | 3.07 | 3.06 | 1.53 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.43 | 0.56 | 0.55 | 1.28 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.37 | 2.85 | 2.89 | 2.07 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.73 | 1.05 | 1.07 | 1.45 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.77 | 1.16 | 1.16 | 1.50 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.79 | 1.64 | 1.63 | 2.06 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.61 | 0.81 | 0.82 | 1.34 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.67 | 0.96 | 0.96 | 1.43 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.06 | 1.95 | 1.94 | 1.83 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.12 | 1.07 | 1.07 | 0.96 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.49 | 1.57 | 1.58 | 1.05 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.98 | 2.28 | 2.23 | 1.15 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.43 | 0.54 | 0.53 | 1.24 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.74 | 1.03 | 1.03 | 1.39 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.74 | 1.25 | 1.26 | 1.69 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.64 | 1.20 | 1.20 | 1.87 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.43 | 2.20 | 2.11 | 1.54 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.66 | 0.66 | 0.67 | 1.00 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.76 | 0.80 | 0.81 | 1.05 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.70 | 1.73 | 1.79 | 1.02 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 3.09 | 3.05 | 3.02 | 0.99 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.21 | 1.27 | 1.27 | 1.05 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.81 | 1.85 | 1.84 | 1.02 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.89 | 1.86 | 1.86 | 0.98 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.28 | 1.83 | 1.85 | 1.43 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.91 | 1.16 | 1.14 | 1.27 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.83 | 1.42 | 1.43 | 1.71 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.81 | 1.10 | 1.10 | 1.37 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.51 | 2.14 | 2.09 | 1.42 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.60 | 0.83 | 0.84 | 1.39 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.62 | 0.85 | 0.85 | 1.38 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.62 | 0.84 | 0.85 | 1.36 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.61 | 0.85 | 0.84 | 1.39 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.72 | 0.99 | 0.98 | 1.38 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.73 | 1.00 | 0.99 | 1.37 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.49 | 0.68 | 0.67 | 1.40 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.60 | 0.73 | 0.74 | 1.21 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.02 | 2.74 | 2.31 | 2.68 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.36 | 4.08 | 3.58 | 3.00 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.57 | timeout | timeout | - | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.00 | 2.64 | 2.30 | 2.65 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.33 | 3.95 | 3.62 | 2.97 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.52 | timeout | timeout | - | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.89 | 2.75 | 2.44 | 3.11 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.11 | 4.69 | 4.31 | 4.23 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.12 | 4.80 | 4.46 | 4.29 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.43 | 3.60 | 3.72 | 2.52 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.06 | timeout | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.52 | 3.72 | 3.10 | 2.45 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.14 | timeout | 4.47 | - | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.37 | 0.60 | 0.63 | 1.63 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.37 | 0.60 | 0.62 | 1.62 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.37 | 0.58 | 0.61 | 1.56 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.38 | 0.57 | 0.60 | 1.51 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.61 | 1.14 | 0.96 | 1.87 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.58 | 1.45 | 0.97 | 2.49 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.97 | timeout | timeout | - | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.78 | 1.92 | 2.05 | 2.47 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.69 | timeout | 4.92 | - | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.46 | 2.70 | 2.58 | 1.85 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.38 | timeout | 3.79 | - | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.71 | 0.93 | 0.94 | 1.31 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.03 | 3.48 | 3.08 | 3.37 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.39 | 3.74 | 3.17 | 2.70 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.58 | 0.63 | 0.64 | 1.09 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.41 | 0.51 | 0.52 | 1.26 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.52 | 0.66 | 0.66 | 1.28 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.54 | 0.69 | 0.71 | 1.28 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.44 | 0.58 | 0.58 | 1.31 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.50 | 0.69 | 0.69 | 1.38 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.60 | 0.89 | 0.93 | 1.49 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.58 | 0.67 | 0.68 | 1.16 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.48 | 0.62 | 0.63 | 1.29 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.43 | 0.60 | 0.62 | 1.39 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.42 | 0.64 | 0.64 | 1.51 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.59 | 0.61 | 0.60 | 1.03 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.72 | 0.83 | 0.82 | 1.16 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.02 | 1.27 | 1.30 | 1.25 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.79 | 2.55 | 2.56 | 1.42 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 2.10 | 2.96 | 2.98 | 1.41 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.77 | 1.77 | 1.80 | 1.00 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 2.18 | 2.70 | 2.63 | 1.24 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.68 | 1.87 | 1.91 | 1.12 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 2.21 | 3.18 | 3.23 | 1.44 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.04 | 1.66 | 1.71 | 1.59 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.77 | 1.24 | 1.37 | 1.61 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.79 | 1.21 | 1.38 | 1.54 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.95 | timeout | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.55 | 0.61 | 0.61 | 1.11 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.74 | 0.71 | 0.71 | 0.96 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.96 | 4.57 | 4.80 | 2.33 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.10 | 1.75 | 1.79 | 1.59 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.68 | 4.02 | 3.50 | 5.92 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.04 | 3.89 | 3.67 | 3.74 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.63 | 0.75 | 0.75 | 1.19 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.24 | 3.61 | 3.54 | 2.92 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.12 | 4.40 | 4.41 | 3.94 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.57 | 0.67 | 0.68 | 1.18 | yes | a Let-bound condition used positively and negatively |
