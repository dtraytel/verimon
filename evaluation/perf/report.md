# Performance suite: monpoly vs vdense vs dense

185 formulas, 21 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 847 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 185 | 183 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 183 formulas both finish: geometric mean of vdense/monpoly = **1.34**, median 1.26, 28 where vdense is faster, 41 within 10%, 23 where vdense is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.08 | 0.86 | 1.32 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.08 | 0.97 | 1.29 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.09 | 0.94 | 1.31 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.14 | 0.95 | 1.31 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.02 | 0.90 | 1.35 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.02 | 0.82 | 1.46 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.66 | 1.68 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 2.06 | 1.28 | 3.06 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.15 | 0.99 | 1.42 | 0 | 0 | 0 |
| since | 13 | 13 | 1.48 | 0.63 | 2.50 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.35 | 1.05 | 2.15 | 0 | 0 | 0 |
| until | 6 | 6 | 1.39 | 1.23 | 1.73 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.13 | 0.85 | 1.49 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.17 | 0.95 | 1.58 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.27 | 1.06 | 1.43 | 0 | 0 | 0 |
| agg_once | 22 | 21 | 2.00 | 1.32 | 3.25 | 0 | 1 | 0 |
| agg_fut | 5 | 4 | 1.77 | 1.41 | 2.19 | 0 | 1 | 0 |
| let | 4 | 4 | 1.14 | 0.98 | 1.37 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.34 | 1.08 | 1.59 | 0 | 0 | 0 |
| long | 12 | 12 | 1.31 | 1.01 | 1.65 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.74 | 0.88 | 3.84 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 1.98 | 3.84 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.77 | 2.49 | 3.25 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.81 | 2.60 | 3.23 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.48 | 4.51 | 3.06 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.13 | 3.26 | 2.89 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.19 | 3.23 | 2.72 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.49 | 1.27 | 2.61 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.98 | 2.55 | 2.61 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.76 | 1.90 | 2.50 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.88 | 2.19 | 2.48 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.56 | 3.76 | 2.40 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.88 | 2.12 | 2.40 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.94 | 2.23 | 2.37 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.90 | 2.11 | 2.35 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.60 | 3.75 | 2.35 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.63 | 0.63 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.44 | 0.95 | 0.66 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.36 | 0.29 | 0.82 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.40 | 0.33 | 0.82 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.84 | 0.71 | 0.85 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.35 | 0.30 | 0.86 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.36 | 0.31 | 0.86 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.52 | 0.46 | 0.88 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.04 | 0.92 | 0.89 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.48 | 0.43 | 0.90 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | vdense |
|---|---|---|---|---|
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.35 s | timeout |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.61 s | timeout |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 185 | 183 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 183 formulas both finish: geometric mean of dense/monpoly = **1.39**, median 1.29, 23 where dense is faster, 36 within 10%, 27 where dense is more than 2x slower, 3 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.07 | 0.89 | 1.31 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.08 | 0.93 | 1.28 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.13 | 0.97 | 1.22 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.15 | 1.00 | 1.31 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.06 | 0.92 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.06 | 0.81 | 1.46 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.65 | 1.73 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 1.95 | 1.29 | 2.77 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.20 | 1.01 | 1.50 | 0 | 0 | 0 |
| since | 13 | 13 | 1.49 | 0.56 | 2.53 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.40 | 1.05 | 2.24 | 0 | 0 | 0 |
| until | 6 | 6 | 1.40 | 1.27 | 1.65 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.12 | 0.91 | 1.49 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.16 | 0.81 | 1.54 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.30 | 1.09 | 1.56 | 0 | 0 | 0 |
| agg_once | 22 | 20 | 2.42 | 1.38 | 4.84 | 0 | 2 | 0 |
| agg_fut | 5 | 5 | 1.92 | 1.43 | 2.87 | 0 | 0 | 0 |
| let | 4 | 4 | 1.19 | 1.11 | 1.36 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.32 | 1.03 | 1.59 | 0 | 0 | 0 |
| long | 12 | 12 | 1.42 | 1.14 | 1.90 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.88 | 1.05 | 5.12 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 2.63 | 5.12 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.77 | 3.71 | 4.84 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.81 | 3.45 | 4.29 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.13 | 4.21 | 3.74 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.19 | 4.22 | 3.56 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.88 | 2.93 | 3.32 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.97 | 2.94 | 3.01 |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.98 | 2.89 | 2.95 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.49 | 1.41 | 2.88 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.82 | 2.37 | 2.87 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.48 | 4.08 | 2.77 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.03 | 2.85 | 2.76 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.71 | 1.81 | 2.55 |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.04 | 2.64 | 2.53 |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.40 | 3.43 | 2.45 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.56 | 0.56 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.44 | 0.93 | 0.65 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.36 | 0.29 | 0.81 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.82 | 0.67 | 0.81 |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.60 | 0.52 | 0.87 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.36 | 0.31 | 0.88 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.35 | 0.31 | 0.89 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.40 | 0.36 | 0.90 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.84 | 0.76 | 0.91 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.47 | 0.43 | 0.92 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.35 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.56 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.26 | 0.28 | 0.29 | 1.07 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.37 | 0.43 | 0.39 | 1.16 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.33 | 0.40 | 0.33 | 1.20 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.43 | 0.49 | 0.55 | 1.15 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.39 | 0.38 | 0.36 | 0.98 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.42 | 0.40 | 0.42 | 0.94 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.36 | 0.40 | 0.41 | 1.14 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.21 | 0.28 | 0.27 | 1.32 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.35 | 0.30 | 0.31 | 0.86 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.12 | 0.11 | 0.11 | 0.97 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.37 | 0.48 | 0.47 | 1.29 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.81 | 0.85 | 0.84 | 1.04 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.42 | 0.42 | 0.47 | 0.99 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.38 | 0.42 | 0.40 | 1.10 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.37 | 0.41 | 0.36 | 1.11 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.34 | 0.35 | 0.40 | 1.04 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.39 | 0.43 | 0.47 | 1.10 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.41 | 0.47 | 0.50 | 1.15 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.31 | 0.36 | 0.37 | 1.17 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.43 | 0.56 | 0.48 | 1.31 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.38 | 0.36 | 0.42 | 0.94 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.39 | 0.38 | 0.40 | 0.97 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.30 | 0.39 | 0.37 | 1.29 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.22 | 0.28 | 0.27 | 1.31 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.34 | 0.36 | 0.38 | 1.06 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.34 | 0.39 | 0.39 | 1.13 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.39 | 0.46 | 0.45 | 1.19 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.44 | 0.42 | 0.47 | 0.95 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.44 | 0.45 | 0.45 | 1.00 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.30 | 0.39 | 0.39 | 1.29 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.48 | 0.43 | 0.46 | 0.90 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.47 | 0.42 | 0.43 | 0.91 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.36 | 0.49 | 0.51 | 1.35 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.38 | 0.38 | 0.37 | 1.00 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.33 | 0.37 | 0.40 | 1.12 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.37 | 0.35 | 0.36 | 0.93 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.26 | 0.38 | 0.38 | 1.46 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.29 | 0.33 | 0.38 | 1.15 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.36 | 0.31 | 0.29 | 0.86 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.28 | 0.32 | 0.32 | 1.15 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.42 | 0.44 | 0.43 | 1.06 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.40 | 0.33 | 0.36 | 0.82 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.36 | 0.29 | 0.31 | 0.82 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.26 | 0.26 | 0.29 | 1.00 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.29 | 0.37 | 0.41 | 1.30 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.34 | 0.44 | 0.43 | 1.30 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.40 | 0.46 | 0.41 | 1.14 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.41 | 0.44 | 0.47 | 1.09 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.50 | 0.63 | 0.55 | 1.26 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.74 | 1.13 | 1.12 | 1.53 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.25 | 2.09 | 2.05 | 1.67 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.40 | 1.95 | 1.93 | 1.39 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.70 | 0.72 | 0.75 | 1.03 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.10 | 1.09 | 1.06 | 0.99 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 1.71 | 1.95 | 2.11 | 1.14 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.04 | 0.92 | 0.98 | 0.89 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.44 | 0.95 | 0.93 | 0.66 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.83 | 1.39 | 1.42 | 1.68 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.79 | 1.25 | 1.31 | 1.59 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.90 | 1.13 | 1.09 | 1.26 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.63 | 1.08 | 0.94 | 1.72 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.90 | 2.11 | 1.98 | 2.35 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.48 | 4.51 | 4.08 | 3.06 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.64 | 0.83 | 0.83 | 1.28 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.60 | 3.75 | 3.80 | 2.35 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.15 | 0.15 | 0.15 | 0.99 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.35 | 1.91 | 2.02 | 1.42 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.73 | 0.80 | 0.79 | 1.10 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.57 | 0.64 | 0.73 | 1.13 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.62 | 0.63 | 0.59 | 1.01 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.64 | 0.63 | 0.69 | 0.99 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.54 | 0.82 | 0.85 | 1.52 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.48 | 0.74 | 0.72 | 1.55 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.51 | 0.76 | 0.73 | 1.49 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.47 | 0.94 | 0.84 | 2.00 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.66 | 1.20 | 1.29 | 1.81 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.76 | 1.90 | 1.76 | 2.50 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.88 | 2.12 | 1.89 | 2.40 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.70 | 1.16 | 1.20 | 1.66 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.04 | 1.62 | 2.64 | 1.55 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.63 | 0.56 | 0.63 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.39 | 0.52 | 0.47 | 1.34 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.42 | 0.52 | 0.53 | 1.24 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.85 | 0.93 | 0.96 | 1.10 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.45 | 2.28 | 2.40 | 1.58 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.55 | 0.58 | 0.58 | 1.05 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.77 | 0.91 | 1.00 | 1.18 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.53 | 2.39 | 2.37 | 1.56 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.33 | 0.40 | 0.44 | 1.22 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.98 | 2.12 | 2.20 | 2.15 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.47 | 0.73 | 0.70 | 1.55 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.62 | 0.77 | 0.80 | 1.23 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.60 | 0.76 | 0.76 | 1.26 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.46 | 0.60 | 0.59 | 1.31 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.45 | 0.60 | 0.66 | 1.34 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.80 | 1.37 | 1.32 | 1.73 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.84 | 0.71 | 0.76 | 0.85 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.18 | 1.28 | 1.10 | 1.08 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.61 | 1.96 | 1.95 | 1.22 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.32 | 0.37 | 0.38 | 1.17 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.55 | 0.64 | 0.64 | 1.15 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.54 | 0.63 | 0.58 | 1.16 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.47 | 0.56 | 0.62 | 1.19 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.11 | 1.65 | 1.65 | 1.49 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.45 | 0.43 | 0.44 | 0.96 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.60 | 0.57 | 0.52 | 0.96 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.07 | 1.10 | 1.21 | 1.04 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.85 | 2.14 | 2.18 | 1.16 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.82 | 0.78 | 0.67 | 0.95 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.24 | 1.29 | 1.37 | 1.04 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.35 | 1.30 | 1.28 | 0.96 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.00 | 1.58 | 1.40 | 1.58 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.61 | 0.88 | 0.88 | 1.43 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.61 | 0.92 | 0.93 | 1.52 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.59 | 0.68 | 0.77 | 1.16 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.23 | 1.60 | 1.57 | 1.30 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.46 | 0.55 | 0.61 | 1.20 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.43 | 0.62 | 0.62 | 1.43 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.42 | 0.58 | 0.53 | 1.37 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.39 | 0.56 | 0.60 | 1.41 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.48 | 0.68 | 0.75 | 1.40 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.57 | 0.61 | 0.62 | 1.06 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.38 | 0.44 | 0.44 | 1.16 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.45 | 0.54 | 0.54 | 1.19 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.75 | 1.29 | 1.69 | 1.72 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.03 | 2.07 | 2.85 | 2.00 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.13 | 3.26 | 4.21 | 2.89 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.79 | 1.32 | 1.74 | 1.68 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.97 | 2.17 | 2.94 | 2.23 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.19 | 3.23 | 4.22 | 2.72 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.71 | 1.48 | 1.81 | 2.09 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.77 | 2.49 | 3.71 | 3.25 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.81 | 2.60 | 3.45 | 3.23 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.98 | 2.55 | 2.89 | 2.61 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.35 | timeout | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.12 | 1.88 | 2.07 | 1.68 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.40 | 2.83 | 3.43 | 2.02 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.29 | 0.45 | 0.51 | 1.52 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.30 | 0.48 | 0.50 | 1.60 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.27 | 0.44 | 0.47 | 1.62 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.29 | 0.45 | 0.41 | 1.53 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.39 | 0.58 | 0.71 | 1.48 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.44 | 0.58 | 0.75 | 1.32 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.56 | 3.45 | timeout | 2.21 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.49 | 1.27 | 1.41 | 2.61 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.87 | 3.00 | 3.91 | 1.60 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.12 | 2.07 | 1.83 | 1.85 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.61 | timeout | 2.85 | - | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.46 | 0.65 | 0.66 | 1.41 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.82 | 1.81 | 2.37 | 2.19 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.10 | 1.89 | 2.45 | 1.71 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.46 | 0.46 | 0.52 | 0.98 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.29 | 0.40 | 0.40 | 1.37 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.41 | 0.48 | 0.48 | 1.19 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.42 | 0.44 | 0.47 | 1.06 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.30 | 0.48 | 0.45 | 1.59 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.41 | 0.49 | 0.53 | 1.21 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.48 | 0.68 | 0.64 | 1.42 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.42 | 0.50 | 0.53 | 1.18 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.39 | 0.51 | 0.45 | 1.30 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.32 | 0.48 | 0.50 | 1.52 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.33 | 0.50 | 0.50 | 1.52 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.41 | 0.44 | 0.42 | 1.08 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.47 | 0.55 | 0.61 | 1.16 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.72 | 0.98 | 0.92 | 1.36 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.37 | 2.03 | 2.19 | 1.48 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 1.62 | 2.47 | 2.44 | 1.52 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.25 | 1.33 | 1.43 | 1.06 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 1.74 | 2.13 | 2.25 | 1.23 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.34 | 1.35 | 1.53 | 1.01 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 1.76 | 2.26 | 2.62 | 1.28 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.86 | 1.20 | 1.19 | 1.39 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.58 | 0.96 | 0.95 | 1.65 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.53 | 0.82 | 1.00 | 1.56 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.12 | 3.66 | 4.84 | 1.17 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.44 | 0.47 | 0.47 | 1.08 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.52 | 0.46 | 0.56 | 0.88 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.56 | 3.76 | 3.80 | 2.40 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.75 | 1.23 | 1.31 | 1.64 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 1.98 | 2.63 | 3.84 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.88 | 2.19 | 2.93 | 2.48 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.48 | 0.55 | 0.58 | 1.14 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.92 | 2.14 | 2.17 | 2.33 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.94 | 2.23 | 2.09 | 2.37 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.42 | 0.48 | 0.44 | 1.15 | yes | a Let-bound condition used positively and negatively |
