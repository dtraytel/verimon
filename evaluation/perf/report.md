# Performance suite: monpoly vs vdense vs dense

185 formulas, 21 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 869 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 185 | 185 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 185 formulas both finish: geometric mean of vdense/monpoly = **1.35**, median 1.26, 20 where vdense is faster, 45 within 10%, 22 where vdense is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.96 | 1.58 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.97 | 1.10 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.09 | 0.98 | 1.23 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.15 | 1.06 | 1.21 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.11 | 0.96 | 1.40 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.06 | 0.84 | 1.42 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.70 | 1.74 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 2.04 | 1.34 | 2.94 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.23 | 1.17 | 1.34 | 0 | 0 | 0 |
| since | 13 | 13 | 1.45 | 0.63 | 2.23 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.34 | 1.01 | 2.22 | 0 | 0 | 0 |
| until | 6 | 6 | 1.38 | 1.23 | 1.83 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.17 | 0.93 | 1.52 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.17 | 0.94 | 1.69 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.33 | 1.26 | 1.43 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.98 | 1.29 | 3.29 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 1.50 | 1.08 | 2.15 | 0 | 0 | 0 |
| let | 4 | 4 | 1.19 | 1.02 | 1.27 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.33 | 1.11 | 1.56 | 0 | 0 | 0 |
| long | 12 | 12 | 1.31 | 0.99 | 1.71 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.79 | 0.91 | 3.85 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 1.98 | 3.85 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.87 | 2.86 | 3.29 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.87 | 2.81 | 3.24 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.23 | 3.62 | 2.94 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.50 | 4.40 | 2.94 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.85 | 2.49 | 2.93 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.22 | 3.56 | 2.92 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.86 | 2.24 | 2.59 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 3.93 | 2.56 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.63 | 4.13 | 2.54 |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.53 | 3.64 | 2.38 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.99 | 2.25 | 2.28 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.71 | 1.59 | 2.25 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.01 | 2.26 | 2.24 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.86 | 1.91 | 2.23 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.63 | 0.63 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.47 | 1.03 | 0.70 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.43 | 0.36 | 0.84 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.57 | 0.52 | 0.91 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.23 | 1.12 | 0.92 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.35 | 0.32 | 0.92 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.34 | 0.31 | 0.92 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.89 | 0.83 | 0.93 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.85 | 0.80 | 0.94 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.48 | 0.46 | 0.96 |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 185 | 183 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 183 formulas both finish: geometric mean of dense/monpoly = **1.39**, median 1.26, 18 where dense is faster, 38 within 10%, 28 where dense is more than 2x slower, 3 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.94 | 1.63 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.97 | 1.10 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.10 | 0.99 | 1.23 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.15 | 1.08 | 1.21 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.11 | 0.95 | 1.38 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.06 | 0.84 | 1.40 | 0 | 0 | 0 |
| once | 16 | 16 | 1.22 | 0.71 | 1.83 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 2.04 | 1.33 | 3.02 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.23 | 1.18 | 1.35 | 0 | 0 | 0 |
| since | 13 | 13 | 1.53 | 0.62 | 2.41 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.33 | 1.02 | 2.18 | 0 | 0 | 0 |
| until | 6 | 6 | 1.38 | 1.25 | 1.82 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.17 | 0.92 | 1.47 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.15 | 0.92 | 1.51 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.32 | 1.22 | 1.47 | 0 | 0 | 0 |
| agg_once | 22 | 20 | 2.32 | 1.51 | 4.33 | 0 | 2 | 0 |
| agg_fut | 5 | 5 | 1.97 | 1.27 | 2.99 | 0 | 0 | 0 |
| let | 4 | 4 | 1.22 | 1.11 | 1.27 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.32 | 1.14 | 1.55 | 0 | 0 | 0 |
| long | 12 | 12 | 1.37 | 1.01 | 1.90 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.92 | 0.94 | 5.49 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 2.83 | 5.49 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.87 | 3.76 | 4.33 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.87 | 3.69 | 4.25 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.23 | 4.65 | 3.78 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.86 | 3.10 | 3.59 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.50 | 4.53 | 3.02 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.85 | 2.55 | 2.99 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.05 | 3.01 | 2.86 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.85 | 2.42 | 2.85 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.60 | 1.65 | 2.77 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.08 | 2.98 | 2.75 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.71 | 1.91 | 2.71 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 4.00 | 2.60 |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.41 | 3.58 | 2.54 |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.01 | 2.53 | 2.51 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.62 | 0.62 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.47 | 1.04 | 0.71 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.43 | 0.36 | 0.84 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.23 | 1.11 | 0.91 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.85 | 0.78 | 0.92 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.89 | 0.82 | 0.92 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.34 | 0.32 | 0.92 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.35 | 0.32 | 0.93 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.57 | 0.54 | 0.94 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.33 | 0.31 | 0.94 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.22 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.53 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.32 | 0.32 | 0.32 | 1.01 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.45 | 0.47 | 0.47 | 1.04 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.31 | 0.39 | 0.39 | 1.29 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.45 | 0.54 | 0.53 | 1.21 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.38 | 0.39 | 0.40 | 1.03 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.42 | 0.42 | 0.44 | 0.99 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.35 | 0.42 | 0.39 | 1.20 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.20 | 0.31 | 0.32 | 1.58 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.33 | 0.32 | 0.31 | 0.96 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.13 | 0.14 | 0.14 | 1.10 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.44 | 0.48 | 0.47 | 1.07 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.85 | 0.88 | 0.87 | 1.04 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.49 | 0.48 | 0.48 | 0.97 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.39 | 0.43 | 0.43 | 1.09 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.45 | 0.44 | 0.44 | 0.99 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.39 | 0.43 | 0.43 | 1.09 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.45 | 0.52 | 0.53 | 1.14 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.47 | 0.55 | 0.56 | 1.15 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.36 | 0.42 | 0.42 | 1.15 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.46 | 0.57 | 0.57 | 1.23 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.44 | 0.43 | 0.45 | 0.99 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.44 | 0.43 | 0.43 | 0.98 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.36 | 0.40 | 0.42 | 1.12 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.26 | 0.32 | 0.32 | 1.21 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.34 | 0.40 | 0.41 | 1.17 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.36 | 0.42 | 0.41 | 1.17 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.40 | 0.45 | 0.45 | 1.12 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.45 | 0.48 | 0.48 | 1.06 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.42 | 0.47 | 0.47 | 1.13 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.34 | 0.42 | 0.41 | 1.21 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.48 | 0.46 | 0.46 | 0.96 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.47 | 0.47 | 0.46 | 1.00 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.36 | 0.51 | 0.50 | 1.40 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.44 | 0.46 | 0.46 | 1.03 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.33 | 0.39 | 0.39 | 1.19 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.37 | 0.43 | 0.44 | 1.16 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.28 | 0.39 | 0.39 | 1.41 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.28 | 0.39 | 0.39 | 1.42 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.35 | 0.32 | 0.32 | 0.92 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.31 | 0.32 | 0.32 | 1.03 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.43 | 0.43 | 0.45 | 1.00 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.43 | 0.36 | 0.36 | 0.84 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.34 | 0.31 | 0.32 | 0.92 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.30 | 0.32 | 0.32 | 1.07 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.30 | 0.42 | 0.42 | 1.41 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.37 | 0.45 | 0.46 | 1.23 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.40 | 0.48 | 0.48 | 1.21 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.47 | 0.54 | 0.54 | 1.14 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.56 | 0.65 | 0.66 | 1.16 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.87 | 1.14 | 1.12 | 1.31 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.42 | 2.31 | 2.29 | 1.63 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.37 | 1.99 | 2.01 | 1.46 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.73 | 0.75 | 0.75 | 1.02 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.14 | 1.14 | 1.16 | 1.00 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.00 | 2.17 | 2.11 | 1.08 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.23 | 1.12 | 1.11 | 0.92 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.47 | 1.03 | 1.04 | 0.70 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.88 | 1.54 | 1.61 | 1.74 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.83 | 1.33 | 1.37 | 1.61 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.84 | 1.07 | 1.09 | 1.28 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.68 | 1.06 | 1.06 | 1.56 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.99 | 2.25 | 2.22 | 2.28 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.50 | 4.40 | 4.53 | 2.94 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.76 | 1.02 | 1.02 | 1.34 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.63 | 4.13 | 3.99 | 2.54 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.15 | 0.18 | 0.18 | 1.20 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.53 | 2.05 | 2.07 | 1.34 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.72 | 0.84 | 0.86 | 1.17 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.64 | 0.78 | 0.78 | 1.23 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.63 | 0.65 | 0.68 | 1.04 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.62 | 0.72 | 0.75 | 1.16 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.64 | 0.84 | 0.87 | 1.30 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.50 | 0.77 | 0.77 | 1.55 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.50 | 0.84 | 0.83 | 1.66 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.54 | 0.96 | 0.97 | 1.78 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.66 | 1.41 | 1.40 | 2.14 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.86 | 1.91 | 1.87 | 2.23 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.96 | 2.15 | 2.09 | 2.23 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.83 | 1.16 | 1.36 | 1.40 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.18 | 1.80 | 2.84 | 1.52 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.00 | 0.63 | 0.62 | 0.63 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.44 | 0.55 | 0.54 | 1.26 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.52 | 0.55 | 0.54 | 1.06 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.76 | 0.92 | 0.92 | 1.22 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.57 | 2.69 | 2.57 | 1.71 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.66 | 0.66 | 0.67 | 1.01 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.92 | 0.99 | 1.01 | 1.08 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.71 | 2.69 | 2.57 | 1.57 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.35 | 0.45 | 0.45 | 1.26 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.06 | 2.35 | 2.30 | 2.22 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.57 | 0.76 | 0.75 | 1.35 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.62 | 0.76 | 0.78 | 1.23 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.63 | 0.79 | 0.80 | 1.26 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.43 | 0.59 | 0.61 | 1.37 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.52 | 0.69 | 0.65 | 1.31 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.81 | 1.48 | 1.48 | 1.83 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.89 | 0.83 | 0.82 | 0.93 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.15 | 1.26 | 1.28 | 1.09 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.62 | 2.01 | 2.01 | 1.24 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.34 | 0.41 | 0.40 | 1.21 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.57 | 0.68 | 0.67 | 1.18 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.58 | 0.70 | 0.69 | 1.21 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.49 | 0.61 | 0.68 | 1.25 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.22 | 1.85 | 1.80 | 1.52 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.53 | 0.51 | 0.52 | 0.96 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.60 | 0.64 | 0.65 | 1.07 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.29 | 1.31 | 1.30 | 1.02 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 2.23 | 2.28 | 2.29 | 1.02 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.85 | 0.80 | 0.78 | 0.94 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.37 | 1.37 | 1.35 | 1.00 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.43 | 1.39 | 1.43 | 0.97 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.00 | 1.70 | 1.49 | 1.69 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.74 | 0.89 | 0.89 | 1.21 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.65 | 0.98 | 0.97 | 1.52 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.65 | 0.80 | 0.80 | 1.23 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.18 | 1.72 | 1.66 | 1.46 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.50 | 0.67 | 0.65 | 1.34 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.50 | 0.66 | 0.65 | 1.34 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.49 | 0.65 | 0.64 | 1.32 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.48 | 0.63 | 0.64 | 1.33 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.56 | 0.73 | 0.74 | 1.30 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.55 | 0.73 | 0.73 | 1.32 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.37 | 0.54 | 0.55 | 1.43 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.47 | 0.60 | 0.58 | 1.26 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.81 | 1.52 | 1.76 | 1.87 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.05 | 2.28 | 3.01 | 2.17 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.23 | 3.62 | 4.65 | 2.94 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.78 | 1.47 | 1.82 | 1.88 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.08 | 2.20 | 2.98 | 2.03 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.22 | 3.56 | timeout | 2.92 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.71 | 1.59 | 1.91 | 2.25 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.87 | 2.86 | 3.76 | 3.29 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.87 | 2.81 | 3.69 | 3.24 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.03 | 1.82 | 2.13 | 1.77 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.41 | 2.79 | 3.58 | 1.98 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.08 | 2.00 | 2.27 | 1.85 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.57 | 2.90 | 3.38 | 1.84 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.26 | 0.44 | 0.50 | 1.68 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.29 | 0.45 | 0.50 | 1.56 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.29 | 0.45 | 0.47 | 1.58 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.30 | 0.44 | 0.50 | 1.50 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.45 | 0.64 | 0.71 | 1.41 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.48 | 0.62 | 0.73 | 1.29 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.53 | 3.64 | timeout | 2.38 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.60 | 1.23 | 1.65 | 2.07 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.00 | 3.13 | 3.84 | 1.56 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.08 | 1.41 | 1.96 | 1.31 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.73 | 1.88 | 2.99 | 1.08 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.54 | 0.70 | 0.68 | 1.30 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.85 | 1.83 | 2.55 | 2.15 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.01 | 1.95 | 2.53 | 1.94 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.46 | 0.47 | 0.51 | 1.02 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.31 | 0.39 | 0.39 | 1.27 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.40 | 0.49 | 0.49 | 1.23 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.44 | 0.54 | 0.54 | 1.23 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.34 | 0.46 | 0.45 | 1.37 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.39 | 0.52 | 0.52 | 1.36 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.51 | 0.73 | 0.73 | 1.44 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.47 | 0.55 | 0.55 | 1.18 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.40 | 0.51 | 0.52 | 1.28 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.36 | 0.49 | 0.50 | 1.37 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.33 | 0.52 | 0.52 | 1.56 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.44 | 0.49 | 0.50 | 1.11 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.56 | 0.67 | 0.65 | 1.19 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.82 | 0.95 | 1.00 | 1.16 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.53 | 2.20 | 2.15 | 1.44 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 1.86 | 2.62 | 2.56 | 1.41 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.49 | 1.48 | 1.51 | 0.99 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 1.91 | 2.40 | 2.35 | 1.26 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.35 | 1.54 | 1.57 | 1.14 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 1.94 | 2.69 | 2.61 | 1.39 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.89 | 1.27 | 1.30 | 1.44 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.56 | 0.95 | 1.05 | 1.71 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.60 | 0.92 | 1.08 | 1.54 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.04 | 3.78 | 4.82 | 1.24 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.42 | 0.50 | 0.47 | 1.19 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.57 | 0.52 | 0.54 | 0.91 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 3.93 | 4.00 | 2.56 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.82 | 1.22 | 1.24 | 1.48 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.51 | 1.98 | 2.83 | 3.85 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.86 | 2.24 | 3.10 | 2.59 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.48 | 0.56 | 0.57 | 1.18 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.01 | 2.26 | 2.23 | 2.24 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.85 | 2.49 | 2.42 | 2.93 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.47 | 0.50 | 0.53 | 1.06 | yes | a Let-bound condition used positively and negatively |
