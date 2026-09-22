# Performance suite: monpoly vs vdense vs dense

185 formulas, 21 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 866 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 185 | 185 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 185 formulas both finish: geometric mean of vdense/monpoly = **1.31**, median 1.26, 25 where vdense is faster, 50 within 10%, 16 where vdense is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.11 | 0.96 | 1.55 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.03 | 0.97 | 1.06 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.08 | 0.95 | 1.26 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.13 | 1.05 | 1.21 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.11 | 0.97 | 1.43 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.04 | 0.82 | 1.40 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.64 | 1.81 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 1.97 | 1.28 | 2.85 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.22 | 1.13 | 1.35 | 0 | 0 | 0 |
| since | 13 | 13 | 1.46 | 0.62 | 2.23 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.29 | 0.98 | 2.06 | 0 | 0 | 0 |
| until | 6 | 6 | 1.36 | 1.23 | 1.74 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.18 | 0.95 | 1.45 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.16 | 0.94 | 1.66 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.33 | 1.22 | 1.47 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.70 | 1.19 | 2.66 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 1.30 | 0.89 | 1.85 | 0 | 0 | 0 |
| let | 4 | 4 | 1.24 | 1.16 | 1.36 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.31 | 1.09 | 1.47 | 0 | 0 | 0 |
| long | 12 | 12 | 1.28 | 0.97 | 1.64 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.67 | 0.92 | 2.77 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.54 | 4.39 | 2.85 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.93 | 2.58 | 2.77 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 4.12 | 2.68 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.88 | 2.35 | 2.66 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 2.38 | 2.64 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.66 | 4.15 | 2.49 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.98 | 2.36 | 2.41 |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.54 | 1.28 | 2.37 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.85 | 1.89 | 2.23 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.95 | 2.09 | 2.21 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.06 | 2.24 | 2.11 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.21 | 2.50 | 2.07 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.09 | 2.24 | 2.06 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.87 | 1.75 | 2.01 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.68 | 1.37 | 2.01 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.07 | 0.66 | 0.62 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.07 | 0.64 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.44 | 0.36 | 0.82 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.80 | 1.60 | 0.89 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.25 | 1.15 | 0.92 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.35 | 0.33 | 0.92 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.58 | 0.54 | 0.92 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.87 | 0.82 | 0.94 |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.46 | 0.43 | 0.95 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.90 | 0.86 | 0.95 |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 185 | 183 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 183 formulas both finish: geometric mean of dense/monpoly = **1.39**, median 1.28, 21 where dense is faster, 40 within 10%, 29 where dense is more than 2x slower, 3 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.12 | 0.97 | 1.54 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.03 | 0.97 | 1.06 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.10 | 0.96 | 1.26 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.13 | 1.03 | 1.20 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.09 | 0.93 | 1.42 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.04 | 0.81 | 1.39 | 0 | 0 | 0 |
| once | 16 | 16 | 1.21 | 0.64 | 1.73 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 1.98 | 1.32 | 2.94 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.22 | 1.17 | 1.36 | 0 | 0 | 0 |
| since | 13 | 13 | 1.53 | 0.59 | 2.38 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.29 | 1.00 | 2.05 | 0 | 0 | 0 |
| until | 6 | 6 | 1.37 | 1.27 | 1.79 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.17 | 0.93 | 1.44 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.16 | 0.96 | 1.48 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.33 | 1.22 | 1.47 | 0 | 0 | 0 |
| agg_once | 22 | 21 | 2.36 | 1.51 | 4.34 | 0 | 1 | 0 |
| agg_fut | 5 | 5 | 1.91 | 1.30 | 2.99 | 0 | 0 | 0 |
| let | 4 | 4 | 1.28 | 1.16 | 1.52 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.31 | 1.14 | 1.45 | 0 | 0 | 0 |
| long | 12 | 11 | 1.33 | 1.02 | 1.79 | 0 | 1 | 0 |
| policy | 10 | 10 | 1.92 | 0.91 | 5.48 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.54 | 2.97 | 5.48 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.88 | 3.84 | 4.34 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 3.81 | 4.24 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.24 | 4.65 | 3.76 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.21 | 4.43 | 3.68 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.87 | 3.03 | 3.47 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.97 | 3.01 | 3.11 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.87 | 2.60 | 2.99 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.54 | 4.52 | 2.94 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.68 | 1.93 | 2.84 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.05 | 2.94 | 2.79 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.93 | 2.52 | 2.70 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 4.09 | 2.65 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.62 | 1.62 | 2.63 |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.40 | 3.61 | 2.57 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.07 | 0.63 | 0.59 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.07 | 0.64 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.44 | 0.35 | 0.81 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.35 | 0.31 | 0.87 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.25 | 1.14 | 0.91 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.58 | 0.53 | 0.91 |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.50 | 0.47 | 0.93 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.90 | 0.84 | 0.93 |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.47 | 0.45 | 0.95 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.34 | 0.33 | 0.96 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.56 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.27 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.33 | 0.32 | 0.32 | 0.98 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.46 | 0.47 | 0.47 | 1.01 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.34 | 0.41 | 0.40 | 1.23 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.46 | 0.57 | 0.58 | 1.24 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.39 | 0.42 | 0.42 | 1.06 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.46 | 0.44 | 0.45 | 0.96 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.38 | 0.42 | 0.43 | 1.13 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.21 | 0.33 | 0.33 | 1.55 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.34 | 0.33 | 0.33 | 0.97 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.13 | 0.14 | 0.14 | 1.05 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.46 | 0.48 | 0.48 | 1.05 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.87 | 0.90 | 0.91 | 1.04 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.51 | 0.49 | 0.49 | 0.97 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.40 | 0.43 | 0.43 | 1.06 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.46 | 0.44 | 0.45 | 0.96 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.41 | 0.44 | 0.45 | 1.07 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.47 | 0.54 | 0.54 | 1.15 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.47 | 0.55 | 0.56 | 1.18 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.37 | 0.41 | 0.42 | 1.12 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.45 | 0.57 | 0.57 | 1.26 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.44 | 0.45 | 0.45 | 1.01 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.46 | 0.43 | 0.44 | 0.95 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.38 | 0.41 | 0.42 | 1.07 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.27 | 0.33 | 0.32 | 1.21 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.34 | 0.40 | 0.41 | 1.17 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.37 | 0.43 | 0.41 | 1.15 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.42 | 0.46 | 0.47 | 1.09 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.48 | 0.50 | 0.49 | 1.05 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.44 | 0.49 | 0.47 | 1.09 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.35 | 0.41 | 0.42 | 1.18 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.50 | 0.48 | 0.47 | 0.97 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.46 | 0.46 | 0.45 | 0.98 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.37 | 0.52 | 0.52 | 1.43 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.47 | 0.46 | 0.45 | 0.98 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.33 | 0.39 | 0.40 | 1.18 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.38 | 0.45 | 0.44 | 1.19 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.28 | 0.40 | 0.39 | 1.40 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.29 | 0.39 | 0.37 | 1.34 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.34 | 0.33 | 0.33 | 0.95 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.33 | 0.32 | 0.32 | 0.98 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.43 | 0.45 | 0.45 | 1.04 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.44 | 0.36 | 0.35 | 0.82 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.35 | 0.33 | 0.31 | 0.92 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.31 | 0.31 | 0.33 | 1.00 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.30 | 0.41 | 0.42 | 1.35 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.35 | 0.46 | 0.45 | 1.30 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.40 | 0.47 | 0.49 | 1.19 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.48 | 0.53 | 0.53 | 1.09 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.56 | 0.65 | 0.65 | 1.17 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.88 | 1.18 | 1.14 | 1.34 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.53 | 2.47 | 2.42 | 1.61 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.51 | 2.26 | 2.22 | 1.50 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.75 | 0.76 | 0.78 | 1.01 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.19 | 1.17 | 1.18 | 0.98 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.12 | 2.32 | 2.38 | 1.10 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.25 | 1.15 | 1.14 | 0.92 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.07 | 1.07 | 0.64 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.92 | 1.67 | 1.59 | 1.81 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.89 | 1.40 | 1.39 | 1.58 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.87 | 1.15 | 1.15 | 1.33 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.70 | 1.07 | 1.02 | 1.53 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.06 | 2.24 | 2.23 | 2.11 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.54 | 4.39 | 4.52 | 2.85 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.77 | 0.99 | 1.02 | 1.28 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.66 | 4.15 | 4.26 | 2.49 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.16 | 0.19 | 0.18 | 1.22 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.56 | 2.10 | 2.12 | 1.35 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.76 | 0.86 | 0.88 | 1.13 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.65 | 0.76 | 0.77 | 1.17 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.62 | 0.66 | 0.68 | 1.07 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.63 | 0.76 | 0.76 | 1.20 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.65 | 0.84 | 0.84 | 1.29 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.51 | 0.79 | 0.81 | 1.55 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.49 | 0.85 | 0.85 | 1.73 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.54 | 0.93 | 0.97 | 1.73 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.71 | 1.39 | 1.41 | 1.97 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.85 | 1.89 | 1.96 | 2.23 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.95 | 2.09 | 2.05 | 2.21 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.78 | 1.20 | 1.35 | 1.54 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.24 | 1.84 | 2.95 | 1.48 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.07 | 0.66 | 0.63 | 0.62 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.42 | 0.55 | 0.53 | 1.31 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.53 | 0.55 | 0.55 | 1.04 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.86 | 0.95 | 0.95 | 1.11 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.71 | 2.61 | 2.65 | 1.53 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.66 | 0.65 | 0.67 | 0.98 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.93 | 1.00 | 1.01 | 1.07 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.69 | 2.72 | 2.62 | 1.61 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.34 | 0.44 | 0.44 | 1.28 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.09 | 2.24 | 2.23 | 2.06 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.57 | 0.75 | 0.75 | 1.31 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.60 | 0.81 | 0.81 | 1.35 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.63 | 0.82 | 0.81 | 1.29 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.48 | 0.59 | 0.61 | 1.23 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.54 | 0.72 | 0.70 | 1.32 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.87 | 1.51 | 1.56 | 1.74 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.90 | 0.86 | 0.84 | 0.95 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.21 | 1.31 | 1.32 | 1.09 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.64 | 2.06 | 2.02 | 1.25 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.34 | 0.43 | 0.42 | 1.24 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.58 | 0.68 | 0.70 | 1.19 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.56 | 0.69 | 0.68 | 1.22 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.51 | 0.70 | 0.68 | 1.37 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.28 | 1.86 | 1.85 | 1.45 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.53 | 0.52 | 0.51 | 0.99 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.60 | 0.65 | 0.67 | 1.08 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.32 | 1.33 | 1.34 | 1.00 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 2.28 | 2.38 | 2.36 | 1.04 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.87 | 0.82 | 0.84 | 0.94 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.35 | 1.39 | 1.36 | 1.03 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.45 | 1.42 | 1.46 | 0.98 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.06 | 1.76 | 1.47 | 1.66 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.72 | 0.89 | 0.91 | 1.23 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.66 | 0.94 | 0.93 | 1.43 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.66 | 0.83 | 0.78 | 1.25 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.20 | 1.63 | 1.78 | 1.36 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.50 | 0.66 | 0.63 | 1.32 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.48 | 0.64 | 0.65 | 1.33 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.49 | 0.65 | 0.65 | 1.34 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.48 | 0.66 | 0.64 | 1.36 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.57 | 0.74 | 0.75 | 1.31 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.57 | 0.75 | 0.77 | 1.31 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.36 | 0.53 | 0.53 | 1.47 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.47 | 0.58 | 0.58 | 1.22 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.80 | 1.28 | 1.80 | 1.61 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.05 | 1.78 | 2.94 | 1.69 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.21 | 2.50 | 4.43 | 2.07 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.78 | 1.21 | 1.75 | 1.55 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.97 | 1.69 | 3.01 | 1.75 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.24 | 2.49 | 4.65 | 2.01 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.68 | 1.37 | 1.93 | 2.01 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.88 | 2.35 | 3.84 | 2.66 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 2.38 | 3.81 | 2.64 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.07 | 1.64 | 2.15 | 1.53 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.40 | 2.33 | 3.61 | 1.66 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.12 | 1.86 | 2.38 | 1.66 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.58 | 2.54 | 3.50 | 1.61 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.31 | 0.46 | 0.51 | 1.51 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.31 | 0.46 | 0.50 | 1.50 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.31 | 0.47 | 0.51 | 1.51 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.30 | 0.45 | 0.50 | 1.50 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.48 | 0.63 | 0.73 | 1.30 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.49 | 0.58 | 0.74 | 1.19 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.56 | 3.03 | timeout | 1.94 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.62 | 1.17 | 1.62 | 1.90 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.06 | 2.77 | 4.12 | 1.35 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.16 | 1.28 | 2.00 | 1.10 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.80 | 1.60 | 2.95 | 0.89 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.53 | 0.72 | 0.70 | 1.34 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.87 | 1.61 | 2.60 | 1.85 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.12 | 1.67 | 2.59 | 1.50 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.45 | 0.52 | 0.52 | 1.16 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.27 | 0.37 | 0.42 | 1.36 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.43 | 0.51 | 0.51 | 1.18 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.42 | 0.53 | 0.55 | 1.26 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.36 | 0.48 | 0.47 | 1.33 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.41 | 0.56 | 0.55 | 1.35 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.52 | 0.76 | 0.73 | 1.47 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.48 | 0.55 | 0.55 | 1.14 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.39 | 0.52 | 0.52 | 1.31 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.35 | 0.50 | 0.50 | 1.42 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.35 | 0.50 | 0.51 | 1.44 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.43 | 0.47 | 0.49 | 1.09 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.56 | 0.67 | 0.62 | 1.20 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.83 | 0.99 | 1.00 | 1.20 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.58 | 2.21 | 2.27 | 1.40 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 1.87 | 2.66 | 2.66 | 1.42 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.44 | 1.40 | 1.47 | 0.97 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 1.90 | 2.35 | 2.37 | 1.23 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.40 | 1.52 | 1.57 | 1.09 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 1.88 | 2.67 | 2.67 | 1.41 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.87 | 1.28 | 1.25 | 1.48 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.61 | 1.00 | 1.09 | 1.64 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.57 | 0.80 | 0.92 | 1.39 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.27 | 3.45 | timeout | 1.06 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.43 | 0.50 | 0.49 | 1.16 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.58 | 0.54 | 0.53 | 0.92 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.54 | 4.12 | 4.09 | 2.68 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.89 | 1.32 | 1.34 | 1.48 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.54 | 1.28 | 2.97 | 2.37 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.87 | 1.75 | 3.03 | 2.01 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.49 | 0.58 | 0.59 | 1.18 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.98 | 2.36 | 2.28 | 2.41 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.93 | 2.58 | 2.52 | 2.77 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.47 | 0.51 | 0.53 | 1.09 | yes | a Let-bound condition used positively and negatively |
