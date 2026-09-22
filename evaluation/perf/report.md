# Performance suite: monpoly vs vdense vs dense

196 formulas, 22 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 926 s (budget 2400 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 196 | 196 |
| timeout | 0 | 0 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 196 formulas both finish: geometric mean of vdense/monpoly = **1.29**, median 1.26, 33 where vdense is faster, 46 within 10%, 16 where vdense is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.09 | 0.93 | 1.45 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.04 | 0.94 | 1.29 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.05 | 0.95 | 1.26 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.12 | 1.03 | 1.23 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.08 | 0.94 | 1.49 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.02 | 0.73 | 1.39 | 0 | 0 | 0 |
| once | 16 | 16 | 1.19 | 0.62 | 1.74 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 1.97 | 1.27 | 3.08 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.17 | 1.13 | 1.22 | 0 | 0 | 0 |
| since | 13 | 13 | 1.42 | 0.61 | 2.18 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.28 | 1.00 | 1.86 | 0 | 0 | 0 |
| until | 6 | 6 | 1.35 | 1.26 | 1.71 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.14 | 0.96 | 1.46 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.11 | 0.89 | 1.54 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.34 | 1.24 | 1.49 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.69 | 1.13 | 2.64 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 1.28 | 0.85 | 1.80 | 0 | 0 | 0 |
| let | 4 | 4 | 1.18 | 1.06 | 1.26 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.31 | 1.06 | 1.54 | 0 | 0 | 0 |
| long | 12 | 12 | 1.27 | 1.01 | 1.45 | 0 | 0 | 0 |
| policy | 10 | 10 | 1.58 | 0.78 | 2.92 | 0 | 0 | 0 |
| match | 11 | 11 | 1.55 | 1.16 | 2.01 | 0 | 0 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.59 | 4.90 | 3.08 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.89 | 2.58 | 2.92 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 2.39 | 2.64 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.50 | 3.81 | 2.53 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.94 | 2.37 | 2.53 |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.53 | 1.34 | 2.53 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.69 | 4.23 | 2.50 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.23 | 2.75 | 2.23 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.20 | 2.66 | 2.23 |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.00 | 2.18 | 2.18 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.80 | 1.75 | 2.18 |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.90 | 1.96 | 2.16 |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.70 | 1.50 | 2.16 |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.03 | 2.13 | 2.07 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.09 | 2.19 | 2.01 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.05 | 0.64 | 0.61 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.03 | 0.62 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.50 | 0.37 | 0.73 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.60 | 0.47 | 0.78 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.42 | 0.35 | 0.83 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.90 | 1.61 | 0.85 |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.47 | 0.41 | 0.87 |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.89 | 0.79 | 0.89 |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.50 | 1.37 | 0.91 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.30 | 1.20 | 0.92 |

## dense against monpoly

| | monpoly | dense |
|---|---|---|
| ok | 196 | 194 |
| timeout | 0 | 2 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 194 formulas both finish: geometric mean of dense/monpoly = **1.35**, median 1.24, 31 where dense is faster, 52 within 10%, 26 where dense is more than 2x slower, 3 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean dense/monpoly | min | max | monpoly timeouts | dense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.12 | 0.96 | 1.52 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.99 | 1.22 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.05 | 0.93 | 1.23 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.13 | 1.06 | 1.26 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.09 | 0.94 | 1.53 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.03 | 0.76 | 1.42 | 0 | 0 | 0 |
| once | 16 | 16 | 1.22 | 0.66 | 1.74 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 2.00 | 1.32 | 2.91 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.24 | 1.18 | 1.39 | 0 | 0 | 0 |
| since | 13 | 13 | 1.51 | 0.63 | 2.38 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.29 | 1.03 | 1.89 | 0 | 0 | 0 |
| until | 6 | 6 | 1.35 | 1.24 | 1.70 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.16 | 0.91 | 1.48 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.12 | 0.95 | 1.46 | 0 | 0 | 0 |
| agg | 8 | 8 | 1.31 | 1.23 | 1.44 | 0 | 0 | 0 |
| agg_once | 22 | 21 | 2.35 | 1.43 | 4.28 | 0 | 1 | 0 |
| agg_fut | 5 | 5 | 1.91 | 1.28 | 2.97 | 0 | 0 | 0 |
| let | 4 | 4 | 1.16 | 1.10 | 1.24 | 0 | 0 | 0 |
| wide | 8 | 8 | 1.29 | 1.00 | 1.51 | 0 | 0 | 0 |
| long | 12 | 11 | 1.33 | 1.02 | 1.65 | 0 | 1 | 0 |
| policy | 10 | 10 | 1.87 | 0.85 | 5.18 | 0 | 0 | 0 |
| match | 11 | 11 | 1.01 | 0.73 | 1.32 | 0 | 0 | 0 |

### Where dense is slowest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.53 | 2.75 | 5.18 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 3.87 | 4.28 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.94 | 3.91 | 4.18 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.20 | 4.74 | 3.96 |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.23 | 4.84 | 3.92 |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.80 | 2.94 | 3.67 |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.62 | 1.85 | 2.98 |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.91 | 2.69 | 2.97 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.59 | 4.63 | 2.91 |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.08 | 3.13 | 2.90 |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.11 | 3.15 | 2.83 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.89 | 2.46 | 2.78 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.77 | 1.97 | 2.57 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.69 | 4.32 | 2.55 |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.50 | 3.78 | 2.52 |

### Where dense is fastest relative to monpoly

| name | log | formula | monpoly s | dense s | ratio |
|---|---|---|---|---|---|
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.05 | 0.67 | 0.63 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.09 | 0.66 |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.56 | 0.41 | 0.73 |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.50 | 0.38 | 0.76 |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.42 | 0.34 | 0.81 |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.60 | 0.51 | 0.85 |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.61 | 0.54 | 0.88 |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.30 | 1.16 | 0.89 |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.94 | 0.85 | 0.91 |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.42 | 0.38 | 0.91 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | dense |
|---|---|---|---|---|
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.63 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.01 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | dense s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.35 | 0.33 | 0.36 | 0.93 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.49 | 0.54 | 0.53 | 1.10 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.42 | 0.54 | 0.56 | 1.28 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.64 | 0.76 | 0.72 | 1.18 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.50 | 0.48 | 0.53 | 0.95 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.48 | 0.46 | 0.47 | 0.94 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.38 | 0.44 | 0.41 | 1.15 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.23 | 0.33 | 0.34 | 1.45 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.34 | 0.33 | 0.33 | 0.96 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.11 | 0.14 | 0.13 | 1.29 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.47 | 0.49 | 0.49 | 1.03 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.95 | 0.90 | 0.94 | 0.94 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.52 | 0.50 | 0.51 | 0.97 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.42 | 0.42 | 0.42 | 1.01 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.48 | 0.45 | 0.44 | 0.95 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.42 | 0.43 | 0.41 | 1.02 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.48 | 0.57 | 0.55 | 1.18 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.47 | 0.54 | 0.55 | 1.14 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.41 | 0.39 | 0.42 | 0.95 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.46 | 0.58 | 0.57 | 1.26 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.45 | 0.44 | 0.44 | 0.99 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.46 | 0.44 | 0.45 | 0.96 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.37 | 0.39 | 0.42 | 1.05 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.28 | 0.33 | 0.33 | 1.17 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.35 | 0.39 | 0.38 | 1.11 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.39 | 0.43 | 0.43 | 1.12 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.40 | 0.48 | 0.47 | 1.19 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.47 | 0.48 | 0.51 | 1.03 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.46 | 0.47 | 0.49 | 1.04 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.34 | 0.42 | 0.43 | 1.23 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.49 | 0.46 | 0.46 | 0.94 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.49 | 0.45 | 0.47 | 0.94 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.34 | 0.50 | 0.51 | 1.49 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.47 | 0.46 | 0.47 | 0.99 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.35 | 0.38 | 0.38 | 1.08 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.38 | 0.42 | 0.43 | 1.11 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.29 | 0.39 | 0.40 | 1.33 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.29 | 0.40 | 0.41 | 1.39 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.37 | 0.35 | 0.35 | 0.93 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.30 | 0.32 | 0.32 | 1.07 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.43 | 0.46 | 0.46 | 1.09 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.50 | 0.37 | 0.38 | 0.73 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.42 | 0.35 | 0.34 | 0.83 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.34 | 0.32 | 0.34 | 0.96 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.32 | 0.42 | 0.41 | 1.28 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.35 | 0.42 | 0.43 | 1.20 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.41 | 0.47 | 0.47 | 1.14 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.47 | 0.57 | 0.62 | 1.21 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.57 | 0.70 | 0.69 | 1.23 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.89 | 1.22 | 1.18 | 1.37 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.55 | 2.46 | 2.41 | 1.58 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.44 | 2.22 | 2.19 | 1.55 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.78 | 0.74 | 0.80 | 0.95 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.17 | 1.13 | 1.21 | 0.96 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.09 | 2.15 | 2.28 | 1.03 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.30 | 1.20 | 1.16 | 0.92 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.67 | 1.03 | 1.09 | 0.62 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.86 | 1.50 | 1.50 | 1.74 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.86 | 1.39 | 1.47 | 1.61 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.87 | 1.10 | 1.16 | 1.27 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.71 | 1.07 | 1.13 | 1.50 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.09 | 2.19 | 2.24 | 2.01 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.59 | 4.90 | 4.63 | 3.08 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.83 | 1.05 | 1.09 | 1.27 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.69 | 4.23 | 4.32 | 2.50 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.16 | 0.18 | 0.19 | 1.16 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.66 | 2.02 | 2.31 | 1.22 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.78 | 0.88 | 0.91 | 1.13 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.66 | 0.78 | 0.80 | 1.19 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.68 | 0.70 | 0.70 | 1.03 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.69 | 0.76 | 0.77 | 1.11 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.65 | 0.85 | 0.87 | 1.31 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.53 | 0.79 | 0.80 | 1.48 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.54 | 0.81 | 0.86 | 1.50 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.55 | 0.98 | 0.97 | 1.79 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.70 | 1.50 | 1.53 | 2.16 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.90 | 1.96 | 1.96 | 2.16 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.00 | 2.18 | 2.25 | 2.18 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.86 | 1.19 | 1.31 | 1.37 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.29 | 1.88 | 3.07 | 1.45 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.05 | 0.64 | 0.67 | 0.61 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.45 | 0.57 | 0.57 | 1.27 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.51 | 0.54 | 0.55 | 1.05 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.86 | 0.99 | 1.00 | 1.15 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.74 | 2.84 | 2.70 | 1.64 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.68 | 0.68 | 0.70 | 1.00 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.94 | 1.03 | 0.98 | 1.10 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.71 | 2.66 | 2.85 | 1.55 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.38 | 0.45 | 0.46 | 1.18 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.23 | 2.28 | 2.33 | 1.86 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.60 | 0.78 | 0.76 | 1.31 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.63 | 0.85 | 0.82 | 1.36 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.67 | 0.85 | 0.83 | 1.26 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.49 | 0.62 | 0.65 | 1.27 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.56 | 0.71 | 0.75 | 1.27 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.91 | 1.55 | 1.54 | 1.71 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.94 | 0.92 | 0.85 | 0.97 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.19 | 1.26 | 1.33 | 1.05 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.61 | 1.93 | 1.96 | 1.20 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.36 | 0.43 | 0.42 | 1.19 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.62 | 0.69 | 0.71 | 1.11 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.59 | 0.70 | 0.73 | 1.19 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.52 | 0.63 | 0.69 | 1.21 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.26 | 1.84 | 1.86 | 1.46 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.56 | 0.54 | 0.54 | 0.96 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.63 | 0.63 | 0.69 | 0.99 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.35 | 1.34 | 1.30 | 0.99 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 2.42 | 2.48 | 2.44 | 1.02 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.89 | 0.79 | 0.84 | 0.89 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.50 | 1.37 | 1.44 | 0.91 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.54 | 1.47 | 1.51 | 0.96 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.15 | 1.77 | 1.49 | 1.54 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.80 | 0.90 | 0.93 | 1.13 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.69 | 0.96 | 1.01 | 1.39 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.67 | 0.84 | 0.85 | 1.25 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.32 | 1.66 | 1.78 | 1.25 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.56 | 0.70 | 0.69 | 1.25 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.52 | 0.64 | 0.64 | 1.24 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.46 | 0.63 | 0.65 | 1.36 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.48 | 0.71 | 0.62 | 1.46 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.54 | 0.73 | 0.76 | 1.35 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.59 | 0.76 | 0.73 | 1.29 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.37 | 0.54 | 0.53 | 1.49 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.46 | 0.60 | 0.57 | 1.30 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.82 | 1.28 | 1.87 | 1.55 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.11 | 1.91 | 3.15 | 1.72 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.20 | 2.66 | 4.74 | 2.23 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.79 | 1.37 | 1.91 | 1.72 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.08 | 1.78 | 3.13 | 1.65 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.23 | 2.75 | 4.84 | 2.23 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.77 | 1.38 | 1.97 | 1.81 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.94 | 2.37 | 3.91 | 2.53 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.90 | 2.39 | 3.87 | 2.64 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.14 | 1.77 | 2.25 | 1.55 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 1.55 | 2.48 | 3.86 | 1.59 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.18 | 1.83 | 2.33 | 1.55 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.71 | 2.67 | 3.71 | 1.56 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.29 | 0.44 | 0.50 | 1.52 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.32 | 0.47 | 0.52 | 1.43 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.31 | 0.47 | 0.49 | 1.54 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.30 | 0.47 | 0.50 | 1.57 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.50 | 0.62 | 0.71 | 1.24 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.50 | 0.57 | 0.73 | 1.13 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.63 | 3.18 | timeout | 1.96 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.62 | 1.14 | 1.85 | 1.83 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.16 | 3.00 | 4.21 | 1.39 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.20 | 1.33 | 2.01 | 1.11 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.90 | 1.61 | 3.19 | 0.85 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.58 | 0.72 | 0.75 | 1.23 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.91 | 1.63 | 2.69 | 1.80 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.13 | 1.88 | 2.69 | 1.66 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.50 | 0.53 | 0.55 | 1.06 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.33 | 0.40 | 0.40 | 1.24 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.45 | 0.52 | 0.51 | 1.16 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.46 | 0.57 | 0.52 | 1.26 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.38 | 0.51 | 0.48 | 1.35 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.41 | 0.55 | 0.56 | 1.33 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.53 | 0.81 | 0.77 | 1.54 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.51 | 0.57 | 0.56 | 1.11 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.42 | 0.52 | 0.53 | 1.25 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.33 | 0.48 | 0.51 | 1.43 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.36 | 0.52 | 0.51 | 1.46 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.48 | 0.51 | 0.48 | 1.06 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.57 | 0.70 | 0.70 | 1.22 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.85 | 1.05 | 1.08 | 1.24 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.64 | 2.38 | 2.25 | 1.45 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 1.88 | 2.70 | 2.65 | 1.44 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.49 | 1.51 | 1.52 | 1.01 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 1.91 | 2.45 | 2.40 | 1.29 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.42 | 1.57 | 1.65 | 1.10 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 2.04 | 2.81 | 2.80 | 1.38 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.91 | 1.31 | 1.29 | 1.44 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.64 | 0.88 | 0.99 | 1.39 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.61 | 0.82 | 1.01 | 1.33 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.01 | 3.24 | timeout | 1.08 | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.47 | 0.41 | 0.50 | 0.87 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.60 | 0.47 | 0.51 | 0.78 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.50 | 3.81 | 3.78 | 2.53 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.79 | 1.11 | 1.31 | 1.40 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.53 | 1.34 | 2.75 | 2.53 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.80 | 1.75 | 2.94 | 2.18 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.48 | 0.60 | 0.54 | 1.26 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.03 | 2.13 | 2.25 | 2.07 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.89 | 2.58 | 2.46 | 2.92 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.51 | 0.49 | 0.54 | 0.97 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.35 | 0.46 | 0.33 | 1.31 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.36 | 0.50 | 0.34 | 1.40 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.47 | 0.74 | 0.53 | 1.57 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.37 | 0.75 | 0.37 | 2.01 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.56 | 1.08 | 0.41 | 1.92 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.41 | 0.47 | 0.40 | 1.16 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.61 | 0.96 | 0.54 | 1.57 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.42 | 0.69 | 0.38 | 1.66 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.61 | 1.04 | 0.72 | 1.71 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.40 | 0.62 | 0.53 | 1.56 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.36 | 0.50 | 0.45 | 1.37 | NO | an aggregate over a past regex |
