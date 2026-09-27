# Performance suite: monpoly vs verimon

The starting point: both systems from a build of master (025a1423), where `-verified` is the original VeriMon, on the same suite and logs as `report.md`.  Run on 2026-09-27 on SCI1029244, one run after the other with `report.md`, so the two compare.

285 formulas, 30 families; 3 repetitions (best of), timeout 5 s per run, 8 workers; wall time 198 s (budget 3600 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 264 | 259 |
| timeout | 0 | 25 |
| refused | 0 | 0 |
| unmonitorable | 21 | 1 |
| error | 0 | 0 |

Over the 240 formulas both finish: geometric mean of verimon/monpoly = **3.69**, median 3.35, 0 where verimon is faster, 0 within 10%, 196 where verimon is more than 2x slower, 73 more than 4x slower.

Verdict disagreements: match-pcnt

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 8 | 2.07 | 1.27 | 3.52 | 0 | 1 | 0 |
| join_scale | 5 | 5 | 3.35 | 2.44 | 4.84 | 0 | 0 | 0 |
| andnot | 8 | 8 | 3.63 | 3.09 | 5.21 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.86 | 1.44 | 3.50 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.69 | 1.29 | 2.20 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.64 | 1.18 | 3.69 | 0 | 0 | 0 |
| once | 16 | 16 | 3.43 | 2.06 | 4.56 | 0 | 0 | 0 |
| once_exists | 5 | 5 | 3.84 | 3.24 | 4.26 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 3.89 | 3.35 | 4.20 | 0 | 0 | 0 |
| since | 13 | 13 | 3.05 | 1.39 | 3.76 | 0 | 0 | 0 |
| eventually | 8 | 8 | 3.21 | 2.30 | 3.88 | 0 | 0 | 0 |
| until | 6 | 6 | 2.13 | 1.92 | 2.77 | 0 | 0 | 0 |
| burst | 9 | 9 | 2.68 | 1.96 | 4.21 | 0 | 0 | 0 |
| nested | 11 | 5 | 4.24 | 3.32 | 4.88 | 0 | 6 | 0 |
| agg | 8 | 8 | 2.46 | 2.18 | 3.54 | 0 | 0 | 0 |
| agg_once | 22 | 20 | 3.81 | 2.29 | 5.98 | 0 | 2 | 0 |
| agg_fut | 5 | 5 | 3.78 | 2.24 | 6.31 | 0 | 0 | 0 |
| let | 4 | 4 | 2.76 | 1.78 | 4.30 | 0 | 0 | 0 |
| wide | 8 | 8 | 3.78 | 2.11 | 5.09 | 0 | 0 | 0 |
| long | 12 | 11 | 3.33 | 2.59 | 4.23 | 0 | 1 | 0 |
| policy | 10 | 8 | 4.30 | 2.12 | 9.49 | 0 | 2 | 0 |
| match | 11 | 11 | 2.36 | 1.29 | 4.85 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |
| frz | 29 | 20 | 45.28 | 5.61 | 113.91 | 0 | 9 | 0 |
| frz_rw | 8 | 7 | 3.26 | 2.56 | 4.31 | 0 | 1 | 0 |
| past_inf | 5 | 5 | 2.45 | 1.20 | 3.88 | 0 | 0 | 0 |
| derived | 6 | 6 | 2.88 | 1.28 | 8.52 | 0 | 0 | 0 |
| terms | 10 | 10 | 2.24 | 1.47 | 9.20 | 0 | 0 | 0 |
| agg_more | 10 | 8 | 3.25 | 1.69 | 6.74 | 0 | 2 | 0 |
| vm_only | 16 | 0 | - | - | - | 0 | 1 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| frz-ev5 | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[0,5] (A(x,y) AND q(x))` | 0.04 | 4.11 | 113.91 |
| frz-next | tp500 | `FRZ q(x) = C(x) IN NEXT[0,5] (A(x,y) AND q(x))` | 0.03 | 2.90 | 102.88 |
| frz-evlb | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[2,10] (A(x,y) AND q(x))` | 0.04 | 3.97 | 91.26 |
| frz-since | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[0,10] (A(x,y) AND q(x)))` | 0.05 | 3.80 | 81.21 |
| frz-tbody | tp250 | `FRZ q(x) = ONCE[0,10] C(x) IN ONCE[0,10] (A(x,y) AND q(x))` | 0.05 | 3.82 | 80.76 |
| frz-sincelb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[2,10] (A(x,y) AND q(x)))` | 0.05 | 3.65 | 76.78 |
| frz-agg | tp500 | `FRZ q(x) = C(x) IN (r <- CNT y; x ONCE[0,10] (A(x,y) AND q(x)))` | 0.04 | 2.90 | 66.89 |
| frz-until | tp250 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[0,5] (A(x,y) AND q(x)))` | 0.03 | 2.06 | 63.83 |
| frz-once5 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,5] (A(x,y) AND q(x))` | 0.04 | 2.22 | 62.75 |
| frz-exists | tp500 | `FRZ q(x) = C(x) IN EXISTS y. ONCE[0,10] (A(x,y) AND q(x))` | 0.04 | 2.55 | 59.13 |
| frz-now | tp500 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.03 | 1.44 | 57.09 |
| frz-oncelb | tp500 | `FRZ q(x) = C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.04 | 2.34 | 54.14 |
| frz-outer | tp500 | `C(x) AND (FRZ q(x) = C(x) IN ONCE[0,10] (EXISTS y. A(x,y) AND q(x)))` | 0.04 | 1.98 | 49.84 |
| frz-prev | tp500 | `FRZ q(x) = C(x) IN PREV[0,5] (A(x,y) AND q(x))` | 0.03 | 1.46 | 45.03 |
| frz-once20 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.06 | 2.42 | 42.49 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.22 | 0.26 | 1.18 |
| inf-prev | base | `A(x,y) AND PREV[1,*) B(x,y)` | 0.23 | 0.27 | 1.20 |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.22 | 0.27 | 1.20 |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.21 | 0.26 | 1.24 |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.22 | 0.28 | 1.27 |
| join-both | base | `A(x,y) AND B(x,y)` | 0.21 | 0.27 | 1.28 |
| der-false | base | `A(x,y) OR (FALSE AND B(x,y))` | 0.26 | 0.33 | 1.28 |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.28 | 0.36 | 1.29 |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.22 | 0.29 | 1.29 |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.21 | 0.28 | 1.34 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.26 s | timeout |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.82 s | timeout |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.51 s | timeout |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.54 s | timeout |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.86 s | timeout |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.86 s | timeout |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.59 s | timeout |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.93 s | timeout |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.95 s | timeout |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 2.20 s | timeout |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.05 s | timeout |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.56 s | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.57 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.58 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.91 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.59 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.55 s |
| frz-untillb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[2,10] (A(x,y) AND q(x)))` | 0.07 s | timeout |
| frz-lagphi | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.07 s | timeout |
| frz-neglag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.07 s | timeout |
| frz-sincelag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.07 s | timeout |
| frz-neglag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.05 s | timeout |
| frz-sincelag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.08 s | timeout |
| frz-nested | tp250 | `FRZ q(x) = C(x) IN FRZ r(y) = C(y) IN ONCE[0,10] (A(x,y) AND q(x) AND r(y))` | 0.86 s | timeout |
| frz-len1000 | tp1000 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.10 s | timeout |
| frz-now1000 | tp1000 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.04 s | timeout |
| frzrw-once2 | base | `A(x,y) AND ONCE[0,5] NOT B(x,y)` | 0.85 s | timeout |
| agg-avgonce | base | `r <- AVG y; x ONCE[0,20] A(x,y)` | 0.91 s | timeout |
| agg-avgev | base | `r <- AVG y; x EVENTUALLY[0,20] A(x,y)` | 1.40 s | timeout |
| trig-plain | base | `A(x,y) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.37 s |
| trig-neg | base | `(NOT A(x,y)) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.48 s |
| trig-inf | base | `C(x) TRIGGER[0,*) (EXISTS y. B(x,y))` | unmonitorable | 0.52 s |
| rel-plain | base | `A(x,y) RELEASE[0,5] B(x,y)` | unmonitorable | 0.80 s |
| rel-neg | base | `(NOT A(x,y)) RELEASE[0,5] B(x,y)` | unmonitorable | 1.72 s |
| lp-reach | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,*) r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.36 s |
| lp-reach5 | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.37 s |
| lp-once | base | `LETPAST r(x) = C(x) OR (EXISTS y. ONCE[1,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.89 s |
| lp-count | base | `LETPAST r(x) = C(x) OR PREV[0,*) (r(x) AND NOT (EXISTS y. B(x,y))) IN r(x)` | unmonitorable | 0.52 s |
| lp-chain | tp1000 | `LETPAST r(x,y) = A(x,y) OR (PREV[0,1] r(x,y) AND NOT B(x,y)) IN r(x,y)` | unmonitorable | timeout |
| der-hist5 | dom50 | `HISTORICALLY[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.44 s |
| der-hist20 | dom50 | `HISTORICALLY[0,20] C(x)` | unmonitorable | 0.25 s |
| der-always5 | dom50 | `ALWAYS[0,5] (EXISTS y. A(x,y))` | unmonitorable | 1.31 s |
| der-equiv | base | `A(x,y) AND (C(x) EQUIV C(y))` | unmonitorable | unmonitorable |
| vm-frztrig | base | `C(x) AND (NOT B(x,x) TRIGGER[0,5] C(x))` | unmonitorable | 0.33 s |
| vm-frzrel | base | `C(x) AND (NOT B(x,x) RELEASE[0,5] C(x))` | unmonitorable | 0.49 s |

## All formulas

| name | log | formula | monpoly s | verimon s | ratio | agree | why |
|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.21 | 0.27 | 1.28 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.25 | 0.83 | 3.25 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.22 | 0.38 | 1.72 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.26 | 0.90 | 3.52 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.26 | 0.45 | 1.76 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.26 | timeout | - | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.20 | 0.58 | 2.87 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.13 | 0.28 | 2.08 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.22 | 0.28 | 1.27 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.06 | 0.16 | 2.44 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.25 | 0.83 | 3.28 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 0.55 | 2.33 | 4.27 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.29 | 1.41 | 4.84 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.22 | 0.57 | 2.54 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.27 | 0.91 | 3.40 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.24 | 0.87 | 3.66 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.28 | 1.01 | 3.62 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.28 | 0.94 | 3.38 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.21 | 0.70 | 3.39 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.26 | 1.37 | 5.21 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.26 | 0.79 | 3.09 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.25 | 0.92 | 3.64 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.20 | 0.31 | 1.50 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.17 | 0.26 | 1.53 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.18 | 0.27 | 1.46 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.21 | 0.31 | 1.48 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.24 | 0.41 | 1.67 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.26 | 0.91 | 3.47 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.24 | 0.86 | 3.50 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.19 | 0.28 | 1.44 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.32 | 0.44 | 1.38 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.28 | 0.36 | 1.29 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.21 | 0.43 | 2.10 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.27 | 0.46 | 1.68 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.23 | 0.39 | 1.66 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.21 | 0.45 | 2.20 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.15 | 0.27 | 1.80 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.15 | 0.26 | 1.79 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.22 | 0.27 | 1.20 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.21 | 0.28 | 1.34 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.24 | 0.90 | 3.69 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.26 | 0.49 | 1.89 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.22 | 0.26 | 1.18 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.21 | 0.26 | 1.24 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.16 | 0.33 | 2.06 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.20 | 0.45 | 2.29 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.25 | 0.57 | 2.31 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.31 | 0.95 | 3.07 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.36 | 1.26 | 3.48 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 0.50 | 2.12 | 4.25 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 0.70 | 3.04 | 4.38 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 0.68 | 2.72 | 3.99 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.48 | 1.96 | 4.07 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 0.71 | 2.87 | 4.06 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 0.99 | 3.38 | 3.41 | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 0.89 | 2.77 | 3.13 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.02 | 3.05 | 3.00 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 0.51 | 2.30 | 4.56 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 0.49 | 1.96 | 4.04 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 0.50 | 2.11 | 4.27 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.41 | 1.65 | 4.01 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 0.66 | 2.73 | 4.13 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 0.97 | 4.15 | 4.26 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 0.50 | 1.64 | 3.24 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 1.15 | 4.21 | 3.65 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.10 | 0.33 | 3.35 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.92 | 3.88 | 4.20 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.42 | 1.64 | 3.88 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.40 | 1.66 | 4.17 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.38 | 1.09 | 2.85 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 0.38 | 1.12 | 2.98 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.38 | 1.20 | 3.13 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.33 | 1.03 | 3.11 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 0.33 | 1.06 | 3.17 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.34 | 1.13 | 3.36 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.43 | 1.54 | 3.60 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 0.49 | 1.78 | 3.63 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 0.49 | 1.81 | 3.71 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 0.51 | 1.89 | 3.67 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 0.82 | 3.09 | 3.76 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 0.59 | 0.82 | 1.39 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.28 | 0.66 | 2.36 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.34 | 0.88 | 2.62 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 0.47 | 1.38 | 2.93 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 0.76 | 2.64 | 3.49 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.40 | 1.53 | 3.85 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 0.52 | 2.02 | 3.88 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 0.75 | 2.77 | 3.67 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.20 | 0.45 | 2.30 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 0.69 | 2.33 | 3.35 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.35 | 0.70 | 1.99 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 0.36 | 0.75 | 2.05 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.37 | 0.80 | 2.18 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.30 | 0.58 | 1.92 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.33 | 0.65 | 1.97 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 0.51 | 1.41 | 2.77 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 0.53 | 1.84 | 3.49 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 0.65 | 2.26 | 3.47 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 0.73 | 2.55 | 3.48 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.22 | 0.50 | 2.30 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.34 | 0.70 | 2.06 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.35 | 0.73 | 2.11 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.30 | 0.63 | 2.06 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.59 | 2.47 | 4.21 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.34 | 0.66 | 1.96 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.36 | 1.74 | 4.88 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 0.82 | timeout | - | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 1.51 | timeout | - | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 0.54 | timeout | - | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 0.86 | timeout | - | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 0.86 | timeout | - | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 0.59 | timeout | - | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.44 | 1.90 | 4.31 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.39 | 1.69 | 4.34 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.37 | 1.24 | 3.32 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 0.65 | 2.95 | 4.53 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.26 | 0.64 | 2.43 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.26 | 0.61 | 2.35 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.26 | 0.62 | 2.37 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.26 | 0.62 | 2.36 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 0.30 | 0.66 | 2.21 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.31 | 0.67 | 2.18 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.19 | 0.47 | 2.48 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.27 | 0.96 | 3.54 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 0.53 | 2.17 | 4.09 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 0.70 | 3.29 | 4.70 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 0.73 | 3.95 | 5.45 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.52 | 2.14 | 4.14 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 0.68 | 3.25 | 4.79 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 0.73 | 3.83 | 5.24 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.48 | 2.24 | 4.68 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 0.61 | 3.62 | 5.91 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 0.61 | 3.67 | 5.98 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 0.68 | 3.34 | 4.90 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 0.93 | timeout | - | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 0.73 | 2.47 | 3.40 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 1.01 | 3.46 | 3.41 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.16 | 0.42 | 2.65 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.16 | 0.38 | 2.44 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.16 | 0.37 | 2.33 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.16 | 0.36 | 2.29 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.30 | 0.79 | 2.61 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.32 | 0.89 | 2.74 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.95 | timeout | - | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.34 | 1.90 | 5.50 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.51 | 4.56 | 3.02 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 0.72 | 2.01 | 2.81 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 1.13 | 2.54 | 2.24 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.31 | 1.11 | 3.64 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 0.53 | 2.84 | 5.33 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 0.75 | 4.72 | 6.31 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.29 | 1.23 | 4.30 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.22 | 0.39 | 1.78 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.24 | 0.48 | 1.96 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.25 | 0.98 | 3.89 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.20 | 0.88 | 4.49 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.22 | 1.08 | 4.86 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.26 | 1.32 | 5.09 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.26 | 1.10 | 4.19 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.22 | 0.89 | 4.13 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.19 | 0.48 | 2.49 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.19 | 0.40 | 2.11 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.29 | 1.19 | 4.13 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.36 | 1.14 | 3.18 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 0.48 | 1.82 | 3.81 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 0.69 | 2.94 | 4.23 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 0.75 | 2.95 | 3.91 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.70 | 2.72 | 3.91 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 0.93 | 2.59 | 2.80 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 0.63 | 2.20 | 3.48 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 0.81 | 2.80 | 3.46 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 0.37 | 1.07 | 2.89 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.23 | 0.64 | 2.78 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.23 | 0.61 | 2.59 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 2.20 | timeout | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.26 | 0.68 | 2.66 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.38 | 0.80 | 2.12 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.05 | timeout | - | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 0.58 | 2.91 | 5.05 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.31 | 2.93 | 9.49 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 0.56 | timeout | - | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.31 | 2.74 | 8.71 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 0.55 | 2.00 | 3.63 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 0.52 | 2.09 | 4.01 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.28 | 0.95 | 3.39 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.22 | 0.29 | 1.29 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.23 | 0.32 | 1.39 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.29 | 0.97 | 3.35 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.26 | 1.28 | 4.85 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.36 | 1.51 | 4.14 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.24 | 0.33 | 1.35 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.33 | 1.00 | 3.07 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.27 | 0.81 | 3.03 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.35 | 0.73 | 2.12 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.21 | 0.43 | 2.09 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.16 | 0.31 | 1.92 | NO | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 0.57 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 0.58 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 0.91 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 0.59 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.55 | - | yes | the trigger narrower than the conjunct |
| frz-now | tp500 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.03 | 1.44 | 57.09 | yes | no temporal operator under the freeze: the cost of FRZ itself |
| frz-once5 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,5] (A(x,y) AND q(x))` | 0.04 | 2.22 | 62.75 | yes | a past window over the frozen predicate |
| frz-once20 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.06 | 2.42 | 42.49 | yes | a wider one |
| frz-once100 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,100] (A(x,y) AND q(x))` | 0.17 | 2.60 | 15.17 | yes | wider still |
| frz-onceinf | tp500 | `FRZ q(x) = C(x) IN ONCE[0,*) (A(x,y) AND q(x))` | 0.40 | 2.26 | 5.61 | yes | the unbounded past |
| frz-oncelb | tp500 | `FRZ q(x) = C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.04 | 2.34 | 54.14 | yes | a window that misses the current time point |
| frz-prev | tp500 | `FRZ q(x) = C(x) IN PREV[0,5] (A(x,y) AND q(x))` | 0.03 | 1.46 | 45.03 | yes | the previous time point |
| frz-sincelb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[2,10] (A(x,y) AND q(x)))` | 0.05 | 3.65 | 76.78 | yes | a Since whose interval misses the current time point |
| frz-evlb | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[2,10] (A(x,y) AND q(x))` | 0.04 | 3.97 | 91.26 | yes | the future dual of frz-oncelb |
| frz-untillb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[2,10] (A(x,y) AND q(x)))` | 0.07 | timeout | - | yes | and of frz-sincelb |
| frz-lagphi | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.07 | timeout | - | yes | a frozen formula that lags: the window is replayed |
| frz-neglag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.07 | timeout | - | yes | it lags, and the frozen predicate is negated: nothing to hoist |
| frz-sincelag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.07 | timeout | - | yes | it lags, and the frozen predicate is the left operand of a Since |
| frz-neglag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.05 | timeout | - | yes | frz-neglag with a lag of 30 time points: many pending verdicts |
| frz-sincelag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.08 | timeout | - | yes | and frz-sincelag |
| frz-next | tp500 | `FRZ q(x) = C(x) IN NEXT[0,5] (A(x,y) AND q(x))` | 0.03 | 2.90 | 102.88 | yes | the next time point |
| frz-ev5 | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[0,5] (A(x,y) AND q(x))` | 0.04 | 4.11 | 113.91 | yes | a future window |
| frz-since | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[0,10] (A(x,y) AND q(x)))` | 0.05 | 3.80 | 81.21 | yes | the frozen predicate in Since's right operand |
| frz-until | tp250 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[0,5] (A(x,y) AND q(x)))` | 0.03 | 2.06 | 63.83 | yes | and in Until's |
| frz-tbody | tp250 | `FRZ q(x) = ONCE[0,10] C(x) IN ONCE[0,10] (A(x,y) AND q(x))` | 0.05 | 3.82 | 80.76 | yes | a temporal formula frozen |
| frz-nested | tp250 | `FRZ q(x) = C(x) IN FRZ r(y) = C(y) IN ONCE[0,10] (A(x,y) AND q(x) AND r(y))` | 0.86 | timeout | - | yes | two freezes, nested |
| frz-binary | tp500 | `FRZ q(x,y) = B(x,y) IN ONCE[0,10] (A(x,y) AND q(x,y))` | 0.04 | 0.65 | 15.44 | yes | a binary frozen predicate |
| frz-agg | tp500 | `FRZ q(x) = C(x) IN (r <- CNT y; x ONCE[0,10] (A(x,y) AND q(x)))` | 0.04 | 2.90 | 66.89 | yes | an aggregation over the frozen window |
| frz-exists | tp500 | `FRZ q(x) = C(x) IN EXISTS y. ONCE[0,10] (A(x,y) AND q(x))` | 0.04 | 2.55 | 59.13 | yes | a projection over it |
| frz-outer | tp500 | `C(x) AND (FRZ q(x) = C(x) IN ONCE[0,10] (EXISTS y. A(x,y) AND q(x)))` | 0.04 | 1.98 | 49.84 | yes | the freeze under a conjunction |
| frz-len250 | tp250 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.03 | 0.61 | 18.13 | yes | frz-once20 on 250 time points |
| frz-len1000 | tp1000 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.10 | timeout | - | yes | and on 1000 |
| frz-now250 | tp250 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.02 | 0.37 | 21.91 | yes | frz-now on 250 time points |
| frz-now1000 | tp1000 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.04 | timeout | - | yes | and on 1000 |
| frzrw-once | base | `C(x) AND ONCE[0,5] NOT B(x,x)` | 0.29 | 0.89 | 3.06 | yes | the guard frozen into a past window |
| frzrw-once20 | base | `C(x) AND ONCE[0,20] NOT B(x,x)` | 0.35 | 1.40 | 3.97 | yes | a wider one |
| frzrw-oncelb | base | `C(x) AND ONCE[2,10] NOT B(x,x)` | 0.41 | 1.14 | 2.77 | yes | a window that misses the current time point |
| frzrw-once2 | base | `A(x,y) AND ONCE[0,5] NOT B(x,y)` | 0.85 | timeout | - | yes | a binary guard |
| frzrw-sincer | base | `C(x) AND (C(x) SINCE[0,5] NOT B(x,x))` | 0.35 | 1.26 | 3.58 | yes | into Since's right operand |
| frzrw-sincelb | base | `C(x) AND ((EXISTS y. A(x,y)) SINCE[1,5] NOT B(x,x))` | 0.53 | 1.37 | 2.56 | yes | and with an interval that misses the current time point |
| frzrw-ev | base | `C(x) AND EVENTUALLY[0,5] NOT B(x,x)` | 0.31 | 1.32 | 4.31 | yes | into a future window |
| frzrw-untilr | base | `C(x) AND (C(x) UNTIL[0,5] NOT B(x,x))` | 0.31 | 0.90 | 2.91 | yes | into Until's right operand |
| inf-since | base | `A(x,y) SINCE[0,*) B(x,y)` | 0.33 | 1.05 | 3.16 | yes | unbounded Since |
| inf-sincelb | base | `A(x,y) SINCE[5,*) B(x,y)` | 0.32 | 0.71 | 2.19 | yes | with a lower bound |
| inf-negsince | base | `(NOT C(x)) SINCE[0,*) A(x,y)` | 1.20 | 3.30 | 2.74 | yes | with a negated left operand |
| inf-prev | base | `A(x,y) AND PREV[1,*) B(x,y)` | 0.23 | 0.27 | 1.20 | yes | Prev with an unbounded interval |
| inf-agg | base | `r <- CNT y; x ONCE[0,*) A(x,y)` | 0.66 | 2.55 | 3.88 | yes | an aggregation over the whole past |
| der-implies | base | `A(x,y) AND (C(x) IMPLIES B(x,y))` | 0.29 | 0.92 | 3.16 | yes | an implication under a guard |
| der-forall | base | `C(x) AND FORALL y. (A(x,y) IMPLIES y < 150)` | 0.20 | 0.40 | 2.00 | yes | a universal quantifier: an anti-join with a filter |
| der-true | base | `A(x,y) AND TRUE` | 0.22 | 0.85 | 3.86 | yes | a trivially true conjunct |
| der-false | base | `A(x,y) OR (FALSE AND B(x,y))` | 0.26 | 0.33 | 1.28 | yes | a trivially false disjunct |
| der-guardhist | base | `C(x) AND HISTORICALLY[0,5] (EXISTS y. A(x,y) OR B(x,y))` | 0.36 | 0.77 | 2.14 | yes | a guarded past Always |
| der-guardalw | base | `C(x) AND ALWAYS[0,5] (EXISTS y. A(x,y) OR B(x,y))` | 0.35 | 2.95 | 8.52 | yes | a guarded future Always |
| term-mul | base | `A(x,y) AND z = x * y` | 0.25 | 0.40 | 1.62 | yes | multiplication |
| term-mod | base | `A(x,y) AND z = x MOD 7` | 0.24 | 0.40 | 1.66 | yes | remainder |
| term-div | base | `A(x,y) AND z = x / 3` | 0.25 | 0.40 | 1.63 | yes | division |
| term-neg | base | `A(x,y) AND z = -x` | 0.25 | 0.41 | 1.64 | yes | negation |
| term-i2f | base | `A(x,y) AND z = i2f(x)` | 0.28 | 0.44 | 1.58 | yes | to a float |
| term-f2i | base | `A(x,y) AND z = f2i(i2f(x) + 0.5)` | 0.25 | 0.41 | 1.68 | yes | float arithmetic and back |
| term-modfilt | base | `A(x,y) AND x MOD 10 = 0` | 0.19 | 0.28 | 1.47 | yes | a constraint over a term |
| term-chain | base | `A(x,y) AND z = x + y AND w = z * 2 AND w < 300` | 0.21 | 0.39 | 1.83 | yes | assignments feeding assignments and a filter |
| term-tp | base | `A(x,y) AND tp(i)` | 0.27 | 1.79 | 6.75 | yes | the time point as a column |
| term-ts | base | `A(x,y) AND ts(t) AND t MOD 10 = 0` | 0.19 | 1.70 | 9.20 | yes | the timestamp as a column, filtered |
| agg-avgonce | base | `r <- AVG y; x ONCE[0,20] A(x,y)` | 0.91 | timeout | - | yes | AVG over a past window |
| agg-medonce | base | `r <- MED y; x ONCE[0,50] A(x,y)` | 1.14 | 3.92 | 3.45 | yes | MED over a wide one |
| agg-since | base | `r <- CNT y; x (B(x,y) SINCE[0,10] A(x,y))` | 0.43 | 1.59 | 3.72 | yes | over a Since |
| agg-until | base | `r <- SUM y; x (B(x,y) UNTIL[0,5] A(x,y))` | 0.40 | 1.11 | 2.74 | yes | over an Until |
| agg-avgev | base | `r <- AVG y; x EVENTUALLY[0,20] A(x,y)` | 1.40 | timeout | - | yes | AVG over a future window |
| agg-minev | base | `r <- MIN y; x EVENTUALLY[0,20] A(x,y)` | 1.16 | 2.76 | 2.38 | yes | MIN over a future window |
| agg-nested | base | `s <- MAX r (r <- CNT y; x ONCE[0,10] A(x,y))` | 0.50 | 3.35 | 6.74 | yes | an aggregation of an aggregation |
| agg-exists | base | `r <- CNT x (EXISTS y. ONCE[0,10] A(x,y))` | 0.54 | 3.19 | 5.91 | yes | over a projected window |
| agg-empty | base | `r <- CNT y ONCE[0,5] (A(x,y) AND x < 0)` | 0.18 | 0.30 | 1.69 | yes | over an always empty table: the default value |
| agg-float | base | `r <- SUM z; x (A(x,y) AND z = i2f(y))` | 0.31 | 0.70 | 2.23 | yes | a sum of floats |
| trig-plain | base | `A(x,y) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.37 | - | yes | Trigger |
| trig-neg | base | `(NOT A(x,y)) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.48 | - | yes | with a negated left operand |
| trig-inf | base | `C(x) TRIGGER[0,*) (EXISTS y. B(x,y))` | unmonitorable | 0.52 | - | yes | over the unbounded past |
| rel-plain | base | `A(x,y) RELEASE[0,5] B(x,y)` | unmonitorable | 0.80 | - | yes | Release |
| rel-neg | base | `(NOT A(x,y)) RELEASE[0,5] B(x,y)` | unmonitorable | 1.72 | - | yes | with a negated left operand |
| lp-reach | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,*) r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.36 | - | yes | recursion through the past: reachability along A |
| lp-reach5 | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.37 | - | yes | with a bounded step |
| lp-once | base | `LETPAST r(x) = C(x) OR (EXISTS y. ONCE[1,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.89 | - | yes | through a window |
| lp-count | base | `LETPAST r(x) = C(x) OR PREV[0,*) (r(x) AND NOT (EXISTS y. B(x,y))) IN r(x)` | unmonitorable | 0.52 | - | yes | a state kept until B resets it |
| lp-chain | tp1000 | `LETPAST r(x,y) = A(x,y) OR (PREV[0,1] r(x,y) AND NOT B(x,y)) IN r(x,y)` | unmonitorable | timeout | - | yes | a binary state; on a short log, its cost grows faster than the log |
| der-hist5 | dom50 | `HISTORICALLY[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.44 | - | yes | unguarded past Always |
| der-hist20 | dom50 | `HISTORICALLY[0,20] C(x)` | unmonitorable | 0.25 | - | yes | over a wider window |
| der-always5 | dom50 | `ALWAYS[0,5] (EXISTS y. A(x,y))` | unmonitorable | 1.31 | - | yes | unguarded future Always |
| der-equiv | base | `A(x,y) AND (C(x) EQUIV C(y))` | unmonitorable | unmonitorable | - | yes | an equivalence |
| vm-frztrig | base | `C(x) AND (NOT B(x,x) TRIGGER[0,5] C(x))` | unmonitorable | 0.33 | - | yes | the rewriter's freeze into a trigger |
| vm-frzrel | base | `C(x) AND (NOT B(x,x) RELEASE[0,5] C(x))` | unmonitorable | 0.49 | - | yes | and into a release |
