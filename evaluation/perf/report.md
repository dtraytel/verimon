# Performance suite: monpoly vs vdense

339 formulas, 35 families; 2 repetitions (best of), timeout 5 s per run, 2 workers; wall time 801 s (budget 1800 s).

## vdense against monpoly

| | monpoly | vdense |
|---|---|---|
| ok | 338 | 325 |
| timeout | 1 | 14 |
| refused | 0 | 0 |
| unmonitorable | 0 | 0 |
| error | 0 | 0 |

Over the 325 formulas both finish: geometric mean of vdense/monpoly = **1.38**, median 1.28, 20 where vdense is faster, 79 within 10%, 38 where vdense is more than 2x slower, 2 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean vdense/monpoly | min | max | monpoly timeouts | vdense timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 12 | 12 | 1.11 | 0.98 | 1.61 | 0 | 0 | 0 |
| join_rate | 8 | 8 | 1.07 | 1.03 | 1.13 | 0 | 0 | 0 |
| join_dom | 9 | 9 | 1.05 | 0.98 | 1.11 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.11 | 0.99 | 1.26 | 0 | 0 | 0 |
| andnot_dom | 6 | 6 | 1.03 | 1.00 | 1.09 | 0 | 0 | 0 |
| rel | 10 | 10 | 1.15 | 1.07 | 1.28 | 0 | 0 | 0 |
| or | 4 | 4 | 0.97 | 0.93 | 1.03 | 0 | 0 | 0 |
| exists | 6 | 6 | 1.27 | 1.00 | 1.45 | 0 | 0 | 0 |
| prevnext | 11 | 11 | 1.09 | 0.88 | 1.43 | 0 | 0 | 0 |
| once_raw | 6 | 6 | 1.30 | 1.19 | 1.37 | 0 | 0 | 0 |
| once_guard | 9 | 9 | 1.45 | 1.13 | 1.81 | 0 | 0 | 0 |
| once_first | 6 | 6 | 1.17 | 1.05 | 1.37 | 0 | 0 | 0 |
| once_lb | 5 | 5 | 0.97 | 0.81 | 1.05 | 0 | 0 | 0 |
| once_inf | 4 | 3 | 1.61 | 1.28 | 1.95 | 1 | 1 | 0 |
| once_exists | 6 | 4 | 1.81 | 1.43 | 2.32 | 0 | 2 | 0 |
| once_rate | 8 | 8 | 1.17 | 1.08 | 1.37 | 0 | 0 | 0 |
| once_dom | 9 | 9 | 1.24 | 1.11 | 1.38 | 0 | 0 | 0 |
| since | 21 | 20 | 1.65 | 0.68 | 3.23 | 0 | 1 | 0 |
| eventually | 10 | 10 | 1.26 | 1.05 | 1.63 | 0 | 0 | 0 |
| eventually_raw | 5 | 5 | 1.34 | 1.28 | 1.44 | 0 | 0 | 0 |
| eventually_burst | 11 | 11 | 1.16 | 1.01 | 1.28 | 0 | 0 | 0 |
| until | 11 | 11 | 1.59 | 1.36 | 2.28 | 0 | 0 | 0 |
| until_burst | 8 | 8 | 1.33 | 1.28 | 1.42 | 0 | 0 | 0 |
| nested | 24 | 24 | 1.20 | 0.98 | 1.85 | 0 | 0 | 0 |
| agg | 12 | 12 | 1.35 | 1.22 | 1.44 | 0 | 0 | 0 |
| agg_once | 18 | 13 | 2.81 | 2.15 | 3.92 | 0 | 5 | 0 |
| agg_once_cnt | 11 | 11 | 1.98 | 1.55 | 3.16 | 0 | 0 | 0 |
| agg_dom | 9 | 9 | 1.78 | 1.42 | 2.44 | 0 | 0 | 0 |
| agg_rate | 8 | 7 | 1.86 | 1.56 | 2.45 | 0 | 1 | 0 |
| agg_ev | 4 | 2 | 1.87 | 1.85 | 1.89 | 0 | 2 | 0 |
| agg_guard | 3 | 3 | 2.17 | 1.38 | 2.98 | 0 | 0 | 0 |
| let | 8 | 8 | 1.23 | 1.10 | 1.30 | 0 | 0 | 0 |
| wide | 17 | 17 | 1.31 | 1.04 | 1.59 | 0 | 0 | 0 |
| long | 20 | 19 | 1.40 | 1.05 | 1.86 | 0 | 1 | 0 |
| policy | 12 | 11 | 1.83 | 1.01 | 4.93 | 0 | 1 | 0 |

### Where vdense is slowest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| policy-07 | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.69 | 3.39 | 4.93 |
| policy-11 | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.13 | 4.71 | 4.17 |
| agg_once-12 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.12 | 4.41 | 3.92 |
| agg_once-09 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.12 | 4.30 | 3.85 |
| policy-08 | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.08 | 3.66 | 3.40 |
| agg_once-08 | base | `r <- MIN y; x ONCE[0,20] A(x,y)` | 1.12 | 3.71 | 3.32 |
| since-11 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,20] A(x,y))` | 1.02 | 3.29 | 3.23 |
| agg_once-11 | base | `r <- MAX y; x ONCE[0,20] A(x,y)` | 1.14 | 3.64 | 3.19 |
| agg_once_cnt-09 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.53 | 4.84 | 3.16 |
| since-12 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,100] A(x,y))` | 1.09 | 3.45 | 3.15 |
| since-13 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.20 | 3.70 | 3.09 |
| policy-10 | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.23 | 3.73 | 3.04 |
| agg_guard-02 | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.06 | 3.16 | 2.98 |
| since-10 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.87 | 2.56 | 2.94 |
| agg_once-10 | base | `r <- MAX y; x ONCE[0,5] A(x,y)` | 0.90 | 2.63 | 2.93 |

### Where vdense is fastest relative to monpoly

| name | log | formula | monpoly s | vdense s | ratio |
|---|---|---|---|---|---|
| since-19 | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.89 | 0.68 |
| since-18 | base | `A(x,y) SINCE[2,100] B(x,y)` | 1.12 | 0.80 | 0.71 |
| since-17 | base | `A(x,y) SINCE[2,5] B(x,y)` | 0.84 | 0.66 | 0.79 |
| once_lb-05 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.85 | 1.51 | 0.81 |
| prevnext-05 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.48 | 0.88 |
| or-01 | base | `A(x,y) OR B(x,y)` | 0.63 | 0.59 | 0.93 |
| once_lb-04 | base | `C(x) AND ONCE[100,120] A(x,y)` | 1.67 | 1.57 | 0.94 |
| prevnext-11 | burst | `A(x,y) AND PREV[1,1] B(x,y)` | 0.41 | 0.39 | 0.95 |
| prevnext-03 | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.43 | 0.96 |
| or-02 | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.60 | 0.57 | 0.96 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | vdense |
|---|---|---|---|---|
| once_inf-03 | rate10 | `C(x) AND ONCE[10,*) B(x,y)` | timeout | timeout |
| once_exists-05 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.97 s | timeout |
| once_exists-06 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.12 s | timeout |
| since-16 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,100] A(x,y))` | 4.07 s | timeout |
| agg_once-03 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.58 s | timeout |
| agg_once-06 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.55 s | timeout |
| agg_once-14 | base | `r <- AVG y; x ONCE[0,20] A(x,y)` | 1.99 s | timeout |
| agg_once-15 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.13 s | timeout |
| agg_once-18 | base | `r <- MED y; x ONCE[0,50] A(x,y)` | 2.52 s | timeout |
| agg_rate-07 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.00 s | timeout |
| agg_ev-03 | base | `r <- CNT y; x EVENTUALLY[0,20] A(x,y)` | 2.39 s | timeout |
| agg_ev-04 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.49 s | timeout |
| long-17 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.94 s | timeout |
| policy-05 | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.97 s | timeout |

## All formulas

| name | log | formula | monpoly s | vdense s | ratio | agree |
|---|---|---|---|---|---|---|
| join-01 | base | `A(x,y) AND B(x,y)` | 0.41 | 0.42 | 1.03 | yes |
| join-02 | base | `A(x,y) AND B(y,z)` | 0.58 | 0.61 | 1.05 | yes |
| join-03 | base | `A(x,y) AND B(y,x)` | 0.42 | 0.53 | 1.27 | yes |
| join-04 | base | `A(x,y) AND B(z,x)` | 0.57 | 0.71 | 1.25 | yes |
| join-05 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.51 | 0.53 | 1.04 | yes |
| join-06 | base | `A(x,y) AND B(y,z) AND C(x)` | 0.51 | 0.54 | 1.06 | yes |
| join-07 | base | `A(x,y) AND B(y,z) AND A(z,w)` | 0.57 | 0.59 | 1.02 | yes |
| join-08 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.55 | 0.56 | 1.02 | yes |
| join-09 | base | `A(x,y) AND D(y,z,w)` | 0.46 | 0.51 | 1.12 | yes |
| join-10 | base | `D(x,y,z) AND D(z,y,x)` | 0.26 | 0.42 | 1.61 | yes |
| join-11 | base | `D(x,y,z) AND A(x,y) AND B(y,z)` | 0.41 | 0.40 | 0.98 | yes |
| join-12 | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.43 | 0.42 | 0.99 | yes |
| join_rate-01 | rate10 | `A(x,y) AND B(y,z)` | 0.16 | 0.17 | 1.09 | yes |
| join_rate-02 | rate10 | `A(x,y) AND B(y,z) AND C(z)` | 0.12 | 0.13 | 1.03 | yes |
| join_rate-03 | rate20 | `A(x,y) AND B(y,z)` | 0.31 | 0.35 | 1.13 | yes |
| join_rate-04 | rate20 | `A(x,y) AND B(y,z) AND C(z)` | 0.24 | 0.25 | 1.07 | yes |
| join_rate-05 | base | `A(x,y) AND B(y,z)` | 0.59 | 0.61 | 1.04 | yes |
| join_rate-06 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.52 | 0.54 | 1.04 | yes |
| join_rate-07 | rate80 | `A(x,y) AND B(y,z)` | 1.15 | 1.19 | 1.03 | yes |
| join_rate-08 | rate80 | `A(x,y) AND B(y,z) AND C(z)` | 1.10 | 1.21 | 1.10 | yes |
| join_dom-01 | dom50 | `A(x,y) AND B(y,z)` | 0.63 | 0.62 | 0.98 | yes |
| join_dom-02 | dom50 | `A(x,y) AND B(x,y)` | 0.45 | 0.47 | 1.05 | yes |
| join_dom-03 | dom50 | `A(x,y) AND B(y,z) AND C(z)` | 0.62 | 0.64 | 1.04 | yes |
| join_dom-04 | base | `A(x,y) AND B(y,z)` | 0.56 | 0.61 | 1.09 | yes |
| join_dom-05 | base | `A(x,y) AND B(x,y)` | 0.40 | 0.43 | 1.06 | yes |
| join_dom-06 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.51 | 0.53 | 1.06 | yes |
| join_dom-07 | dom1000 | `A(x,y) AND B(y,z)` | 0.52 | 0.57 | 1.11 | yes |
| join_dom-08 | dom1000 | `A(x,y) AND B(x,y)` | 0.39 | 0.40 | 1.04 | yes |
| join_dom-09 | dom1000 | `A(x,y) AND B(y,z) AND C(z)` | 0.45 | 0.48 | 1.05 | yes |
| andnot-01 | base | `A(x,y) AND NOT B(x,y)` | 0.58 | 0.57 | 0.99 | yes |
| andnot-02 | base | `A(x,y) AND NOT C(x)` | 0.53 | 0.57 | 1.06 | yes |
| andnot-03 | base | `A(x,y) AND NOT C(y)` | 0.51 | 0.56 | 1.09 | yes |
| andnot-04 | base | `A(x,y) AND NOT B(y,x)` | 0.58 | 0.67 | 1.16 | yes |
| andnot-05 | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.57 | 0.72 | 1.25 | yes |
| andnot-06 | base | `D(x,y,z) AND NOT A(x,y)` | 0.46 | 0.51 | 1.11 | yes |
| andnot-07 | base | `A(x,y) AND B(y,z) AND NOT C(z)` | 0.60 | 0.61 | 1.02 | yes |
| andnot-08 | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.58 | 0.73 | 1.26 | yes |
| andnot_dom-01 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.55 | 0.55 | 1.00 | yes |
| andnot_dom-02 | dom50 | `A(x,y) AND NOT C(x)` | 0.52 | 0.53 | 1.01 | yes |
| andnot_dom-03 | base | `A(x,y) AND NOT B(x,y)` | 0.56 | 0.57 | 1.02 | yes |
| andnot_dom-04 | base | `A(x,y) AND NOT C(x)` | 0.51 | 0.55 | 1.09 | yes |
| andnot_dom-05 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.56 | 0.56 | 1.00 | yes |
| andnot_dom-06 | dom1000 | `A(x,y) AND NOT C(x)` | 0.50 | 0.54 | 1.08 | yes |
| rel-01 | base | `A(x,y) AND x < y` | 0.46 | 0.52 | 1.14 | yes |
| rel-02 | base | `A(x,y) AND x < 20` | 0.41 | 0.53 | 1.28 | yes |
| rel-03 | base | `A(x,y) AND x = y` | 0.35 | 0.43 | 1.23 | yes |
| rel-04 | base | `A(x,y) AND NOT x < y` | 0.46 | 0.53 | 1.14 | yes |
| rel-05 | base | `A(x,y) AND z = x + y` | 0.52 | 0.59 | 1.13 | yes |
| rel-06 | base | `A(x,y) AND z = 2 * x` | 0.51 | 0.58 | 1.12 | yes |
| rel-07 | base | `A(x,y) AND z = x - y` | 0.52 | 0.58 | 1.13 | yes |
| rel-08 | base | `A(x,y) AND B(y,z) AND x < z` | 0.55 | 0.60 | 1.09 | yes |
| rel-09 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.57 | 0.61 | 1.07 | yes |
| rel-10 | base | `A(x,y) AND x < y AND y < 100` | 0.45 | 0.52 | 1.18 | yes |
| or-01 | base | `A(x,y) OR B(x,y)` | 0.63 | 0.59 | 0.93 | yes |
| or-02 | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.60 | 0.57 | 0.96 | yes |
| or-03 | base | `A(x,y) OR B(y,x)` | 0.68 | 0.71 | 1.03 | yes |
| or-04 | base | `(A(x,y) AND NOT C(x)) OR (B(x,y) AND NOT C(y))` | 0.69 | 0.67 | 0.97 | yes |
| exists-01 | base | `EXISTS y. A(x,y)` | 0.46 | 0.66 | 1.42 | yes |
| exists-02 | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.57 | 0.57 | 1.00 | yes |
| exists-03 | base | `EXISTS x. EXISTS y. A(x,y) AND B(y,z)` | 0.55 | 0.72 | 1.31 | yes |
| exists-04 | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.42 | 0.53 | 1.25 | yes |
| exists-05 | base | `EXISTS z. D(x,y,z)` | 0.36 | 0.53 | 1.45 | yes |
| exists-06 | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.45 | 0.55 | 1.23 | yes |
| prevnext-01 | base | `PREV[0,1] C(x)` | 0.35 | 0.49 | 1.39 | yes |
| prevnext-02 | base | `NEXT[0,1] C(x)` | 0.35 | 0.50 | 1.43 | yes |
| prevnext-03 | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.45 | 0.43 | 0.96 | yes |
| prevnext-04 | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.42 | 0.43 | 1.02 | yes |
| prevnext-05 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.54 | 0.48 | 0.88 | yes |
| prevnext-06 | base | `PREV[0,1] PREV[0,1] C(x)` | 0.36 | 0.49 | 1.36 | yes |
| prevnext-07 | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.53 | 0.57 | 1.07 | yes |
| prevnext-08 | base | `A(x,y) AND NOT NEXT[0,1] A(x,y)` | 0.50 | 0.57 | 1.13 | yes |
| prevnext-09 | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.43 | 0.42 | 0.96 | yes |
| prevnext-10 | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.40 | 0.42 | 1.05 | yes |
| prevnext-11 | burst | `A(x,y) AND PREV[1,1] B(x,y)` | 0.41 | 0.39 | 0.95 | yes |
| once_raw-01 | base | `ONCE[0,0] C(x)` | 0.37 | 0.52 | 1.37 | yes |
| once_raw-02 | base | `ONCE[0,1] C(x)` | 0.40 | 0.54 | 1.36 | yes |
| once_raw-03 | base | `ONCE[0,2] C(x)` | 0.42 | 0.55 | 1.30 | yes |
| once_raw-04 | base | `ONCE[0,5] C(x)` | 0.44 | 0.58 | 1.32 | yes |
| once_raw-05 | base | `ONCE[0,10] C(x)` | 0.47 | 0.59 | 1.24 | yes |
| once_raw-06 | base | `ONCE[0,20] C(x)` | 0.52 | 0.62 | 1.19 | yes |
| once_guard-01 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.61 | 0.69 | 1.13 | yes |
| once_guard-02 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.73 | 0.87 | 1.19 | yes |
| once_guard-03 | base | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.93 | 1.20 | 1.30 | yes |
| once_guard-04 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.09 | 1.47 | 1.35 | yes |
| once_guard-05 | base | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.25 | 1.87 | 1.49 | yes |
| once_guard-06 | base | `A(x,y) AND ONCE[0,200] B(x,y)` | 1.44 | 2.34 | 1.62 | yes |
| once_guard-07 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 1.80 | 3.25 | 1.81 | yes |
| once_guard-08 | base | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.90 | 3.34 | 1.75 | yes |
| once_guard-09 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 1.69 | 2.63 | 1.56 | yes |
| once_first-01 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 0.97 | 1.02 | 1.05 | yes |
| once_first-02 | base | `A(x,y) AND NOT ONCE[1,20] A(x,y)` | 1.26 | 1.36 | 1.09 | yes |
| once_first-03 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.45 | 1.63 | 1.12 | yes |
| once_first-04 | base | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.76 | 1.96 | 1.11 | yes |
| once_first-05 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | 2.47 | 3.37 | 1.37 | yes |
| once_first-06 | base | `A(x,y) AND NOT ONCE[1,2000] A(x,y)` | 2.06 | 2.74 | 1.33 | yes |
| once_lb-01 | base | `C(x) AND ONCE[1,21] A(x,y)` | 1.54 | 1.62 | 1.05 | yes |
| once_lb-02 | base | `C(x) AND ONCE[5,25] A(x,y)` | 1.54 | 1.58 | 1.03 | yes |
| once_lb-03 | base | `C(x) AND ONCE[20,40] A(x,y)` | 1.53 | 1.57 | 1.03 | yes |
| once_lb-04 | base | `C(x) AND ONCE[100,120] A(x,y)` | 1.67 | 1.57 | 0.94 | yes |
| once_lb-05 | base | `C(x) AND ONCE[500,520] A(x,y)` | 1.85 | 1.51 | 0.81 | yes |
| once_inf-01 | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.09 | 2.12 | 1.95 | yes |
| once_inf-02 | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.17 | 1.96 | 1.68 | yes |
| once_inf-03 | rate10 | `C(x) AND ONCE[10,*) B(x,y)` | timeout | timeout | - | yes |
| once_inf-04 | rate10 | `A(x,y) AND NOT ONCE[10,*) B(x,y)` | 0.42 | 0.54 | 1.28 | yes |
| once_exists-01 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 0.88 | 1.49 | 1.69 | yes |
| once_exists-02 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 1.01 | 1.45 | 1.43 | yes |
| once_exists-03 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.30 | 3.00 | 2.32 | yes |
| once_exists-04 | base | `C(x) AND NOT (EXISTS y. ONCE[1,20] A(x,y))` | 1.44 | 2.74 | 1.90 | yes |
| once_exists-05 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 1.97 | timeout | - | yes |
| once_exists-06 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.12 | timeout | - | yes |
| once_rate-01 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.19 | 0.23 | 1.18 | yes |
| once_rate-02 | rate10 | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.42 | 0.46 | 1.08 | yes |
| once_rate-03 | rate20 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.41 | 0.50 | 1.21 | yes |
| once_rate-04 | rate20 | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 0.79 | 0.87 | 1.11 | yes |
| once_rate-05 | base | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.94 | 1.20 | 1.27 | yes |
| once_rate-06 | base | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.69 | 1.84 | 1.09 | yes |
| once_rate-07 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 2.00 | 2.75 | 1.37 | yes |
| once_rate-08 | rate80 | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 3.87 | 4.26 | 1.10 | yes |
| once_dom-01 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.95 | 1.22 | 1.29 | yes |
| once_dom-02 | dom50 | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.18 | 1.33 | 1.13 | yes |
| once_dom-03 | dom50 | `ONCE[0,5] C(x)` | 0.40 | 0.56 | 1.38 | yes |
| once_dom-04 | base | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.93 | 1.18 | 1.26 | yes |
| once_dom-05 | base | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.66 | 1.84 | 1.11 | yes |
| once_dom-06 | base | `ONCE[0,5] C(x)` | 0.44 | 0.58 | 1.32 | yes |
| once_dom-07 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.80 | 1.03 | 1.28 | yes |
| once_dom-08 | dom1000 | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.66 | 1.87 | 1.12 | yes |
| once_dom-09 | dom1000 | `ONCE[0,5] C(x)` | 0.44 | 0.58 | 1.29 | yes |
| since-01 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.79 | 0.94 | 1.19 | yes |
| since-02 | base | `A(x,y) SINCE[0,20] B(x,y)` | 0.79 | 1.02 | 1.28 | yes |
| since-03 | base | `A(x,y) SINCE[0,100] B(x,y)` | 0.82 | 1.09 | 1.33 | yes |
| since-04 | base | `A(x,y) SINCE[0,500] B(x,y)` | 0.83 | 1.15 | 1.39 | yes |
| since-05 | base | `A(x,y) SINCE[0,2000] B(x,y)` | 0.84 | 1.20 | 1.42 | yes |
| since-06 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.66 | 1.26 | 1.91 | yes |
| since-07 | base | `B(x,y) AND (C(x) SINCE[0,20] A(x,y))` | 0.67 | 1.31 | 1.96 | yes |
| since-08 | base | `B(x,y) AND (C(x) SINCE[0,100] A(x,y))` | 0.67 | 1.36 | 2.02 | yes |
| since-09 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.69 | 1.46 | 2.11 | yes |
| since-10 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 0.87 | 2.56 | 2.94 | yes |
| since-11 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,20] A(x,y))` | 1.02 | 3.29 | 3.23 | yes |
| since-12 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,100] A(x,y))` | 1.09 | 3.45 | 3.15 | yes |
| since-13 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.20 | 3.70 | 3.09 | yes |
| since-14 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.08 | 1.94 | 1.80 | yes |
| since-15 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 1.58 | 3.92 | 2.49 | yes |
| since-16 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,100] A(x,y))` | 4.07 | timeout | - | yes |
| since-17 | base | `A(x,y) SINCE[2,5] B(x,y)` | 0.84 | 0.66 | 0.79 | yes |
| since-18 | base | `A(x,y) SINCE[2,100] B(x,y)` | 1.12 | 0.80 | 0.71 | yes |
| since-19 | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.30 | 0.89 | 0.68 | yes |
| since-20 | base | `C(x) SINCE[5,*) A(x,y)` | 0.57 | 0.85 | 1.49 | yes |
| since-21 | base | `C(x) SINCE[100,*) A(x,y)` | 0.59 | 0.86 | 1.46 | yes |
| eventually-01 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.66 | 0.76 | 1.15 | yes |
| eventually-02 | base | `A(x,y) AND EVENTUALLY[0,5] B(x,y)` | 0.78 | 0.92 | 1.17 | yes |
| eventually-03 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 1.04 | 1.27 | 1.23 | yes |
| eventually-04 | base | `A(x,y) AND EVENTUALLY[0,100] B(x,y)` | 1.45 | 1.93 | 1.33 | yes |
| eventually-05 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 1.85 | 3.01 | 1.63 | yes |
| eventually-06 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 0.83 | 0.87 | 1.05 | yes |
| eventually-07 | base | `A(x,y) AND NOT EVENTUALLY[0,5] B(x,y)` | 0.94 | 1.03 | 1.10 | yes |
| eventually-08 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.13 | 1.32 | 1.17 | yes |
| eventually-09 | base | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.49 | 1.96 | 1.31 | yes |
| eventually-10 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 1.93 | 3.00 | 1.56 | yes |
| eventually_raw-01 | base | `EVENTUALLY[0,0] C(x)` | 0.37 | 0.53 | 1.44 | yes |
| eventually_raw-02 | base | `EVENTUALLY[0,1] C(x)` | 0.40 | 0.54 | 1.36 | yes |
| eventually_raw-03 | base | `EVENTUALLY[0,2] C(x)` | 0.42 | 0.56 | 1.33 | yes |
| eventually_raw-04 | base | `EVENTUALLY[0,5] C(x)` | 0.44 | 0.57 | 1.30 | yes |
| eventually_raw-05 | base | `EVENTUALLY[0,10] C(x)` | 0.48 | 0.62 | 1.28 | yes |
| eventually_burst-01 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.10 | 1.11 | 1.01 | yes |
| eventually_burst-02 | burst | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 1.36 | 1.48 | 1.09 | yes |
| eventually_burst-03 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.49 | 1.66 | 1.12 | yes |
| eventually_burst-04 | burst | `A(x,y) AND NOT EVENTUALLY[0,5] B(x,y)` | 1.71 | 1.99 | 1.17 | yes |
| eventually_burst-05 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.96 | 2.40 | 1.22 | yes |
| eventually_burst-06 | burst | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 2.03 | 2.61 | 1.28 | yes |
| eventually_burst-07 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,0] C(y)` | 0.50 | 0.54 | 1.09 | yes |
| eventually_burst-08 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,1] C(y)` | 0.50 | 0.57 | 1.15 | yes |
| eventually_burst-09 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,2] C(y)` | 0.46 | 0.55 | 1.20 | yes |
| eventually_burst-10 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.44 | 0.55 | 1.27 | yes |
| eventually_burst-11 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,10] C(y)` | 0.44 | 0.54 | 1.23 | yes |
| until-01 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.73 | 1.09 | 1.51 | yes |
| until-02 | base | `A(x,y) UNTIL[0,20] B(x,y)` | 0.75 | 1.16 | 1.55 | yes |
| until-03 | base | `A(x,y) UNTIL[0,100] B(x,y)` | 0.77 | 1.17 | 1.51 | yes |
| until-04 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.80 | 1.15 | 1.44 | yes |
| until-05 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.61 | 0.85 | 1.40 | yes |
| until-06 | base | `B(x,y) AND (C(x) UNTIL[0,20] A(x,y))` | 0.64 | 0.98 | 1.53 | yes |
| until-07 | base | `B(x,y) AND (C(x) UNTIL[0,100] A(x,y))` | 0.68 | 0.96 | 1.42 | yes |
| until-08 | base | `B(x,y) AND (C(x) UNTIL[0,500] A(x,y))` | 0.71 | 0.96 | 1.36 | yes |
| until-09 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,5] A(x,y))` | 0.87 | 1.53 | 1.76 | yes |
| until-10 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.06 | 2.06 | 1.93 | yes |
| until-11 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,100] A(x,y))` | 1.24 | 2.83 | 2.28 | yes |
| until_burst-01 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.74 | 0.94 | 1.28 | yes |
| until_burst-02 | burst | `B(x,y) AND (C(x) UNTIL[0,1] A(x,y))` | 0.61 | 0.86 | 1.42 | yes |
| until_burst-03 | burst | `A(x,y) UNTIL[0,2] B(x,y)` | 0.75 | 0.95 | 1.28 | yes |
| until_burst-04 | burst | `B(x,y) AND (C(x) UNTIL[0,2] A(x,y))` | 0.62 | 0.87 | 1.40 | yes |
| until_burst-05 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.74 | 0.95 | 1.28 | yes |
| until_burst-06 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.66 | 0.90 | 1.38 | yes |
| until_burst-07 | burst | `A(x,y) UNTIL[0,10] B(x,y)` | 0.76 | 0.98 | 1.29 | yes |
| until_burst-08 | burst | `B(x,y) AND (C(x) UNTIL[0,10] A(x,y))` | 0.66 | 0.88 | 1.32 | yes |
| nested-01 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.75 | 0.81 | 1.08 | yes |
| nested-02 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,5] C(z))` | 1.00 | 1.06 | 1.06 | yes |
| nested-03 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 1.69 | 1.82 | 1.08 | yes |
| nested-04 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 3.05 | 3.03 | 1.00 | yes |
| nested-05 | rate10 | `A(x,y) AND ONCE[0,100] (B(y,z) AND ONCE[0,20] C(z))` | 0.45 | 0.48 | 1.08 | yes |
| nested-06 | rate10 | `A(x,y) AND ONCE[0,100] (B(y,z) AND ONCE[0,100] C(z))` | 0.92 | 0.99 | 1.08 | yes |
| nested-07 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.21 | 1.33 | 1.10 | yes |
| nested-08 | base | `A(x,y) AND EVENTUALLY[0,5] (B(x,z) AND ONCE[0,5] C(z))` | 0.81 | 0.85 | 1.05 | yes |
| nested-09 | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 1.78 | 1.91 | 1.08 | yes |
| nested-10 | base | `A(x,y) AND EVENTUALLY[0,50] (B(x,z) AND ONCE[0,20] C(z))` | 3.19 | 3.28 | 1.03 | yes |
| nested-11 | base | `A(x,y) AND ONCE[0,5] (B(x,z) AND EVENTUALLY[0,5] C(z))` | 0.90 | 0.89 | 0.98 | yes |
| nested-12 | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 1.89 | 1.97 | 1.05 | yes |
| nested-13 | base | `A(x,y) AND ONCE[0,50] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 3.32 | 3.26 | 0.98 | yes |
| nested-14 | rate10 | `A(x,y) AND EVENTUALLY[0,100] (B(x,z) AND ONCE[0,20] C(z))` | 0.48 | 0.52 | 1.08 | yes |
| nested-15 | rate10 | `A(x,y) AND EVENTUALLY[0,500] (B(x,z) AND ONCE[0,20] C(z))` | 1.29 | 1.49 | 1.15 | yes |
| nested-16 | base | `C(x) AND ((ONCE[0,5] A(x,y)) SINCE[0,5] B(x,y))` | 1.06 | 1.46 | 1.37 | yes |
| nested-17 | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 1.29 | 1.97 | 1.53 | yes |
| nested-18 | base | `C(x) AND ((ONCE[0,100] A(x,y)) SINCE[0,100] B(x,y))` | 2.31 | 4.24 | 1.84 | yes |
| nested-19 | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,5] A(x,y)) AND ONCE[0,5] C(y))` | 0.90 | 1.08 | 1.21 | yes |
| nested-20 | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 0.92 | 1.20 | 1.31 | yes |
| nested-21 | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.83 | 1.53 | 1.85 | yes |
| nested-22 | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.82 | 1.15 | 1.40 | yes |
| nested-23 | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND (EVENTUALLY[0,20] B(x,y))` | 1.38 | 2.00 | 1.45 | yes |
| nested-24 | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 1.47 | 2.14 | 1.45 | yes |
| agg-01 | base | `r <- CNT y; x A(x,y)` | 0.60 | 0.87 | 1.44 | yes |
| agg-02 | base | `r <- SUM y; x A(x,y)` | 0.62 | 0.87 | 1.40 | yes |
| agg-03 | base | `r <- MIN y; x A(x,y)` | 0.62 | 0.87 | 1.41 | yes |
| agg-04 | base | `r <- MAX y; x A(x,y)` | 0.62 | 0.86 | 1.38 | yes |
| agg-05 | base | `r <- AVG y; x A(x,y)` | 0.72 | 1.00 | 1.38 | yes |
| agg-06 | base | `r <- MED y; x A(x,y)` | 0.75 | 1.02 | 1.35 | yes |
| agg-07 | base | `r <- CNT y A(x,y)` | 0.48 | 0.69 | 1.44 | yes |
| agg-08 | base | `r <- SUM y A(x,y)` | 0.50 | 0.69 | 1.40 | yes |
| agg-09 | base | `r <- MAX y A(x,y)` | 0.49 | 0.69 | 1.42 | yes |
| agg-10 | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.61 | 0.75 | 1.23 | yes |
| agg-11 | base | `r <- SUM z; x (A(x,y) AND B(y,z))` | 0.61 | 0.74 | 1.22 | yes |
| agg-12 | base | `r <- MAX z; x (A(x,y) AND B(y,z))` | 0.61 | 0.74 | 1.22 | yes |
| agg_once-01 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.02 | 2.47 | 2.42 | yes |
| agg_once-02 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.35 | 3.65 | 2.71 | yes |
| agg_once-03 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.58 | timeout | - | yes |
| agg_once-04 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.00 | 2.43 | 2.42 | yes |
| agg_once-05 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.36 | 3.62 | 2.66 | yes |
| agg_once-06 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 1.55 | timeout | - | yes |
| agg_once-07 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 0.90 | 2.64 | 2.93 | yes |
| agg_once-08 | base | `r <- MIN y; x ONCE[0,20] A(x,y)` | 1.12 | 3.71 | 3.32 | yes |
| agg_once-09 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.12 | 4.30 | 3.85 | yes |
| agg_once-10 | base | `r <- MAX y; x ONCE[0,5] A(x,y)` | 0.90 | 2.63 | 2.93 | yes |
| agg_once-11 | base | `r <- MAX y; x ONCE[0,20] A(x,y)` | 1.14 | 3.64 | 3.19 | yes |
| agg_once-12 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.12 | 4.41 | 3.92 | yes |
| agg_once-13 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.45 | 3.66 | 2.53 | yes |
| agg_once-14 | base | `r <- AVG y; x ONCE[0,20] A(x,y)` | 1.99 | timeout | - | yes |
| agg_once-15 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.13 | timeout | - | yes |
| agg_once-16 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.56 | 3.38 | 2.16 | yes |
| agg_once-17 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.22 | 4.79 | 2.15 | yes |
| agg_once-18 | base | `r <- MED y; x ONCE[0,50] A(x,y)` | 2.52 | timeout | - | yes |
| agg_once_cnt-01 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.37 | 0.61 | 1.62 | yes |
| agg_once_cnt-02 | base | `r <- CNT x ONCE[0,20] C(x)` | 0.39 | 0.62 | 1.61 | yes |
| agg_once_cnt-03 | base | `r <- CNT x ONCE[0,100] C(x)` | 0.38 | 0.63 | 1.67 | yes |
| agg_once_cnt-04 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.38 | 0.59 | 1.55 | yes |
| agg_once_cnt-05 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.38 | 0.58 | 1.55 | yes |
| agg_once_cnt-06 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.02 | 2.49 | 2.43 | yes |
| agg_once_cnt-07 | base | `r <- CNT y; x ONCE[0,20] A(x,y)` | 1.30 | 3.20 | 2.45 | yes |
| agg_once_cnt-08 | base | `r <- CNT y; x ONCE[0,100] A(x,y)` | 1.40 | 3.85 | 2.75 | yes |
| agg_once_cnt-09 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 1.53 | 4.84 | 3.16 | yes |
| agg_once_cnt-10 | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.61 | 1.05 | 1.73 | yes |
| agg_once_cnt-11 | base | `r <- CNT z; x,y ONCE[0,20] D(x,y,z)` | 1.22 | 2.42 | 1.99 | yes |
| agg_dom-01 | dom50 | `r <- CNT y; x A(x,y)` | 0.58 | 0.82 | 1.42 | yes |
| agg_dom-02 | dom50 | `r <- SUM y; x ONCE[0,5] A(x,y)` | 0.72 | 1.76 | 2.44 | yes |
| agg_dom-03 | dom50 | `r <- CNT x ONCE[0,20] C(x)` | 0.37 | 0.57 | 1.54 | yes |
| agg_dom-04 | base | `r <- CNT y; x A(x,y)` | 0.61 | 0.87 | 1.44 | yes |
| agg_dom-05 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.01 | 2.42 | 2.39 | yes |
| agg_dom-06 | base | `r <- CNT x ONCE[0,20] C(x)` | 0.38 | 0.62 | 1.62 | yes |
| agg_dom-07 | dom1000 | `r <- CNT y; x A(x,y)` | 0.61 | 0.90 | 1.46 | yes |
| agg_dom-08 | dom1000 | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.24 | 2.97 | 2.40 | yes |
| agg_dom-09 | dom1000 | `r <- CNT x ONCE[0,20] C(x)` | 0.38 | 0.66 | 1.74 | yes |
| agg_rate-01 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.59 | 1.21 | 2.06 | yes |
| agg_rate-02 | rate10 | `r <- CNT x ONCE[0,100] C(x)` | 0.16 | 0.26 | 1.60 | yes |
| agg_rate-03 | rate20 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.89 | 2.03 | 2.28 | yes |
| agg_rate-04 | rate20 | `r <- CNT x ONCE[0,100] C(x)` | 0.24 | 0.37 | 1.56 | yes |
| agg_rate-05 | base | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.27 | 3.10 | 2.45 | yes |
| agg_rate-06 | base | `r <- CNT x ONCE[0,100] C(x)` | 0.38 | 0.60 | 1.56 | yes |
| agg_rate-07 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.00 | timeout | - | yes |
| agg_rate-08 | rate80 | `r <- CNT x ONCE[0,100] C(x)` | 0.65 | 1.10 | 1.70 | yes |
| agg_ev-01 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 1.49 | 2.80 | 1.89 | yes |
| agg_ev-02 | base | `r <- SUM y; x EVENTUALLY[0,5] A(x,y)` | 1.49 | 2.75 | 1.85 | yes |
| agg_ev-03 | base | `r <- CNT y; x EVENTUALLY[0,20] A(x,y)` | 2.39 | timeout | - | yes |
| agg_ev-04 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 2.49 | timeout | - | yes |
| agg_guard-01 | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 0.71 | 0.98 | 1.38 | yes |
| agg_guard-02 | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.06 | 3.16 | 2.98 | yes |
| agg_guard-03 | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.42 | 3.52 | 2.48 | yes |
| let-01 | base | `LET P(x) = ONCE[0,5] C(x) IN A(x,y) AND P(x)` | 0.53 | 0.65 | 1.23 | yes |
| let-02 | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,5] Q(y,x)` | 0.42 | 0.54 | 1.28 | yes |
| let-03 | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.61 | 0.68 | 1.13 | yes |
| let-04 | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.41 | 0.54 | 1.30 | yes |
| let-05 | base | `LET P(x) = ONCE[0,500] C(x) IN A(x,y) AND P(x)` | 0.59 | 0.64 | 1.10 | yes |
| let-06 | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,500] Q(y,x)` | 0.41 | 0.53 | 1.29 | yes |
| let-07 | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.53 | 0.67 | 1.26 | yes |
| let-08 | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.55 | 0.71 | 1.29 | yes |
| wide-01 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.46 | 0.63 | 1.37 | yes |
| wide-02 | base | `D(x,y,z) AND ONCE[0,20] D(x,y,z)` | 0.49 | 0.68 | 1.39 | yes |
| wide-03 | base | `D(x,y,z) AND ONCE[0,100] D(x,y,z)` | 0.55 | 0.78 | 1.44 | yes |
| wide-04 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.65 | 0.99 | 1.53 | yes |
| wide-05 | base | `D(x,y,z) AND NOT ONCE[1,5] D(x,y,z)` | 0.48 | 0.59 | 1.23 | yes |
| wide-06 | base | `D(x,y,z) AND NOT ONCE[1,20] D(x,y,z)` | 0.53 | 0.65 | 1.21 | yes |
| wide-07 | base | `D(x,y,z) AND NOT ONCE[1,100] D(x,y,z)` | 0.63 | 0.74 | 1.18 | yes |
| wide-08 | base | `D(x,y,z) AND NOT ONCE[1,500] D(x,y,z)` | 0.73 | 0.91 | 1.25 | yes |
| wide-09 | base | `D(x,y,z) AND EVENTUALLY[0,5] D(x,y,z)` | 0.46 | 0.59 | 1.28 | yes |
| wide-10 | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.48 | 0.65 | 1.35 | yes |
| wide-11 | base | `D(x,y,z) AND EVENTUALLY[0,100] D(x,y,z)` | 0.54 | 0.74 | 1.35 | yes |
| wide-12 | base | `D(x,y,z) AND ONCE[0,5] (A(x,y) AND B(y,z))` | 0.52 | 0.54 | 1.04 | yes |
| wide-13 | base | `A(x,y) AND ONCE[0,5] (EXISTS z. D(x,y,z))` | 0.43 | 0.55 | 1.28 | yes |
| wide-14 | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.57 | 0.64 | 1.12 | yes |
| wide-15 | base | `A(x,y) AND ONCE[0,50] (EXISTS z. D(x,y,z))` | 0.55 | 0.73 | 1.33 | yes |
| wide-16 | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.44 | 0.64 | 1.44 | yes |
| wide-17 | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.42 | 0.67 | 1.59 | yes |
| long-01 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.71 | 0.84 | 1.18 | yes |
| long-02 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.04 | 1.35 | 1.29 | yes |
| long-03 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 1.79 | 2.67 | 1.49 | yes |
| long-04 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 2.13 | 3.12 | 1.46 | yes |
| long-05 | long | `A(x,y) AND NOT ONCE[1,10] A(x,y)` | 1.35 | 1.43 | 1.05 | yes |
| long-06 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 1.77 | 1.86 | 1.05 | yes |
| long-07 | long | `A(x,y) AND NOT ONCE[1,1000] A(x,y)` | 2.53 | 2.74 | 1.08 | yes |
| long-08 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 2.13 | 2.63 | 1.24 | yes |
| long-09 | long | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 1.34 | 1.44 | 1.08 | yes |
| long-10 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 1.72 | 2.06 | 1.20 | yes |
| long-11 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 2.22 | 3.19 | 1.44 | yes |
| long-12 | long | `r <- CNT x ONCE[0,10] C(x)` | 0.77 | 1.27 | 1.65 | yes |
| long-13 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.71 | 1.19 | 1.68 | yes |
| long-14 | long | `r <- CNT x ONCE[0,1000] C(x)` | 0.67 | 1.14 | 1.70 | yes |
| long-15 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.68 | 1.15 | 1.71 | yes |
| long-16 | long | `r <- SUM y; x ONCE[0,10] A(x,y)` | 1.91 | 3.55 | 1.86 | yes |
| long-17 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | 3.94 | timeout | - | yes |
| long-18 | long | `C(x) SINCE[0,10] A(x,y)` | 1.13 | 1.66 | 1.48 | yes |
| long-19 | long | `C(x) SINCE[0,100] A(x,y)` | 1.08 | 1.85 | 1.72 | yes |
| long-20 | long | `C(x) SINCE[0,1000] A(x,y)` | 1.09 | 1.93 | 1.76 | yes |
| policy-01 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.56 | 0.65 | 1.15 | yes |
| policy-02 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.44 | 0.53 | 1.21 | yes |
| policy-03 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.75 | 0.75 | 1.01 | yes |
| policy-04 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.66 | 0.69 | 1.04 | yes |
| policy-05 | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 1.97 | timeout | - | yes |
| policy-06 | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.11 | 1.84 | 1.65 | yes |
| policy-07 | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.69 | 3.39 | 4.93 | yes |
| policy-08 | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.08 | 3.66 | 3.40 | yes |
| policy-09 | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.63 | 0.76 | 1.22 | yes |
| policy-10 | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.23 | 3.73 | 3.04 | yes |
| policy-11 | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.13 | 4.71 | 4.17 | yes |
| policy-12 | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.58 | 0.72 | 1.23 | yes |
