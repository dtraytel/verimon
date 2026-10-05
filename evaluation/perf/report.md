# Performance suite: monpoly vs verimon vs monpoly-verified

285 formulas, 30 families; 3 repetitions (best of), timeout 5 s per run, 2 workers; wall time 1561 s (budget 7200 s).

## verimon against monpoly

| | monpoly | verimon |
|---|---|---|
| ok | 262 | 283 |
| timeout | 2 | 2 |
| refused | 0 | 0 |
| unmonitorable | 21 | 0 |
| error | 0 | 0 |

Over the 262 formulas both finish: geometric mean of verimon/monpoly = **1.03**, median 1.05, 101 where verimon is faster, 100 within 10%, 0 where verimon is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean verimon/monpoly | min | max | monpoly timeouts | verimon timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.83 | 1.29 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.06 | 0.94 | 1.16 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.00 | 0.71 | 1.31 | 0 | 0 | 0 |
| rel | 8 | 8 | 0.97 | 0.74 | 1.26 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.07 | 0.82 | 1.27 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.03 | 0.89 | 1.24 | 0 | 0 | 0 |
| once | 16 | 15 | 1.04 | 0.58 | 1.43 | 1 | 0 | 0 |
| once_exists | 5 | 5 | 0.52 | 0.27 | 0.82 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.17 | 1.05 | 1.38 | 0 | 0 | 0 |
| since | 13 | 13 | 1.00 | 0.48 | 1.48 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.04 | 0.56 | 1.42 | 0 | 0 | 0 |
| until | 6 | 6 | 1.11 | 0.91 | 1.27 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.07 | 0.88 | 1.69 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.10 | 0.90 | 1.34 | 0 | 0 | 0 |
| agg | 8 | 8 | 0.90 | 0.76 | 1.01 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.16 | 0.77 | 1.66 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 0.86 | 0.62 | 1.17 | 0 | 0 | 0 |
| let | 4 | 4 | 1.29 | 1.09 | 1.44 | 0 | 0 | 0 |
| wide | 8 | 8 | 0.96 | 0.79 | 1.21 | 0 | 0 | 0 |
| long | 12 | 11 | 1.03 | 0.79 | 1.73 | 1 | 1 | 0 |
| policy | 10 | 10 | 1.16 | 0.81 | 1.97 | 0 | 0 | 0 |
| match | 11 | 11 | 0.99 | 0.67 | 1.19 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |
| frz | 29 | 29 | 1.05 | 0.04 | 1.81 | 0 | 0 | 0 |
| frz_rw | 8 | 8 | 0.94 | 0.79 | 1.17 | 0 | 0 | 0 |
| past_inf | 5 | 5 | 1.00 | 0.83 | 1.21 | 0 | 0 | 0 |
| derived | 6 | 6 | 1.13 | 0.96 | 1.38 | 0 | 0 | 0 |
| terms | 10 | 10 | 0.99 | 0.74 | 1.12 | 0 | 0 | 0 |
| agg_more | 10 | 10 | 0.98 | 0.56 | 1.30 | 0 | 0 | 0 |
| vm_only | 16 | 0 | - | - | - | 0 | 1 | 0 |

### Where verimon is slowest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.48 | 2.90 | 1.97 |
| frz-neglag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.16 | 0.29 | 1.81 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 2.31 | 4.00 | 1.73 |
| frz-agg | tp500 | `FRZ q(x) = C(x) IN (r <- CNT y; x ONCE[0,10] (A(x,y) AND q(x)))` | 0.09 | 0.15 | 1.70 |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.76 | 2.97 | 1.69 |
| frz-sincelag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.15 | 0.25 | 1.68 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.42 | 2.36 | 1.66 |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 1.24 | 2.05 | 1.65 |
| frz-once100 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,100] (A(x,y) AND q(x))` | 0.29 | 0.47 | 1.63 |
| frz-onceinf | tp500 | `FRZ q(x) = C(x) IN ONCE[0,*) (A(x,y) AND q(x))` | 0.75 | 1.22 | 1.62 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.46 | 2.33 | 1.59 |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.67 | 2.65 | 1.58 |
| frz-len1000 | tp1000 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.19 | 0.30 | 1.58 |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 2.08 | 3.07 | 1.48 |
| frz-len250 | tp250 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.05 | 0.08 | 1.48 |

### Where verimon is fastest relative to monpoly

| name | log | formula | monpoly s | verimon s | ratio |
|---|---|---|---|---|---|
| frz-nested | tp250 | `FRZ q(x) = C(x) IN FRZ r(y) = C(y) IN ONCE[0,10] (A(x,y) AND q(x) AND r(y))` | 1.49 | 0.07 | 0.04 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.58 | 0.70 | 0.27 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 2.56 | 1.05 | 0.41 |
| frz-untillb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[2,10] (A(x,y) AND q(x)))` | 0.13 | 0.06 | 0.44 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.96 | 0.95 | 0.48 |
| agg-exists | base | `r <- CNT x (EXISTS y. ONCE[0,10] A(x,y))` | 1.39 | 0.78 | 0.56 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.61 | 0.91 | 0.56 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 3.11 | 1.80 | 0.58 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.55 | 0.91 | 0.58 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 3.06 | 1.90 | 0.62 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | verimon |
|---|---|---|---|---|
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | timeout | 3.68 s |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | timeout | timeout |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 1.52 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.43 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 2.02 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.41 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.98 s |
| trig-plain | base | `A(x,y) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.59 s |
| trig-neg | base | `(NOT A(x,y)) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.97 s |
| trig-inf | base | `C(x) TRIGGER[0,*) (EXISTS y. B(x,y))` | unmonitorable | 0.89 s |
| rel-plain | base | `A(x,y) RELEASE[0,5] B(x,y)` | unmonitorable | 0.69 s |
| rel-neg | base | `(NOT A(x,y)) RELEASE[0,5] B(x,y)` | unmonitorable | 1.28 s |
| lp-reach | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,*) r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.57 s |
| lp-reach5 | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.59 s |
| lp-once | base | `LETPAST r(x) = C(x) OR (EXISTS y. ONCE[1,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.79 s |
| lp-count | base | `LETPAST r(x) = C(x) OR PREV[0,*) (r(x) AND NOT (EXISTS y. B(x,y))) IN r(x)` | unmonitorable | 0.60 s |
| lp-chain | tp1000 | `LETPAST r(x,y) = A(x,y) OR (PREV[0,1] r(x,y) AND NOT B(x,y)) IN r(x,y)` | unmonitorable | timeout |
| der-hist5 | dom50 | `HISTORICALLY[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.64 s |
| der-hist20 | dom50 | `HISTORICALLY[0,20] C(x)` | unmonitorable | 0.28 s |
| der-always5 | dom50 | `ALWAYS[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.66 s |
| der-equiv | base | `A(x,y) AND (C(x) EQUIV C(y))` | unmonitorable | 0.80 s |
| vm-frztrig | base | `C(x) AND (NOT B(x,x) TRIGGER[0,5] C(x))` | unmonitorable | 0.50 s |
| vm-frzrel | base | `C(x) AND (NOT B(x,x) RELEASE[0,5] C(x))` | unmonitorable | 0.60 s |

## monpoly-verified against monpoly

| | monpoly | monpoly-verified |
|---|---|---|
| ok | 262 | 284 |
| timeout | 2 | 1 |
| refused | 0 | 0 |
| unmonitorable | 21 | 0 |
| error | 0 | 0 |

Over the 261 formulas both finish: geometric mean of monpoly-verified/monpoly = **1.05**, median 1.06, 89 where monpoly-verified is faster, 93 within 10%, 2 where monpoly-verified is more than 2x slower, 0 more than 4x slower.

Verdict disagreements: none

### By family

| family | n | both ok | geomean monpoly-verified/monpoly | min | max | monpoly timeouts | monpoly-verified timeouts | refused |
|---|---|---|---|---|---|---|---|---|
| join | 9 | 9 | 1.13 | 0.89 | 1.32 | 0 | 0 | 0 |
| join_scale | 5 | 5 | 1.05 | 0.86 | 1.19 | 0 | 0 | 0 |
| andnot | 8 | 8 | 1.00 | 0.64 | 1.15 | 0 | 0 | 0 |
| rel | 8 | 8 | 1.03 | 0.80 | 1.38 | 0 | 0 | 0 |
| or_exists | 6 | 6 | 1.13 | 0.90 | 1.49 | 0 | 0 | 0 |
| prevnext | 8 | 8 | 1.05 | 0.92 | 1.29 | 0 | 0 | 0 |
| once | 16 | 15 | 1.03 | 0.55 | 1.42 | 1 | 0 | 0 |
| once_exists | 5 | 5 | 0.53 | 0.27 | 0.91 | 0 | 0 | 0 |
| once_scale | 4 | 4 | 1.20 | 1.09 | 1.35 | 0 | 0 | 0 |
| since | 13 | 13 | 1.05 | 0.45 | 1.40 | 0 | 0 | 0 |
| eventually | 8 | 8 | 1.08 | 0.58 | 1.43 | 0 | 0 | 0 |
| until | 6 | 6 | 1.22 | 1.05 | 1.41 | 0 | 0 | 0 |
| burst | 9 | 9 | 1.08 | 0.87 | 1.62 | 0 | 0 | 0 |
| nested | 11 | 11 | 1.10 | 0.88 | 1.58 | 0 | 0 | 0 |
| agg | 8 | 8 | 0.90 | 0.76 | 1.05 | 0 | 0 | 0 |
| agg_once | 22 | 22 | 1.16 | 0.80 | 1.77 | 0 | 0 | 0 |
| agg_fut | 5 | 5 | 0.81 | 0.56 | 1.26 | 0 | 0 | 0 |
| let | 4 | 4 | 1.35 | 1.03 | 1.63 | 0 | 0 | 0 |
| wide | 8 | 8 | 0.94 | 0.77 | 1.16 | 0 | 0 | 0 |
| long | 12 | 11 | 1.03 | 0.75 | 1.47 | 1 | 0 | 0 |
| policy | 10 | 10 | 1.17 | 0.75 | 2.06 | 0 | 0 | 0 |
| match | 11 | 11 | 1.03 | 0.63 | 1.30 | 0 | 0 | 0 |
| andtrigger | 5 | 0 | - | - | - | 0 | 0 | 0 |
| frz | 29 | 29 | 1.09 | 0.04 | 2.10 | 0 | 0 | 0 |
| frz_rw | 8 | 8 | 0.98 | 0.68 | 1.16 | 0 | 0 | 0 |
| past_inf | 5 | 5 | 1.03 | 0.78 | 1.27 | 0 | 0 | 0 |
| derived | 6 | 6 | 1.12 | 0.89 | 1.41 | 0 | 0 | 0 |
| terms | 10 | 10 | 0.98 | 0.81 | 1.27 | 0 | 0 | 0 |
| agg_more | 10 | 9 | 1.01 | 0.71 | 1.29 | 0 | 1 | 0 |
| vm_only | 16 | 0 | - | - | - | 0 | 0 | 0 |

### Where monpoly-verified is slowest relative to monpoly

| name | log | formula | monpoly s | monpoly-verified s | ratio |
|---|---|---|---|---|---|
| frz-once5 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,5] (A(x,y) AND q(x))` | 0.07 | 0.14 | 2.10 |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.48 | 3.05 | 2.06 |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.42 | 2.52 | 1.77 |
| frz-len1000 | tp1000 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.19 | 0.33 | 1.76 |
| frz-oncelb | tp500 | `FRZ q(x) = C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.09 | 0.15 | 1.73 |
| frz-sincelag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.15 | 0.26 | 1.72 |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.46 | 2.52 | 1.72 |
| frz-neglag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.16 | 0.27 | 1.69 |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.58 | 0.95 | 1.63 |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.76 | 2.86 | 1.62 |
| frz-agg | tp500 | `FRZ q(x) = C(x) IN (r <- CNT y; x ONCE[0,10] (A(x,y) AND q(x)))` | 0.09 | 0.15 | 1.61 |
| frz-ev5 | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[0,5] (A(x,y) AND q(x))` | 0.08 | 0.12 | 1.61 |
| frz-neglag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.11 | 0.17 | 1.59 |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.91 | 1.44 | 1.58 |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.67 | 2.54 | 1.52 |

### Where monpoly-verified is fastest relative to monpoly

| name | log | formula | monpoly s | monpoly-verified s | ratio |
|---|---|---|---|---|---|
| frz-nested | tp250 | `FRZ q(x) = C(x) IN FRZ r(y) = C(y) IN ONCE[0,10] (A(x,y) AND q(x) AND r(y))` | 1.49 | 0.06 | 0.04 |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.58 | 0.69 | 0.27 |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 2.56 | 1.05 | 0.41 |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.96 | 0.88 | 0.45 |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 3.11 | 1.72 | 0.55 |
| frz-untillb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[2,10] (A(x,y) AND q(x)))` | 0.13 | 0.07 | 0.55 |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 3.06 | 1.73 | 0.56 |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.61 | 0.93 | 0.58 |
| frz-until | tp250 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[0,5] (A(x,y) AND q(x)))` | 0.09 | 0.05 | 0.58 |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.55 | 0.91 | 0.59 |

### Timeouts, refusals and errors

| name | log | formula | monpoly | monpoly-verified |
|---|---|---|---|---|
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | timeout | 3.44 s |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | timeout | 3.55 s |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 1.42 s |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.34 s |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 1.98 s |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.24 s |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 1.10 s |
| agg-medonce | base | `r <- MED y; x ONCE[0,50] A(x,y)` | 3.70 s | timeout |
| trig-plain | base | `A(x,y) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.58 s |
| trig-neg | base | `(NOT A(x,y)) TRIGGER[0,5] B(x,y)` | unmonitorable | 1.00 s |
| trig-inf | base | `C(x) TRIGGER[0,*) (EXISTS y. B(x,y))` | unmonitorable | 0.84 s |
| rel-plain | base | `A(x,y) RELEASE[0,5] B(x,y)` | unmonitorable | 0.82 s |
| rel-neg | base | `(NOT A(x,y)) RELEASE[0,5] B(x,y)` | unmonitorable | 1.32 s |
| lp-reach | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,*) r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.69 s |
| lp-reach5 | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.50 s |
| lp-once | base | `LETPAST r(x) = C(x) OR (EXISTS y. ONCE[1,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.68 s |
| lp-count | base | `LETPAST r(x) = C(x) OR PREV[0,*) (r(x) AND NOT (EXISTS y. B(x,y))) IN r(x)` | unmonitorable | 0.65 s |
| lp-chain | tp1000 | `LETPAST r(x,y) = A(x,y) OR (PREV[0,1] r(x,y) AND NOT B(x,y)) IN r(x,y)` | unmonitorable | 3.20 s |
| der-hist5 | dom50 | `HISTORICALLY[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.64 s |
| der-hist20 | dom50 | `HISTORICALLY[0,20] C(x)` | unmonitorable | 0.25 s |
| der-always5 | dom50 | `ALWAYS[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.68 s |
| der-equiv | base | `A(x,y) AND (C(x) EQUIV C(y))` | unmonitorable | 0.66 s |
| vm-frztrig | base | `C(x) AND (NOT B(x,x) TRIGGER[0,5] C(x))` | unmonitorable | 0.54 s |
| vm-frzrel | base | `C(x) AND (NOT B(x,x) RELEASE[0,5] C(x))` | unmonitorable | 0.61 s |

## All formulas

| name | log | formula | monpoly s | verimon s | monpoly-verified s | ratio | agree | why |
|---|---|---|---|---|---|---|---|---|
| join-both | base | `A(x,y) AND B(x,y)` | 0.53 | 0.68 | 0.53 | 1.28 | yes | equi-join on both columns: a set intersection |
| join-one | base | `A(x,y) AND B(y,z)` | 0.65 | 0.83 | 0.80 | 1.29 | yes | one shared column, the common case |
| join-swap | base | `A(x,y) AND B(y,x)` | 0.46 | 0.55 | 0.59 | 1.19 | yes | both columns shared, permuted: the index must reorder |
| join-first | base | `A(x,y) AND B(z,x)` | 0.69 | 0.76 | 0.87 | 1.12 | yes | shared column in different positions |
| join-chain3 | base | `A(x,y) AND B(y,z) AND C(z)` | 0.65 | 0.69 | 0.86 | 1.06 | yes | a chain closed by a unary filter |
| join-chain4 | base | `A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)` | 0.72 | 0.75 | 0.74 | 1.04 | yes | four-way chain: the multi-way join |
| join-ternary | base | `A(x,y) AND D(y,z,w)` | 0.55 | 0.67 | 0.67 | 1.22 | yes | binary with ternary |
| join-self3 | base | `D(x,y,z) AND D(z,y,x)` | 0.37 | 0.31 | 0.33 | 0.83 | yes | ternary self-join, all columns permuted |
| join-star | base | `A(x,y) AND B(x,y) AND C(x) AND C(y)` | 0.51 | 0.63 | 0.50 | 1.23 | yes | intersection with unary filters on both columns |
| join-rate10 | rate10 | `A(x,y) AND B(y,z)` | 0.21 | 0.24 | 0.23 | 1.16 | yes | 10 events per predicate per time point |
| join-rate40 | base | `A(x,y) AND B(y,z)` | 0.73 | 0.77 | 0.78 | 1.06 | yes | 40 (the base log) |
| join-rate80 | rate80 | `A(x,y) AND B(y,z)` | 1.59 | 1.50 | 1.36 | 0.94 | yes | 80: result size grows with the square of the rate |
| join-dom50 | dom50 | `A(x,y) AND B(y,z)` | 0.66 | 0.67 | 0.70 | 1.02 | yes | small domain: many matches per key |
| join-dom1000 | dom1000 | `A(x,y) AND B(y,z)` | 0.57 | 0.66 | 0.68 | 1.16 | yes | large domain: few matches, more distinct keys |
| andnot-both | base | `A(x,y) AND NOT B(x,y)` | 0.68 | 0.71 | 0.73 | 1.03 | yes | difference on both columns |
| andnot-one | base | `A(x,y) AND NOT C(x)` | 0.75 | 0.65 | 0.79 | 0.87 | yes | anti-join on one column |
| andnot-swap | base | `A(x,y) AND NOT B(y,x)` | 0.85 | 1.11 | 0.91 | 1.31 | yes | permuted |
| andnot-exists | base | `A(x,y) AND NOT (EXISTS z. B(x,z))` | 0.74 | 0.86 | 0.75 | 1.16 | yes | projection, then anti-join |
| andnot-wide | base | `D(x,y,z) AND NOT A(x,y)` | 0.85 | 0.60 | 0.54 | 0.71 | yes | ternary minus binary |
| andnot-chain | base | `A(x,y) AND B(y,z) AND NOT A(z,x)` | 0.77 | 0.75 | 0.78 | 0.98 | yes | anti-join after a join |
| andnot-dom50 | dom50 | `A(x,y) AND NOT B(x,y)` | 0.76 | 0.84 | 0.88 | 1.10 | yes | small domain: most tuples are removed |
| andnot-dom1000 | dom1000 | `A(x,y) AND NOT B(x,y)` | 0.67 | 0.66 | 0.74 | 0.99 | yes | large domain: almost nothing is removed |
| rel-lt | base | `A(x,y) AND x < y` | 0.49 | 0.55 | 0.50 | 1.12 | yes | a filter that keeps half |
| rel-eq | base | `A(x,y) AND x = y` | 0.37 | 0.47 | 0.49 | 1.26 | yes | a filter that keeps almost nothing |
| rel-const | base | `A(x,y) AND x < 20` | 0.59 | 0.44 | 0.47 | 0.74 | yes | constant bound |
| rel-notlt | base | `A(x,y) AND NOT x < y` | 0.52 | 0.46 | 0.52 | 0.90 | yes | negated constraint |
| rel-assign | base | `A(x,y) AND z = x + y` | 0.60 | 0.54 | 0.66 | 0.91 | yes | an assignment adds a column |
| rel-assign2 | base | `A(x,y) AND B(y,z) AND w = x + z` | 0.62 | 0.68 | 0.85 | 1.09 | yes | assignment after a join |
| rel-joinlt | base | `A(x,y) AND B(y,z) AND x < z` | 0.81 | 0.82 | 0.68 | 1.02 | yes | constraint across a join |
| rel-two | base | `A(x,y) AND x < y AND y < 100` | 0.64 | 0.51 | 0.60 | 0.81 | yes | two constraints |
| or-plain | base | `A(x,y) OR B(x,y)` | 0.83 | 0.68 | 0.74 | 0.82 | yes | union |
| or-filtered | base | `(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)` | 0.62 | 0.69 | 0.76 | 1.13 | yes | union of filtered operands |
| exists-one | base | `EXISTS y. A(x,y)` | 0.61 | 0.61 | 0.56 | 1.01 | yes | projection |
| exists-join | base | `(EXISTS x. A(x,y)) AND B(y,z)` | 0.62 | 0.66 | 0.73 | 1.07 | yes | projection feeding a join |
| exists-guard | base | `C(x) AND (EXISTS y. A(x,y) AND B(y,x))` | 0.50 | 0.63 | 0.59 | 1.27 | yes | quantifier over a join, guarded |
| exists-wide | base | `(EXISTS z. D(x,y,z)) AND NOT A(x,y)` | 0.52 | 0.60 | 0.77 | 1.17 | yes | projection of a ternary, then anti-join |
| prev-unary | base | `PREV[0,1] C(x)` | 0.38 | 0.37 | 0.39 | 0.98 | yes | one time point back |
| next-unary | base | `NEXT[0,1] C(x)` | 0.42 | 0.41 | 0.42 | 0.98 | yes | one time point ahead: a one-step buffer |
| prev-join | base | `A(x,y) AND PREV[0,1] B(x,y)` | 0.57 | 0.60 | 0.52 | 1.04 | yes | joined with the previous table |
| next-join | base | `A(x,y) AND NEXT[0,1] B(x,y)` | 0.45 | 0.55 | 0.58 | 1.24 | yes | joined with the next table |
| prev-first | base | `A(x,y) AND NOT PREV[0,1] A(x,y)` | 0.69 | 0.61 | 0.65 | 0.89 | yes | tuples new since the previous time point |
| prev-join3 | base | `A(x,y) AND PREV[0,1] (B(x,z) AND C(z))` | 0.61 | 0.56 | 0.64 | 0.92 | yes | Prev of a join |
| prev-burst | burst | `A(x,y) AND PREV[0,0] B(x,y)` | 0.49 | 0.53 | 0.50 | 1.06 | yes | previous time point with the same timestamp |
| next-burst | burst | `A(x,y) AND NEXT[0,0] B(x,y)` | 0.45 | 0.54 | 0.53 | 1.20 | yes | next time point with the same timestamp |
| once-raw0 | base | `ONCE[0,0] C(x)` | 0.43 | 0.43 | 0.44 | 1.01 | yes | the current time point only |
| once-raw5 | base | `ONCE[0,5] C(x)` | 0.73 | 0.58 | 0.57 | 0.79 | yes | unguarded, small predicate: the verdict is the window |
| once-raw20 | base | `ONCE[0,20] C(x)` | 0.62 | 0.54 | 0.59 | 0.87 | yes | window of 200 tuples, at most 200 distinct |
| once-g1 | base | `A(x,y) AND ONCE[0,1] B(x,y)` | 0.90 | 0.82 | 0.79 | 0.91 | yes | guarded: the window is probed, not printed |
| once-g5 | base | `A(x,y) AND ONCE[0,5] B(x,y)` | 0.88 | 0.91 | 1.04 | 1.03 | yes | 240 tuples in the window |
| once-g50 | base | `A(x,y) AND ONCE[0,50] B(x,y)` | 1.35 | 1.79 | 1.75 | 1.32 | yes | 2000 |
| once-g500 | base | `A(x,y) AND ONCE[0,500] B(x,y)` | 2.49 | 3.53 | 3.49 | 1.42 | yes | 20000: half of the 40000 possible tuples |
| once-g2000 | base | `A(x,y) AND ONCE[0,2000] B(x,y)` | 2.75 | 3.31 | 3.13 | 1.20 | yes | the window saturates: every tuple has been seen |
| once-first5 | base | `A(x,y) AND NOT ONCE[1,5] A(x,y)` | 1.22 | 1.13 | 1.07 | 0.93 | yes | first occurrence within the window |
| once-first50 | base | `A(x,y) AND NOT ONCE[1,50] A(x,y)` | 1.97 | 1.99 | 1.95 | 1.01 | yes |  |
| once-first500 | base | `A(x,y) AND NOT ONCE[1,500] A(x,y)` | timeout | 3.68 | 3.44 | - | yes |  |
| once-lb5 | base | `C(x) AND ONCE[5,25] A(x,y)` | 2.11 | 1.93 | 1.79 | 0.92 | yes | positive lower bound: entries wait before they count |
| once-lb500 | base | `C(x) AND ONCE[500,520] A(x,y)` | 3.11 | 1.80 | 1.72 | 0.58 | yes | a long wait, a short window |
| once-inf | base | `A(x,y) AND ONCE[0,*) B(x,y)` | 1.75 | 2.34 | 2.48 | 1.34 | yes | unbounded: the window only grows |
| once-infnot | base | `A(x,y) AND NOT ONCE[1,*) A(x,y)` | 1.47 | 2.10 | 1.93 | 1.43 | yes | first occurrence ever |
| once-half | base | `A(x,y) AND ONCE[0,50) B(x,y)` | 1.61 | 1.96 | 2.11 | 1.21 | yes | half-open interval |
| onceex-5 | base | `C(x) AND (EXISTS y. ONCE[0,5] A(x,y))` | 1.23 | 1.01 | 1.12 | 0.82 | yes | the window is projected before the guard applies |
| onceex-20 | base | `C(x) AND (EXISTS y. ONCE[0,20] A(x,y))` | 1.55 | 0.91 | 0.91 | 0.58 | yes |  |
| onceex-50 | base | `C(x) AND (EXISTS y. ONCE[0,50] A(x,y))` | 2.56 | 1.05 | 1.05 | 0.41 | yes |  |
| onceex-not5 | base | `C(x) AND NOT (EXISTS y. ONCE[1,5] A(x,y))` | 1.24 | 0.86 | 0.90 | 0.69 | yes | negated |
| onceex-not50 | base | `C(x) AND NOT (EXISTS y. ONCE[1,50] A(x,y))` | 2.58 | 0.70 | 0.69 | 0.27 | yes |  |
| once-rate10 | rate10 | `A(x,y) AND ONCE[0,20] B(x,y)` | 0.21 | 0.23 | 0.23 | 1.09 | yes | 200 tuples in the window |
| once-rate80 | rate80 | `A(x,y) AND ONCE[0,20] B(x,y)` | 2.48 | 3.41 | 3.36 | 1.38 | yes | 1600 |
| once-dom50 | dom50 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.25 | 1.31 | 1.42 | 1.05 | yes | 2500 possible tuples: the window nearly saturates |
| once-dom1000 | dom1000 | `A(x,y) AND ONCE[0,20] B(x,y)` | 1.11 | 1.34 | 1.37 | 1.21 | yes | a million possible: every tuple new |
| since-bb5 | base | `A(x,y) SINCE[0,5] B(x,y)` | 0.94 | 0.81 | 1.03 | 0.86 | yes | both binary: the left operand must hold at every time point |
| since-bb50 | base | `A(x,y) SINCE[0,50] B(x,y)` | 1.17 | 1.00 | 1.17 | 0.86 | yes |  |
| since-bb500 | base | `A(x,y) SINCE[0,500] B(x,y)` | 1.08 | 1.13 | 1.09 | 1.04 | yes |  |
| since-u5 | base | `B(x,y) AND (C(x) SINCE[0,5] A(x,y))` | 0.82 | 1.21 | 0.83 | 1.48 | yes | unary left operand |
| since-u50 | base | `B(x,y) AND (C(x) SINCE[0,50] A(x,y))` | 1.01 | 0.94 | 1.06 | 0.93 | yes |  |
| since-u500 | base | `B(x,y) AND (C(x) SINCE[0,500] A(x,y))` | 0.85 | 0.89 | 1.09 | 1.04 | yes |  |
| since-nu5 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,5] A(x,y))` | 1.16 | 1.24 | 1.44 | 1.07 | yes | negated unary left operand |
| since-nu50 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,50] A(x,y))` | 1.28 | 1.66 | 1.80 | 1.30 | yes |  |
| since-nu500 | base | `B(x,y) AND ((NOT C(x)) SINCE[0,500] A(x,y))` | 1.62 | 1.99 | 1.97 | 1.23 | yes |  |
| since-nb5 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,5] A(x,y))` | 1.39 | 1.60 | 1.60 | 1.15 | yes | negated binary left operand |
| since-nb20 | base | `C(x) AND ((NOT B(x,y)) SINCE[0,20] A(x,y))` | 2.40 | 2.30 | 2.22 | 0.96 | yes |  |
| since-lb | base | `A(x,y) SINCE[2,500] B(x,y)` | 1.96 | 0.95 | 0.88 | 0.48 | yes | positive lower bound |
| since-inf | base | `C(x) SINCE[5,*) A(x,y)` | 0.70 | 0.74 | 0.87 | 1.05 | yes | unbounded |
| ev-g1 | base | `A(x,y) AND EVENTUALLY[0,1] B(x,y)` | 0.76 | 0.87 | 0.95 | 1.14 | yes | one time point of delay |
| ev-g20 | base | `A(x,y) AND EVENTUALLY[0,20] B(x,y)` | 1.63 | 1.52 | 1.88 | 0.93 | yes | verdicts delayed by 20 time points |
| ev-g500 | base | `A(x,y) AND EVENTUALLY[0,500] B(x,y)` | 3.14 | 4.32 | 4.22 | 1.38 | yes | 500 time points buffered |
| ev-n1 | base | `A(x,y) AND NOT EVENTUALLY[0,1] B(x,y)` | 1.07 | 1.16 | 1.05 | 1.09 | yes | negated (the P2 shape) |
| ev-n20 | base | `A(x,y) AND NOT EVENTUALLY[0,20] B(x,y)` | 1.65 | 1.89 | 1.83 | 1.15 | yes |  |
| ev-n500 | base | `A(x,y) AND NOT EVENTUALLY[0,500] B(x,y)` | 2.87 | 4.08 | 4.10 | 1.42 | yes |  |
| ev-raw5 | base | `EVENTUALLY[0,5] C(x)` | 0.53 | 0.51 | 0.57 | 0.96 | yes | unguarded, small predicate |
| ev-exists20 | base | `C(x) AND (EXISTS y. EVENTUALLY[0,20] A(x,y))` | 1.61 | 0.91 | 0.93 | 0.56 | yes | quantifier over the future window |
| until-bb5 | base | `A(x,y) UNTIL[0,5] B(x,y)` | 0.92 | 0.83 | 1.09 | 0.91 | yes | both binary |
| until-bb50 | base | `A(x,y) UNTIL[0,50] B(x,y)` | 1.21 | 1.16 | 1.27 | 0.96 | yes |  |
| until-bb500 | base | `A(x,y) UNTIL[0,500] B(x,y)` | 0.91 | 1.08 | 1.11 | 1.19 | yes |  |
| until-u5 | base | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.73 | 0.88 | 1.03 | 1.21 | yes | unary left operand |
| until-u50 | base | `B(x,y) AND (C(x) UNTIL[0,50] A(x,y))` | 0.88 | 1.12 | 1.07 | 1.27 | yes |  |
| until-nu20 | base | `B(x,y) AND ((NOT C(x)) UNTIL[0,20] A(x,y))` | 1.47 | 1.76 | 1.82 | 1.19 | yes | negated unary left operand |
| burst-n0 | burst | `A(x,y) AND NOT EVENTUALLY[0,0] B(x,y)` | 1.40 | 1.22 | 1.31 | 0.88 | yes | the same timestamp only: 60 time points |
| burst-n2 | burst | `A(x,y) AND NOT EVENTUALLY[0,2] B(x,y)` | 1.79 | 2.10 | 1.86 | 1.17 | yes | 180 |
| burst-n10 | burst | `A(x,y) AND NOT EVENTUALLY[0,10] B(x,y)` | 3.17 | 3.12 | 3.18 | 0.98 | yes | 660 time points buffered under the conjunction |
| burst-p2 | burst | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,5] C(y)` | 0.52 | 0.54 | 0.58 | 1.04 | yes | the P2 policy shape |
| burst-u1 | burst | `A(x,y) UNTIL[0,1] B(x,y)` | 0.85 | 0.77 | 0.85 | 0.90 | yes | Until over 120 time points |
| burst-u5 | burst | `A(x,y) UNTIL[0,5] B(x,y)` | 0.92 | 0.85 | 0.81 | 0.92 | yes |  |
| burst-uu5 | burst | `B(x,y) AND (C(x) UNTIL[0,5] A(x,y))` | 0.78 | 0.97 | 0.94 | 1.24 | yes | unary left operand |
| burst-once5 | burst | `A(x,y) AND ONCE[0,5] B(x,y)` | 1.76 | 2.97 | 2.86 | 1.69 | yes | the past on the same log, for comparison |
| burst-p3 | burst | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.80 | 0.80 | 0.85 | 0.99 | yes | the P3 policy shape |
| nest-oo5 | base | `A(x,y) AND ONCE[0,5] (B(y,z) AND ONCE[0,5] C(z))` | 0.82 | 0.98 | 0.96 | 1.20 | yes | a window over a window |
| nest-oo20 | base | `A(x,y) AND ONCE[0,20] (B(y,z) AND ONCE[0,20] C(z))` | 2.16 | 2.28 | 2.21 | 1.06 | yes |  |
| nest-oo50 | base | `A(x,y) AND ONCE[0,50] (B(y,z) AND ONCE[0,20] C(z))` | 3.59 | 3.92 | 3.99 | 1.09 | yes |  |
| nest-oo500 | rate10 | `A(x,y) AND ONCE[0,500] (B(y,z) AND ONCE[0,20] C(z))` | 1.55 | 1.70 | 1.65 | 1.10 | yes | a long outer window, on the thin log |
| nest-eo | base | `A(x,y) AND EVENTUALLY[0,20] (B(x,z) AND ONCE[0,20] C(z))` | 2.52 | 2.26 | 2.53 | 0.90 | yes | future over past |
| nest-oe | base | `A(x,y) AND ONCE[0,20] (B(x,z) AND EVENTUALLY[0,20] C(z))` | 2.46 | 2.39 | 2.51 | 0.97 | yes | past over future |
| nest-so | base | `C(x) AND ((ONCE[0,20] A(x,y)) SINCE[0,20] B(x,y))` | 2.02 | 2.07 | 2.02 | 1.03 | yes | a window as the left operand of Since |
| nest-notso | base | `A(x,y) AND NOT ((B(x,y) SINCE[0,20] A(x,y)) AND ONCE[0,20] C(y))` | 1.40 | 1.49 | 1.24 | 1.06 | yes | negated Since |
| nest-notsince | base | `A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))` | 0.91 | 1.05 | 1.04 | 1.15 | yes | anti-join with a Since |
| nest-notuntil | base | `A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))` | 0.91 | 1.15 | 1.44 | 1.27 | yes | anti-join with an Until |
| nest-pastfut | base | `A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))` | 2.02 | 2.70 | 2.44 | 1.34 | yes | last occurrence: past and future together |
| agg-cnt | base | `r <- CNT y; x A(x,y)` | 0.85 | 0.65 | 0.65 | 0.76 | yes | grouped count, about 200 groups |
| agg-sum | base | `r <- SUM y; x A(x,y)` | 0.69 | 0.67 | 0.68 | 0.97 | yes |  |
| agg-min | base | `r <- MIN y; x A(x,y)` | 0.72 | 0.71 | 0.64 | 0.99 | yes |  |
| agg-max | base | `r <- MAX y; x A(x,y)` | 0.84 | 0.75 | 0.70 | 0.89 | yes |  |
| agg-avg | base | `r <- AVG y; x A(x,y)` | 1.02 | 0.95 | 0.84 | 0.93 | yes |  |
| agg-med | base | `r <- MED y; x A(x,y)` | 0.93 | 0.93 | 0.96 | 1.01 | yes | the median needs the whole group |
| agg-nogroup | base | `r <- CNT y A(x,y)` | 0.61 | 0.52 | 0.55 | 0.85 | yes | one group |
| agg-join | base | `r <- CNT z; x (A(x,y) AND B(y,z))` | 0.83 | 0.69 | 0.88 | 0.83 | yes | aggregation of a join |
| aggonce-cnt5 | base | `r <- CNT y; x ONCE[0,5] A(x,y)` | 1.43 | 1.52 | 1.45 | 1.06 | yes | grouped count of the window |
| aggonce-cnt50 | base | `r <- CNT y; x ONCE[0,50] A(x,y)` | 1.89 | 1.92 | 1.78 | 1.01 | yes |  |
| aggonce-cnt500 | base | `r <- CNT y; x ONCE[0,500] A(x,y)` | 2.08 | 3.07 | 2.84 | 1.48 | yes |  |
| aggonce-sum5 | base | `r <- SUM y; x ONCE[0,5] A(x,y)` | 1.29 | 1.31 | 1.44 | 1.01 | yes |  |
| aggonce-sum50 | base | `r <- SUM y; x ONCE[0,50] A(x,y)` | 1.74 | 1.97 | 1.60 | 1.14 | yes |  |
| aggonce-sum500 | base | `r <- SUM y; x ONCE[0,500] A(x,y)` | 2.23 | 2.99 | 3.37 | 1.34 | yes |  |
| aggonce-min5 | base | `r <- MIN y; x ONCE[0,5] A(x,y)` | 1.24 | 2.05 | 1.80 | 1.65 | yes | the extremum leaves with its tuple: an order per group |
| aggonce-min50 | base | `r <- MIN y; x ONCE[0,50] A(x,y)` | 1.46 | 2.33 | 2.52 | 1.59 | yes |  |
| aggonce-max50 | base | `r <- MAX y; x ONCE[0,50] A(x,y)` | 1.42 | 2.36 | 2.52 | 1.66 | yes |  |
| aggonce-avg5 | base | `r <- AVG y; x ONCE[0,5] A(x,y)` | 1.91 | 2.40 | 2.46 | 1.26 | yes |  |
| aggonce-avg50 | base | `r <- AVG y; x ONCE[0,50] A(x,y)` | 2.89 | 3.50 | 3.78 | 1.21 | yes |  |
| aggonce-med5 | base | `r <- MED y; x ONCE[0,5] A(x,y)` | 1.67 | 2.65 | 2.54 | 1.58 | yes |  |
| aggonce-med20 | base | `r <- MED y; x ONCE[0,20] A(x,y)` | 2.72 | 3.90 | 3.90 | 1.43 | yes |  |
| aggonce-c5 | base | `r <- CNT x ONCE[0,5] C(x)` | 0.53 | 0.44 | 0.48 | 0.82 | yes | closed left operand, no group: the fused window |
| aggonce-c50 | base | `r <- CNT x ONCE[0,50] C(x)` | 0.44 | 0.44 | 0.46 | 1.01 | yes |  |
| aggonce-c500 | base | `r <- CNT x ONCE[0,500] C(x)` | 0.52 | 0.53 | 0.51 | 1.02 | yes |  |
| aggonce-c2000 | base | `r <- CNT x ONCE[0,2000] C(x)` | 0.44 | 0.52 | 0.58 | 1.18 | yes |  |
| aggonce-wide | base | `r <- CNT z; x,y ONCE[0,5] D(x,y,z)` | 0.82 | 0.64 | 0.67 | 0.77 | yes | two group columns over a ternary window |
| aggonce-rate10 | rate10 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 0.83 | 0.68 | 0.68 | 0.82 | yes | the same sum as the rate and the domain grow |
| aggonce-rate80 | rate80 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 2.92 | 3.13 | 3.07 | 1.07 | yes |  |
| aggonce-dom50 | dom50 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 1.11 | 1.17 | 1.23 | 1.05 | yes | 50 groups, many tuples each |
| aggonce-dom1000 | dom1000 | `r <- SUM y; x ONCE[0,20] A(x,y)` | 3.64 | 3.50 | 2.91 | 0.96 | yes | up to 840 groups of one or two tuples |
| aggev-cnt5 | base | `r <- CNT y; x EVENTUALLY[0,5] A(x,y)` | 2.12 | 1.46 | 1.32 | 0.69 | yes | the window completes late |
| aggev-sum20 | base | `r <- SUM y; x EVENTUALLY[0,20] A(x,y)` | 3.06 | 1.90 | 1.73 | 0.62 | yes |  |
| aggguard-cnt | base | `A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3` | 1.00 | 0.93 | 0.77 | 0.93 | yes | aggregate joined and filtered |
| aggguard-sum | base | `C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500` | 1.26 | 1.48 | 1.59 | 1.17 | yes | aggregate of a window, guarded |
| aggguard-not | base | `(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)` | 1.93 | 2.01 | 2.04 | 1.04 | yes | aggregate of a window, anti-joined |
| let-once | base | `LET P(x) = ONCE[0,50] C(x) IN A(x,y) AND P(x)` | 0.63 | 0.69 | 0.65 | 1.09 | yes | a window bound once, used as a predicate |
| let-twice | base | `LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,50] Q(y,x)` | 0.49 | 0.71 | 0.71 | 1.44 | yes | one definition used twice, permuted |
| let-neg | base | `LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)` | 0.64 | 0.87 | 0.87 | 1.36 | yes | a negated definition |
| let-nested | base | `LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)` | 0.58 | 0.76 | 0.95 | 1.31 | yes | two levels |
| wide-once5 | base | `D(x,y,z) AND ONCE[0,5] D(x,y,z)` | 0.54 | 0.61 | 0.57 | 1.13 | yes | three-column tuples in the window |
| wide-once50 | base | `D(x,y,z) AND ONCE[0,50] D(x,y,z)` | 0.78 | 0.61 | 0.68 | 0.79 | yes |  |
| wide-once500 | base | `D(x,y,z) AND ONCE[0,500] D(x,y,z)` | 0.82 | 0.97 | 0.87 | 1.17 | yes |  |
| wide-first | base | `D(x,y,z) AND NOT ONCE[1,50] D(x,y,z)` | 0.74 | 0.59 | 0.57 | 0.80 | yes | first occurrence of a ternary tuple |
| wide-ev | base | `D(x,y,z) AND EVENTUALLY[0,20] D(x,y,z)` | 0.57 | 0.49 | 0.47 | 0.85 | yes |  |
| wide-since | base | `D(x,y,z) SINCE[0,20] D(z,y,x)` | 0.52 | 0.47 | 0.52 | 0.90 | yes | Since with permuted ternary operands |
| wide-until | base | `D(x,y,z) UNTIL[0,20] D(z,y,x)` | 0.54 | 0.49 | 0.49 | 0.90 | yes |  |
| wide-oncejoin | base | `D(x,y,z) AND ONCE[0,50] (A(x,y) AND B(y,z))` | 0.63 | 0.76 | 0.73 | 1.21 | yes | a join inside the window |
| long-g10 | long | `A(x,y) AND ONCE[0,10] B(x,y)` | 0.87 | 0.87 | 1.03 | 1.01 | yes | 88 tuples in the window |
| long-g100 | long | `A(x,y) AND ONCE[0,100] B(x,y)` | 1.48 | 1.82 | 1.53 | 1.23 | yes | 808 |
| long-g1000 | long | `A(x,y) AND ONCE[0,1000] B(x,y)` | 2.31 | 4.00 | 3.40 | 1.73 | yes | 8008 |
| long-g10000 | long | `A(x,y) AND ONCE[0,10000] B(x,y)` | 3.42 | 3.54 | 3.75 | 1.03 | yes | 80008: twice the 40000 possible tuples |
| long-first100 | long | `A(x,y) AND NOT ONCE[1,100] A(x,y)` | 2.39 | 1.90 | 1.78 | 0.79 | yes |  |
| long-first10000 | long | `A(x,y) AND NOT ONCE[1,10000] A(x,y)` | 3.03 | 2.76 | 2.94 | 0.91 | yes |  |
| long-ev100 | long | `A(x,y) AND NOT EVENTUALLY[0,100] B(x,y)` | 2.31 | 1.96 | 2.03 | 0.85 | yes | 100 time points buffered |
| long-ev1000 | long | `A(x,y) AND NOT EVENTUALLY[0,1000] B(x,y)` | 3.30 | 4.32 | 3.96 | 1.31 | yes | 1000 |
| long-since100 | long | `C(x) SINCE[0,100] A(x,y)` | 1.31 | 1.07 | 1.27 | 0.82 | yes |  |
| long-cnt100 | long | `r <- CNT x ONCE[0,100] C(x)` | 0.89 | 0.91 | 0.83 | 1.02 | yes | the fused count over 400 tuples |
| long-cnt10000 | long | `r <- CNT x ONCE[0,10000] C(x)` | 0.89 | 0.86 | 0.88 | 0.96 | yes | over 40000 |
| long-sum100 | long | `r <- SUM y; x ONCE[0,100] A(x,y)` | timeout | timeout | 3.55 | - | yes | grouped sum over 800 tuples |
| pol-p2 | base | `(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)` | 0.63 | 0.60 | 0.64 | 0.94 | yes | P2: no report within six seconds |
| pol-p3 | base | `A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))` | 0.85 | 0.91 | 0.85 | 1.08 | yes | P3: no earlier authorisation |
| pol-unmatched | base | `C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))` | 2.47 | 2.01 | 1.86 | 0.81 | yes | an A without a matching B in the window |
| pol-chain | base | `A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))` | 1.25 | 1.24 | 1.18 | 0.99 | yes | a nested chain of conditions |
| pol-threshold | base | `(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r` | 0.78 | 1.10 | 1.17 | 1.41 | yes | a count over a window against a threshold |
| pol-sumfilter | base | `(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r` | 1.24 | 1.37 | 1.37 | 1.11 | yes | a sum over a window, anti-joined and thresholded |
| pol-repeat | base | `A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))` | 0.80 | 1.00 | 0.89 | 1.25 | yes | first occurrence of a joined pair |
| pol-sincefut | base | `A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)` | 1.81 | 2.42 | 2.50 | 1.34 | yes | past and future conditions together |
| pol-sincefutb | burst | `A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)` | 1.48 | 2.90 | 3.05 | 1.97 | yes | the same on the bursty log |
| pol-let | base | `LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)` | 0.68 | 0.74 | 0.83 | 1.09 | yes | a Let-bound condition used positively and negatively |
| match-p1 | base | `A(x,y) AND MATCHP[0,10] B(x,y)?` | 0.53 | 0.56 | 0.61 | 1.06 | yes | a one-test past regex, guarded |
| match-p50 | base | `A(x,y) AND MATCHP[0,50] B(x,y)?` | 0.59 | 0.64 | 0.59 | 1.09 | yes | the same over a longer window |
| match-palt | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? + B(x,y)?)` | 0.83 | 0.73 | 0.76 | 0.89 | yes | a choice: two tables per step |
| match-pseq | base | `A(x,y) AND MATCHP[0,10] (A(x,y)? . B(x,y)?)` | 0.53 | 0.56 | 0.60 | 1.05 | yes | a concatenation: the derivative walks two states |
| match-pstar | base | `A(x,y) AND MATCHP[0,10] (B(x,y)? . (A(x,y)? . B(x,y)?)*)` | 0.79 | 0.66 | 0.75 | 0.83 | yes | a star: the derivative set grows |
| match-f1 | base | `A(x,y) AND MATCHF[0,10] B(x,y)?` | 0.57 | 0.60 | 0.59 | 1.05 | yes | the future twin, which buffers the window |
| match-falt | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? + B(x,y)?)` | 0.77 | 0.91 | 0.83 | 1.19 | yes | a choice in the future |
| match-fseq | base | `A(x,y) AND MATCHF[0,10] (A(x,y)? . B(x,y)?)` | 0.58 | 0.56 | 0.69 | 0.97 | yes | a concatenation in the future |
| match-fburst | burst | `A(x,y) AND MATCHF[0,3] B(x,y)?` | 0.91 | 1.07 | 1.18 | 1.18 | yes | the future regex on the bursty log |
| match-pnarrow | base | `C(x) AND MATCHP[0,20] (EXISTS y. A(x,y))?` | 0.57 | 0.63 | 0.65 | 1.11 | yes | the operand is narrower than the node's frame |
| match-pcnt | base | `r <- CNT x MATCHP[0,20] C(x)?` | 0.66 | 0.44 | 0.42 | 0.67 | yes | an aggregate over a past regex |
| atrig-5 | base | `A(x,y) AND (A(x,y) TRIGGER[1,5] B(x,y))` | unmonitorable | 1.52 | 1.42 | - | yes | a short window, the trigger at the conjunct's frame |
| atrig-50 | base | `A(x,y) AND (A(x,y) TRIGGER[1,50] B(x,y))` | unmonitorable | 1.43 | 1.34 | - | yes | a longer window |
| atrig-lb | base | `A(x,y) AND (A(x,y) TRIGGER[5,20] B(x,y))` | unmonitorable | 2.02 | 1.98 | - | yes | a positive lower bound: the window starts empty |
| atrig-inf | base | `A(x,y) AND (A(x,y) TRIGGER[1,*) B(x,y))` | unmonitorable | 1.41 | 1.24 | - | yes | unbounded |
| atrig-narrow | base | `A(x,y) AND (C(x) TRIGGER[1,10] (EXISTS y. B(x,y)))` | unmonitorable | 0.98 | 1.10 | - | yes | the trigger narrower than the conjunct |
| frz-now | tp500 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.05 | 0.05 | 0.06 | 1.13 | yes | no temporal operator under the freeze: the cost of FRZ itself |
| frz-once5 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,5] (A(x,y) AND q(x))` | 0.07 | 0.09 | 0.14 | 1.36 | yes | a past window over the frozen predicate |
| frz-once20 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.14 | 0.15 | 0.15 | 1.08 | yes | a wider one |
| frz-once100 | tp500 | `FRZ q(x) = C(x) IN ONCE[0,100] (A(x,y) AND q(x))` | 0.29 | 0.47 | 0.43 | 1.63 | yes | wider still |
| frz-onceinf | tp500 | `FRZ q(x) = C(x) IN ONCE[0,*) (A(x,y) AND q(x))` | 0.75 | 1.22 | 0.96 | 1.62 | yes | the unbounded past |
| frz-oncelb | tp500 | `FRZ q(x) = C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.09 | 0.13 | 0.15 | 1.43 | yes | a window that misses the current time point |
| frz-prev | tp500 | `FRZ q(x) = C(x) IN PREV[0,5] (A(x,y) AND q(x))` | 0.06 | 0.05 | 0.06 | 0.83 | yes | the previous time point |
| frz-sincelb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[2,10] (A(x,y) AND q(x)))` | 0.09 | 0.09 | 0.08 | 0.99 | yes | a Since whose interval misses the current time point |
| frz-evlb | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[2,10] (A(x,y) AND q(x))` | 0.08 | 0.11 | 0.10 | 1.34 | yes | the future dual of frz-oncelb |
| frz-untillb | tp500 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[2,10] (A(x,y) AND q(x)))` | 0.13 | 0.06 | 0.07 | 0.44 | yes | and of frz-sincelb |
| frz-lagphi | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[2,10] (A(x,y) AND q(x))` | 0.14 | 0.14 | 0.13 | 0.97 | yes | a frozen formula that lags: the window is replayed |
| frz-neglag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.16 | 0.29 | 0.27 | 1.81 | yes | it lags, and the frozen predicate is negated: nothing to hoist |
| frz-sincelag | tp500 | `FRZ q(x) = EVENTUALLY[0,3] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.15 | 0.25 | 0.26 | 1.68 | yes | it lags, and the frozen predicate is the left operand of a Since |
| frz-neglag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN ONCE[0,5] (A(x,y) AND NOT q(x))` | 0.11 | 0.14 | 0.17 | 1.35 | yes | frz-neglag with a lag of 30 time points: many pending verdicts |
| frz-sincelag30 | tp500 | `FRZ q(x) = EVENTUALLY[0,30] C(x) IN (q(x) SINCE[0,4] A(x,y))` | 0.20 | 0.28 | 0.28 | 1.37 | yes | and frz-sincelag |
| frz-next | tp500 | `FRZ q(x) = C(x) IN NEXT[0,5] (A(x,y) AND q(x))` | 0.07 | 0.06 | 0.07 | 0.98 | yes | the next time point |
| frz-ev5 | tp500 | `FRZ q(x) = C(x) IN EVENTUALLY[0,5] (A(x,y) AND q(x))` | 0.08 | 0.09 | 0.12 | 1.21 | yes | a future window |
| frz-since | tp500 | `FRZ q(x) = C(x) IN (B(x,y) SINCE[0,10] (A(x,y) AND q(x)))` | 0.11 | 0.10 | 0.10 | 0.97 | yes | the frozen predicate in Since's right operand |
| frz-until | tp250 | `FRZ q(x) = C(x) IN (B(x,y) UNTIL[0,5] (A(x,y) AND q(x)))` | 0.09 | 0.06 | 0.05 | 0.74 | yes | and in Until's |
| frz-tbody | tp250 | `FRZ q(x) = ONCE[0,10] C(x) IN ONCE[0,10] (A(x,y) AND q(x))` | 0.09 | 0.09 | 0.09 | 0.96 | yes | a temporal formula frozen |
| frz-nested | tp250 | `FRZ q(x) = C(x) IN FRZ r(y) = C(y) IN ONCE[0,10] (A(x,y) AND q(x) AND r(y))` | 1.49 | 0.07 | 0.06 | 0.04 | yes | two freezes, nested |
| frz-binary | tp500 | `FRZ q(x,y) = B(x,y) IN ONCE[0,10] (A(x,y) AND q(x,y))` | 0.08 | 0.10 | 0.12 | 1.21 | yes | a binary frozen predicate |
| frz-agg | tp500 | `FRZ q(x) = C(x) IN (r <- CNT y; x ONCE[0,10] (A(x,y) AND q(x)))` | 0.09 | 0.15 | 0.15 | 1.70 | yes | an aggregation over the frozen window |
| frz-exists | tp500 | `FRZ q(x) = C(x) IN EXISTS y. ONCE[0,10] (A(x,y) AND q(x))` | 0.08 | 0.08 | 0.09 | 0.91 | yes | a projection over it |
| frz-outer | tp500 | `C(x) AND (FRZ q(x) = C(x) IN ONCE[0,10] (EXISTS y. A(x,y) AND q(x)))` | 0.08 | 0.09 | 0.09 | 1.18 | yes | the freeze under a conjunction |
| frz-len250 | tp250 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.05 | 0.08 | 0.08 | 1.48 | yes | frz-once20 on 250 time points |
| frz-len1000 | tp1000 | `FRZ q(x) = C(x) IN ONCE[0,20] (A(x,y) AND q(x))` | 0.19 | 0.30 | 0.33 | 1.58 | yes | and on 1000 |
| frz-now250 | tp250 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.03 | 0.03 | 0.03 | 1.02 | yes | frz-now on 250 time points |
| frz-now1000 | tp1000 | `FRZ q(x) = C(x) IN (A(x,y) AND q(x))` | 0.09 | 0.11 | 0.09 | 1.26 | yes | and on 1000 |
| frzrw-once | base | `C(x) AND ONCE[0,5] NOT B(x,x)` | 0.88 | 0.75 | 0.89 | 0.85 | yes | the guard frozen into a past window |
| frzrw-once20 | base | `C(x) AND ONCE[0,20] NOT B(x,x)` | 1.08 | 1.20 | 1.26 | 1.11 | yes | a wider one |
| frzrw-oncelb | base | `C(x) AND ONCE[2,10] NOT B(x,x)` | 1.33 | 1.05 | 0.90 | 0.79 | yes | a window that misses the current time point |
| frzrw-once2 | base | `A(x,y) AND ONCE[0,5] NOT B(x,y)` | 2.43 | 2.01 | 2.13 | 0.82 | yes | a binary guard |
| frzrw-sincer | base | `C(x) AND (C(x) SINCE[0,5] NOT B(x,x))` | 0.89 | 0.84 | 1.02 | 0.94 | yes | into Since's right operand |
| frzrw-sincelb | base | `C(x) AND ((EXISTS y. A(x,y)) SINCE[1,5] NOT B(x,x))` | 1.55 | 1.58 | 1.65 | 1.02 | yes | and with an interval that misses the current time point |
| frzrw-ev | base | `C(x) AND EVENTUALLY[0,5] NOT B(x,x)` | 0.80 | 0.69 | 0.73 | 0.87 | yes | into a future window |
| frzrw-untilr | base | `C(x) AND (C(x) UNTIL[0,5] NOT B(x,x))` | 0.83 | 0.97 | 0.94 | 1.17 | yes | into Until's right operand |
| inf-since | base | `A(x,y) SINCE[0,*) B(x,y)` | 0.81 | 0.96 | 0.98 | 1.18 | yes | unbounded Since |
| inf-sincelb | base | `A(x,y) SINCE[5,*) B(x,y)` | 0.76 | 0.66 | 0.65 | 0.87 | yes | with a lower bound |
| inf-negsince | base | `(NOT C(x)) SINCE[0,*) A(x,y)` | 3.09 | 2.58 | 2.41 | 0.83 | yes | with a negated left operand |
| inf-prev | base | `A(x,y) AND PREV[1,*) B(x,y)` | 0.49 | 0.49 | 0.55 | 0.99 | yes | Prev with an unbounded interval |
| inf-agg | base | `r <- CNT y; x ONCE[0,*) A(x,y)` | 1.85 | 2.23 | 2.36 | 1.21 | yes | an aggregation over the whole past |
| der-implies | base | `A(x,y) AND (C(x) IMPLIES B(x,y))` | 0.65 | 0.82 | 0.75 | 1.25 | yes | an implication under a guard |
| der-forall | base | `C(x) AND FORALL y. (A(x,y) IMPLIES y < 150)` | 0.59 | 0.68 | 0.63 | 1.16 | yes | a universal quantifier: an anti-join with a filter |
| der-true | base | `A(x,y) AND TRUE` | 0.62 | 0.59 | 0.55 | 0.96 | yes | a trivially true conjunct |
| der-false | base | `A(x,y) OR (FALSE AND B(x,y))` | 0.62 | 0.68 | 0.66 | 1.09 | yes | a trivially false disjunct |
| der-guardhist | base | `C(x) AND HISTORICALLY[0,5] (EXISTS y. A(x,y) OR B(x,y))` | 0.92 | 0.94 | 1.09 | 1.01 | yes | a guarded past Always |
| der-guardalw | base | `C(x) AND ALWAYS[0,5] (EXISTS y. A(x,y) OR B(x,y))` | 0.81 | 1.12 | 1.14 | 1.38 | yes | a guarded future Always |
| term-mul | base | `A(x,y) AND z = x * y` | 0.55 | 0.59 | 0.62 | 1.08 | yes | multiplication |
| term-mod | base | `A(x,y) AND z = x MOD 7` | 0.56 | 0.56 | 0.50 | 1.01 | yes | remainder |
| term-div | base | `A(x,y) AND z = x / 3` | 0.57 | 0.54 | 0.52 | 0.94 | yes | division |
| term-neg | base | `A(x,y) AND z = -x` | 0.56 | 0.52 | 0.52 | 0.93 | yes | negation |
| term-i2f | base | `A(x,y) AND z = i2f(x)` | 0.71 | 0.78 | 0.69 | 1.09 | yes | to a float |
| term-f2i | base | `A(x,y) AND z = f2i(i2f(x) + 0.5)` | 0.76 | 0.56 | 0.62 | 0.74 | yes | float arithmetic and back |
| term-modfilt | base | `A(x,y) AND x MOD 10 = 0` | 0.54 | 0.58 | 0.51 | 1.08 | yes | a constraint over a term |
| term-chain | base | `A(x,y) AND z = x + y AND w = z * 2 AND w < 300` | 0.55 | 0.62 | 0.70 | 1.12 | yes | assignments feeding assignments and a filter |
| term-tp | base | `A(x,y) AND tp(i)` | 0.71 | 0.63 | 0.67 | 0.88 | yes | the time point as a column |
| term-ts | base | `A(x,y) AND ts(t) AND t MOD 10 = 0` | 0.45 | 0.49 | 0.50 | 1.09 | yes | the timestamp as a column, filtered |
| agg-avgonce | base | `r <- AVG y; x ONCE[0,20] A(x,y)` | 2.64 | 3.42 | 3.18 | 1.30 | yes | AVG over a past window |
| agg-medonce | base | `r <- MED y; x ONCE[0,50] A(x,y)` | 3.70 | 4.23 | timeout | 1.14 | yes | MED over a wide one |
| agg-since | base | `r <- CNT y; x (B(x,y) SINCE[0,10] A(x,y))` | 1.23 | 1.38 | 1.27 | 1.12 | yes | over a Since |
| agg-until | base | `r <- SUM y; x (B(x,y) UNTIL[0,5] A(x,y))` | 1.26 | 1.26 | 1.40 | 1.00 | yes | over an Until |
| agg-avgev | base | `r <- AVG y; x EVENTUALLY[0,20] A(x,y)` | 4.36 | 3.44 | 3.63 | 0.79 | yes | AVG over a future window |
| agg-minev | base | `r <- MIN y; x EVENTUALLY[0,20] A(x,y)` | 3.53 | 2.40 | 2.51 | 0.68 | yes | MIN over a future window |
| agg-nested | base | `s <- MAX r (r <- CNT y; x ONCE[0,10] A(x,y))` | 1.26 | 1.60 | 1.61 | 1.27 | yes | an aggregation of an aggregation |
| agg-exists | base | `r <- CNT x (EXISTS y. ONCE[0,10] A(x,y))` | 1.39 | 0.78 | 1.01 | 0.56 | yes | over a projected window |
| agg-empty | base | `r <- CNT y ONCE[0,5] (A(x,y) AND x < 0)` | 0.44 | 0.44 | 0.50 | 1.01 | yes | over an always empty table: the default value |
| agg-float | base | `r <- SUM z; x (A(x,y) AND z = i2f(y))` | 0.91 | 1.14 | 1.18 | 1.24 | yes | a sum of floats |
| trig-plain | base | `A(x,y) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.59 | 0.58 | - | yes | Trigger |
| trig-neg | base | `(NOT A(x,y)) TRIGGER[0,5] B(x,y)` | unmonitorable | 0.97 | 1.00 | - | yes | with a negated left operand |
| trig-inf | base | `C(x) TRIGGER[0,*) (EXISTS y. B(x,y))` | unmonitorable | 0.89 | 0.84 | - | yes | over the unbounded past |
| rel-plain | base | `A(x,y) RELEASE[0,5] B(x,y)` | unmonitorable | 0.69 | 0.82 | - | yes | Release |
| rel-neg | base | `(NOT A(x,y)) RELEASE[0,5] B(x,y)` | unmonitorable | 1.28 | 1.32 | - | yes | with a negated left operand |
| lp-reach | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,*) r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.57 | 0.69 | - | yes | recursion through the past: reachability along A |
| lp-reach5 | base | `LETPAST r(x) = C(x) OR (EXISTS y. PREV[0,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.59 | 0.50 | - | yes | with a bounded step |
| lp-once | base | `LETPAST r(x) = C(x) OR (EXISTS y. ONCE[1,5] r(y) AND A(y,x)) IN r(x)` | unmonitorable | 0.79 | 0.68 | - | yes | through a window |
| lp-count | base | `LETPAST r(x) = C(x) OR PREV[0,*) (r(x) AND NOT (EXISTS y. B(x,y))) IN r(x)` | unmonitorable | 0.60 | 0.65 | - | yes | a state kept until B resets it |
| lp-chain | tp1000 | `LETPAST r(x,y) = A(x,y) OR (PREV[0,1] r(x,y) AND NOT B(x,y)) IN r(x,y)` | unmonitorable | timeout | 3.20 | - | yes | a binary state; on a short log, its cost grows faster than the log |
| der-hist5 | dom50 | `HISTORICALLY[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.64 | 0.64 | - | yes | unguarded past Always |
| der-hist20 | dom50 | `HISTORICALLY[0,20] C(x)` | unmonitorable | 0.28 | 0.25 | - | yes | over a wider window |
| der-always5 | dom50 | `ALWAYS[0,5] (EXISTS y. A(x,y))` | unmonitorable | 0.66 | 0.68 | - | yes | unguarded future Always |
| der-equiv | base | `A(x,y) AND (C(x) EQUIV C(y))` | unmonitorable | 0.80 | 0.66 | - | yes | an equivalence |
| vm-frztrig | base | `C(x) AND (NOT B(x,x) TRIGGER[0,5] C(x))` | unmonitorable | 0.50 | 0.54 | - | yes | the rewriter's freeze into a trigger |
| vm-frzrel | base | `C(x) AND (NOT B(x,x) RELEASE[0,5] C(x))` | unmonitorable | 0.60 | 0.61 | - | yes | and into a release |
