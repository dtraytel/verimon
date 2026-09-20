#!/usr/bin/env python3
"""The formulas of the performance suite, by family (see README.md).

Each family is a shape with a parameter sweep: an interval bound, a number of joined
predicates, an aggregation operator, or the log it runs on (rate, domain, burstiness).  Reading
a family's rows in order shows a trend; reading the same row across families shows what an
operator costs relative to another.

Wide temporal subformulas are guarded (`A(x,y) AND ONCE[0,b] B(x,y)`, `A(x,y) AND NOT
ONCE[1,b] A(x,y)`) so that a formula's verdict stays a few tuples per time point: the runtimes
are the operators', not the printer's.  Unguarded ones use the small predicate C.

usage: gen_formulas.py [OUTDIR]   (default: formulas/)  -- writes <family>-<k>.mfotl and suite.json
"""
import json, os, sys

suite = []


def add(family, log, formula, **params):
    k = sum(1 for e in suite if e["family"] == family) + 1
    suite.append({"name": "%s-%02d" % (family, k), "family": family, "log": log,
                  "formula": formula, "params": params})


# ---- joins: how many predicates, which variables shared ------------------------------------
JOINS = [
    ("A(x,y) AND B(x,y)", "2 preds, 2 shared"),
    ("A(x,y) AND B(y,z)", "2 preds, 1 shared"),
    ("A(x,y) AND B(y,x)", "2 preds, swapped"),
    ("A(x,y) AND B(z,x)", "2 preds, 1 shared, first column"),
    ("A(x,y) AND B(y,z) AND C(z)", "3 preds, chain"),
    ("A(x,y) AND B(y,z) AND C(x)", "3 preds, chain + unary"),
    ("A(x,y) AND B(y,z) AND A(z,w)", "3 preds, chain, self-join"),
    ("A(x,y) AND B(y,z) AND A(z,w) AND B(w,v)", "4 preds, chain"),
    ("A(x,y) AND D(y,z,w)", "binary with ternary"),
    ("D(x,y,z) AND D(z,y,x)", "ternary self-join, permuted"),
    ("D(x,y,z) AND A(x,y) AND B(y,z)", "ternary with two binaries"),
    ("A(x,y) AND B(x,y) AND C(x) AND C(y)", "4 preds, star"),
]
for f, d in JOINS:
    add("join", "base", f, shape=d)
for log in ["rate10", "rate20", "base", "rate80"]:
    add("join_rate", log, "A(x,y) AND B(y,z)", shape="2 preds, 1 shared")
    add("join_rate", log, "A(x,y) AND B(y,z) AND C(z)", shape="3 preds, chain")
for log in ["dom50", "base", "dom1000"]:
    add("join_dom", log, "A(x,y) AND B(y,z)", shape="2 preds, 1 shared")
    add("join_dom", log, "A(x,y) AND B(x,y)", shape="2 preds, 2 shared")
    add("join_dom", log, "A(x,y) AND B(y,z) AND C(z)", shape="3 preds, chain")

# ---- negation and relational constraints -----------------------------------------------------
for f in ["A(x,y) AND NOT B(x,y)", "A(x,y) AND NOT C(x)", "A(x,y) AND NOT C(y)",
          "A(x,y) AND NOT B(y,x)", "A(x,y) AND NOT (EXISTS z. B(x,z))",
          "D(x,y,z) AND NOT A(x,y)", "A(x,y) AND B(y,z) AND NOT C(z)",
          "A(x,y) AND B(y,z) AND NOT A(z,x)"]:
    add("andnot", "base", f)
for log in ["dom50", "base", "dom1000"]:
    add("andnot_dom", log, "A(x,y) AND NOT B(x,y)")
    add("andnot_dom", log, "A(x,y) AND NOT C(x)")
for f in ["A(x,y) AND x < y", "A(x,y) AND x < 20", "A(x,y) AND x = y", "A(x,y) AND NOT x < y",
          "A(x,y) AND z = x + y", "A(x,y) AND z = 2 * x", "A(x,y) AND z = x - y",
          "A(x,y) AND B(y,z) AND x < z", "A(x,y) AND B(y,z) AND w = x + z",
          "A(x,y) AND x < y AND y < 100"]:
    add("rel", "base", f)
for f in ["A(x,y) OR B(x,y)", "(A(x,y) AND x < 100) OR (B(x,y) AND y < 100)",
          "A(x,y) OR B(y,x)", "(A(x,y) AND NOT C(x)) OR (B(x,y) AND NOT C(y))"]:
    add("or", "base", f)
for f in ["EXISTS y. A(x,y)", "(EXISTS x. A(x,y)) AND B(y,z)", "EXISTS x. EXISTS y. A(x,y) AND B(y,z)",
          "C(x) AND (EXISTS y. A(x,y) AND B(y,x))", "EXISTS z. D(x,y,z)",
          "(EXISTS z. D(x,y,z)) AND NOT A(x,y)"]:
    add("exists", "base", f)

# ---- Prev and Next ----------------------------------------------------------------------------
for f in ["PREV[0,1] C(x)", "NEXT[0,1] C(x)", "A(x,y) AND PREV[0,1] B(x,y)", "A(x,y) AND NEXT[0,1] B(x,y)",
          "A(x,y) AND PREV[0,1] (B(x,z) AND C(z))", "PREV[0,1] PREV[0,1] C(x)",
          "A(x,y) AND NOT PREV[0,1] A(x,y)", "A(x,y) AND NOT NEXT[0,1] A(x,y)"]:
    add("prevnext", "base", f)
for f in ["A(x,y) AND PREV[0,0] B(x,y)", "A(x,y) AND NEXT[0,0] B(x,y)", "A(x,y) AND PREV[1,1] B(x,y)"]:
    add("prevnext", "burst", f)

# ---- Once, and the window sweeps -----------------------------------------------------------
for b in [0, 1, 2, 5, 10, 20]:
    add("once_raw", "base", "ONCE[0,%d] C(x)" % b, b=b)
for b in [1, 5, 20, 50, 100, 200, 500, 1000, 2000]:
    add("once_guard", "base", "A(x,y) AND ONCE[0,%d] B(x,y)" % b, b=b)
for b in [5, 20, 50, 100, 500, 2000]:
    add("once_first", "base", "A(x,y) AND NOT ONCE[1,%d] A(x,y)" % b, b=b)
for a in [1, 5, 20, 100, 500]:
    add("once_lb", "base", "C(x) AND ONCE[%d,%d] A(x,y)" % (a, a + 20), a=a)
for f in ["A(x,y) AND ONCE[0,*) B(x,y)", "A(x,y) AND NOT ONCE[1,*) A(x,y)"]:
    add("once_inf", "base", f)
for f in ["C(x) AND ONCE[10,*) B(x,y)", "C(x) AND NOT ONCE[10,*) B(x,y)"]:
    add("once_inf", "rate10", f)
for b in [5, 20, 50]:
    add("once_exists", "base", "C(x) AND (EXISTS y. ONCE[0,%d] A(x,y))" % b, b=b)
    add("once_exists", "base", "C(x) AND NOT (EXISTS y. ONCE[1,%d] A(x,y))" % b, b=b)
for log in ["rate10", "rate20", "base", "rate80"]:
    add("once_rate", log, "A(x,y) AND ONCE[0,20] B(x,y)")
    add("once_rate", log, "A(x,y) AND NOT ONCE[1,100] A(x,y)")
for log in ["dom50", "base", "dom1000"]:
    add("once_dom", log, "A(x,y) AND ONCE[0,20] B(x,y)")
    add("once_dom", log, "A(x,y) AND NOT ONCE[1,100] A(x,y)")
    add("once_dom", log, "ONCE[0,5] C(x)")

# ---- Since ---------------------------------------------------------------------------------
for b in [5, 20, 100, 500, 2000]:
    add("since", "base", "A(x,y) SINCE[0,%d] B(x,y)" % b, b=b, shape="both binary")
for b in [5, 20, 100, 500]:
    add("since", "base", "B(x,y) AND (C(x) SINCE[0,%d] A(x,y))" % b, b=b, shape="unary left")
for b in [5, 20, 100, 500]:
    add("since", "base", "B(x,y) AND ((NOT C(x)) SINCE[0,%d] A(x,y))" % b, b=b, shape="negated unary left")
for b in [5, 20, 100]:
    add("since", "base", "C(x) AND ((NOT B(x,y)) SINCE[0,%d] A(x,y))" % b, b=b, shape="negated binary left")
for b in [5, 100, 500]:
    add("since", "base", "A(x,y) SINCE[2,%d] B(x,y)" % b, b=b, shape="positive lower bound")
for b in [5, 100]:
    add("since", "base", "C(x) SINCE[%d,*) A(x,y)" % b, b=b, shape="unbounded")

# ---- Eventually and Until: bounded futures, on the one-per-second log and on the bursty one ----
for b in [1, 5, 20, 100, 500]:
    add("eventually", "base", "A(x,y) AND EVENTUALLY[0,%d] B(x,y)" % b, b=b)
for b in [1, 5, 20, 100, 500]:
    add("eventually", "base", "A(x,y) AND NOT EVENTUALLY[0,%d] B(x,y)" % b, b=b)
for b in [0, 1, 2, 5, 10]:
    add("eventually_raw", "base", "EVENTUALLY[0,%d] C(x)" % b, b=b)
for b in [0, 1, 2, 5, 10, 20]:
    add("eventually_burst", "burst", "A(x,y) AND NOT EVENTUALLY[0,%d] B(x,y)" % b, b=b)
for b in [0, 1, 2, 5, 10]:
    add("eventually_burst", "burst", "(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,%d] C(y)" % b, b=b)
for b in [5, 20, 100, 500]:
    add("until", "base", "A(x,y) UNTIL[0,%d] B(x,y)" % b, b=b, shape="both binary")
for b in [5, 20, 100, 500]:
    add("until", "base", "B(x,y) AND (C(x) UNTIL[0,%d] A(x,y))" % b, b=b, shape="unary left")
for b in [5, 20, 100]:
    add("until", "base", "B(x,y) AND ((NOT C(x)) UNTIL[0,%d] A(x,y))" % b, b=b, shape="negated unary left")
for b in [1, 2, 5, 10]:
    add("until_burst", "burst", "A(x,y) UNTIL[0,%d] B(x,y)" % b, b=b)
    add("until_burst", "burst", "B(x,y) AND (C(x) UNTIL[0,%d] A(x,y))" % b, b=b)

# ---- nested temporal operators -------------------------------------------------------------
for b, c in [(5, 5), (20, 5), (20, 20), (50, 20)]:
    add("nested", "base", "A(x,y) AND ONCE[0,%d] (B(y,z) AND ONCE[0,%d] C(z))" % (b, c), b=b, c=c)
for b, c in [(100, 20), (100, 100), (500, 20)]:
    add("nested", "rate10", "A(x,y) AND ONCE[0,%d] (B(y,z) AND ONCE[0,%d] C(z))" % (b, c), b=b, c=c)
for b, c in [(5, 5), (20, 20), (50, 20)]:
    add("nested", "base", "A(x,y) AND EVENTUALLY[0,%d] (B(x,z) AND ONCE[0,%d] C(z))" % (b, c), b=b, c=c)
for b, c in [(5, 5), (20, 20), (50, 20)]:
    add("nested", "base", "A(x,y) AND ONCE[0,%d] (B(x,z) AND EVENTUALLY[0,%d] C(z))" % (b, c), b=b, c=c)
for b, c in [(100, 20), (500, 20)]:
    add("nested", "rate10", "A(x,y) AND EVENTUALLY[0,%d] (B(x,z) AND ONCE[0,%d] C(z))" % (b, c), b=b, c=c)
for b, c in [(5, 5), (20, 20), (100, 100)]:
    add("nested", "base", "C(x) AND ((ONCE[0,%d] A(x,y)) SINCE[0,%d] B(x,y))" % (b, c), b=b, c=c)
for b, c in [(5, 5), (20, 20)]:
    add("nested", "base", "A(x,y) AND NOT ((B(x,y) SINCE[0,%d] A(x,y)) AND ONCE[0,%d] C(y))" % (b, c), b=b, c=c)
for f in ["A(x,y) AND NOT (C(x) SINCE[0,20] B(x,y))", "A(x,y) AND NOT (C(x) UNTIL[0,20] B(x,y))",
          "A(x,y) AND (ONCE[0,20] B(x,y)) AND (EVENTUALLY[0,20] B(x,y))",
          "A(x,y) AND (ONCE[0,20] B(x,y)) AND NOT (EVENTUALLY[0,20] B(x,y))"]:
    add("nested", "base", f)

# ---- aggregations ---------------------------------------------------------------------------
for op in ["CNT", "SUM", "MIN", "MAX", "AVG", "MED"]:
    add("agg", "base", "r <- %s y; x A(x,y)" % op, op=op, shape="grouped, one time point")
for op in ["CNT", "SUM", "MAX"]:
    add("agg", "base", "r <- %s y A(x,y)" % op, op=op, shape="no group")
for op in ["CNT", "SUM", "MAX"]:
    add("agg", "base", "r <- %s z; x (A(x,y) AND B(y,z))" % op, op=op, shape="grouped join")
for op in ["CNT", "SUM", "MIN", "MAX", "AVG", "MED"]:
    for b in ([5, 50, 500] if op in ("CNT", "SUM") else [5, 20, 50]):
        add("agg_once", "base", "r <- %s y; x ONCE[0,%d] A(x,y)" % (op, b), op=op, b=b)
for b in [5, 20, 100, 500, 2000]:
    add("agg_once_cnt", "base", "r <- CNT x ONCE[0,%d] C(x)" % b, b=b)
for b in [5, 20, 100, 500]:
    add("agg_once_cnt", "base", "r <- CNT y; x ONCE[0,%d] A(x,y)" % b, b=b)
for b in [5, 20]:
    add("agg_once_cnt", "base", "r <- CNT z; x,y ONCE[0,%d] D(x,y,z)" % b, b=b)
for log in ["dom50", "base", "dom1000"]:
    add("agg_dom", log, "r <- CNT y; x A(x,y)")
    add("agg_dom", log, "r <- SUM y; x ONCE[0,5] A(x,y)")
    add("agg_dom", log, "r <- CNT x ONCE[0,20] C(x)")
for log in ["rate10", "rate20", "base", "rate80"]:
    add("agg_rate", log, "r <- SUM y; x ONCE[0,20] A(x,y)")
    add("agg_rate", log, "r <- CNT x ONCE[0,100] C(x)")
for b in [5, 20]:
    add("agg_ev", "base", "r <- CNT y; x EVENTUALLY[0,%d] A(x,y)" % b, b=b)
    add("agg_ev", "base", "r <- SUM y; x EVENTUALLY[0,%d] A(x,y)" % b, b=b)
for f in ["A(x,y) AND (r <- CNT z; y B(y,z)) AND r < 3", "C(x) AND (r <- SUM y; x ONCE[0,20] A(x,y)) AND r < 500",
          "(r <- CNT y; x ONCE[0,20] A(x,y)) AND NOT C(x)"]:
    add("agg_guard", "base", f)

# ---- Let ------------------------------------------------------------------------------------
for b in [5, 50, 500]:
    add("let", "base", "LET P(x) = ONCE[0,%d] C(x) IN A(x,y) AND P(x)" % b, b=b)
    add("let", "base", "LET Q(x,y) = A(x,y) AND B(y,x) IN Q(x,y) AND ONCE[0,%d] Q(y,x)" % b, b=b)
add("let", "base", "LET P(x) = C(x) AND NOT (EXISTS y. A(x,y)) IN B(x,y) AND P(x)")
add("let", "base", "LET P(x,y) = A(x,y) AND NOT B(x,y) IN LET Q(x) = EXISTS y. P(x,y) IN C(x) AND Q(x)")

# ---- ternary predicates (wide tuples) ------------------------------------------------------
for b in [5, 20, 100, 500]:
    add("wide", "base", "D(x,y,z) AND ONCE[0,%d] D(x,y,z)" % b, b=b)
for b in [5, 20, 100, 500]:
    add("wide", "base", "D(x,y,z) AND NOT ONCE[1,%d] D(x,y,z)" % b, b=b)
for b in [5, 20, 100]:
    add("wide", "base", "D(x,y,z) AND EVENTUALLY[0,%d] D(x,y,z)" % b, b=b)
for b in [5, 50]:
    add("wide", "base", "D(x,y,z) AND ONCE[0,%d] (A(x,y) AND B(y,z))" % b, b=b)
    add("wide", "base", "A(x,y) AND ONCE[0,%d] (EXISTS z. D(x,y,z))" % b, b=b)
add("wide", "base", "D(x,y,z) SINCE[0,20] D(z,y,x)")
add("wide", "base", "D(x,y,z) UNTIL[0,20] D(z,y,x)")

# ---- long windows on a long, thin log --------------------------------------------------------
for b in [10, 100, 1000, 10000]:
    add("long", "long", "A(x,y) AND ONCE[0,%d] B(x,y)" % b, b=b)
for b in [10, 100, 1000, 10000]:
    add("long", "long", "A(x,y) AND NOT ONCE[1,%d] A(x,y)" % b, b=b)
for b in [10, 100, 1000]:
    add("long", "long", "A(x,y) AND NOT EVENTUALLY[0,%d] B(x,y)" % b, b=b)
for b in [10, 100, 1000, 10000]:
    add("long", "long", "r <- CNT x ONCE[0,%d] C(x)" % b, b=b)
for b in [10, 100]:
    add("long", "long", "r <- SUM y; x ONCE[0,%d] A(x,y)" % b, b=b)
for b in [10, 100, 1000]:
    add("long", "long", "C(x) SINCE[0,%d] A(x,y)" % b, b=b)

# ---- policy-shaped formulas --------------------------------------------------------------------
POLICIES = [
    ("base", "(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)"),
    ("burst", "(A(x,y) AND x < 100) AND NOT EVENTUALLY[0,6] C(y)"),
    ("base", "A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))"),
    ("burst", "A(x,y) AND x < 100 AND NOT ONCE[2,21] (EXISTS z. B(z,y))"),
    ("base", "C(x) AND NOT (EXISTS y. ONCE[0,30] A(x,y) AND NOT ONCE[0,30] B(y,x))"),
    ("base", "A(x,y) AND (EXISTS z. ONCE[0,10] (B(y,z) AND NOT ONCE[0,5] C(z)))"),
    ("base", "(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r"),
    ("base", "(r <- SUM y; x ONCE[0,60] A(x,y)) AND NOT C(x) AND 4000 < r"),
    ("base", "A(x,y) AND B(y,z) AND NOT ONCE[0,100] (A(x,y) AND B(y,z))"),
    ("base", "A(x,y) AND ((NOT C(x)) SINCE[0,100] B(x,y)) AND NOT EVENTUALLY[0,10] C(y)"),
    ("burst", "A(x,y) AND ((NOT C(x)) SINCE[0,10] B(x,y)) AND NOT EVENTUALLY[0,3] C(y)"),
    ("base", "LET Bad(x) = ONCE[0,50] (C(x) AND NOT PREV[0,1] C(x)) IN A(x,y) AND Bad(x) AND NOT Bad(y)"),
]
for log, f in POLICIES:
    add("policy", log, f)

if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "formulas"
    os.makedirs(out, exist_ok=True)
    for e in suite:
        with open(os.path.join(out, e["name"] + ".mfotl"), "w") as f:
            f.write(e["formula"] + "\n")
    json.dump(suite, open(os.path.join(out, "suite.json"), "w"), indent=1)
    fams = {}
    for e in suite:
        fams[e["family"]] = fams.get(e["family"], 0) + 1
    print(len(suite), "formulas in", len(fams), "families:", ", ".join("%s %d" % kv for kv in fams.items()))
