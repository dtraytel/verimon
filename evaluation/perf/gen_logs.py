#!/usr/bin/env python3
"""Synthetic logs for the performance suite (see README.md).

Every log has one signature, perf.sig:  A(int,int)  B(int,int)  C(int)  D(int,int,int).
Each log is a point in a small design space: the number of time points, how many time points
share a timestamp (burstiness), how many events of each predicate a time point carries (rate)
and the range the values are drawn from (domain, which sets the selectivity of joins and the
number of groups of an aggregation).  Values are uniform, so the logs are memoryless; the
temporal operators see a stationary stream and the trends across a family are the operators'.

usage: gen_logs.py [OUTDIR]        (default: logs/)
"""
import os, random, sys

LOGS = {
    #  name       tps    tps/ts  nA  nB  nC  nD  domain
    "base":     (6000,    1,    40, 40, 10, 10,  200),
    "dom50":    (6000,    1,    40, 40, 10, 10,   50),
    "dom1000":  (6000,    1,    40, 40, 10, 10, 1000),
    "rate10":   (6000,    1,    10, 10,  3,  3,  200),
    "rate20":   (6000,    1,    20, 20,  5,  5,  200),
    "rate80":   (6000,    1,    80, 80, 20, 20,  200),
    "burst":   (12000,   60,    20, 20,  5,  5,  200),
    "long":    (30000,    1,     8,  8,  4,  4,  200),
}

SIG = "A(int,int)\nB(int,int)\nC(int)\nD(int,int,int)\n"


def write_log(path, tps, per_ts, nA, nB, nC, nD, dom):
    rnd = random.Random(hash((tps, per_ts, nA, nB, nC, nD, dom)) & 0xffffffff)
    r = rnd.randrange
    with open(path, "w") as f:
        for tp in range(tps):
            ts = tp // per_ts
            parts = ["@%d" % ts]
            parts += ["A(%d,%d)" % (r(dom), r(dom)) for _ in range(nA)]
            parts += ["B(%d,%d)" % (r(dom), r(dom)) for _ in range(nB)]
            parts += ["C(%d)" % r(dom) for _ in range(nC)]
            parts += ["D(%d,%d,%d)" % (r(dom), r(dom), r(dom)) for _ in range(nD)]
            f.write(" ".join(parts) + "\n")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "logs"
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "perf.sig"), "w") as f:
        f.write(SIG)
    for name, params in LOGS.items():
        path = os.path.join(out, name + ".log")
        if os.path.exists(path):
            continue
        write_log(path, *params)
        print("wrote", path, "%.1f MB" % (os.path.getsize(path) / 1e6), flush=True)
