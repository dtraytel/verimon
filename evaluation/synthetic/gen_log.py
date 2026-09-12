# Synthetic log generator for the formulas in this directory (see ../../EFFICIENCY.md).
import random, sys
random.seed(42)
# usage: gen.py <tps> <events_per_tp> <domain> <out>
tps, n, dom, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
with open(out, "w") as f:
    for tp in range(tps):
        ts = tp  # one time point per second
        f.write(f"@{ts}")
        for _ in range(n):
            f.write(f" A({random.randrange(dom)},{random.randrange(dom)})")
        for _ in range(n):
            f.write(f" B({random.randrange(dom)},{random.randrange(dom)})")
        for _ in range(n // 4 + 1):
            f.write(f" C({random.randrange(dom)})")
        f.write("\n")
