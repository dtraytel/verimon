# Triangle-join benchmark: A(x,y) AND B(y,z) AND C(z,x) over a small domain, one time point per line.
# usage: gen_triangle_log.py <tps> <events_per_relation_per_tp> <domain> <out>
import random, sys
random.seed(7)
tps, n, dom, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
with open(out, "w") as f:
    for tp in range(tps):
        f.write(f"@{tp}")
        for rel in ("A", "B", "C"):
            for _ in range(n):
                f.write(f" {rel}({random.randrange(dom)},{random.randrange(dom)})")
        f.write("\n")
