#!/usr/bin/env python3
"""Draw results/results.json as an SVG: one row per family, one mark per formula at its
runtime ratio (second system over the first), on a log axis; timeouts of the second system
are marked at the right edge.  No dependencies.

usage: plot.py [results/results.json] [results/ratios.svg]
"""
import json, math, sys
from xml.sax.saxutils import escape

def e(x):
    """XML-escape text that goes into an element body (formulas contain < and &)."""
    return escape(str(x))

src = sys.argv[1] if len(sys.argv) > 1 else "results/results.json"
dst = sys.argv[2] if len(sys.argv) > 2 else "results/ratios.svg"
out = json.load(open(src))
R, systems = out["results"], out["systems"]
ref, s = systems[0], systems[1]
fams = []
for r in R.values():
    if r["family"] not in fams:
        fams.append(r["family"])
W, LM, RM, TOP, RH = 900, 130, 40, 40, 16
H = TOP + RH * len(fams) + 40
lo, hi = math.log10(0.25), math.log10(32)
def X(ratio):
    return LM + (W - LM - RM) * (min(max(math.log10(ratio), lo), hi) - lo) / (hi - lo)
L = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" font-family="sans-serif" font-size="11">' % (W, H),
     '<rect width="100%" height="100%" fill="white"/>',
     '<text x="%d" y="18" font-size="13">runtime ratio %s / %s per formula (best of repetitions); x = timeout of %s, o = timeout of %s</text>' % (LM, e(s), e(ref), e(s), e(ref))]
for t in [0.25, 0.5, 1, 2, 4, 8, 16, 32]:
    x = X(t)
    L.append('<line x1="%.1f" y1="%d" x2="%.1f" y2="%d" stroke="%s" stroke-width="%s"/>' % (x, TOP - 8, x, H - 30, "#333" if t == 1 else "#ccc", "1.2" if t == 1 else "0.6"))
    L.append('<text x="%.1f" y="%d" text-anchor="middle" fill="#333">%gx</text>' % (x, H - 16, t))
for i, fam in enumerate(fams):
    y = TOP + RH * i + RH / 2
    L.append('<text x="%d" y="%.1f" text-anchor="end" dominant-baseline="middle">%s</text>' % (LM - 8, y, e(fam)))
    L.append('<line x1="%d" y1="%.1f" x2="%d" y2="%.1f" stroke="#eee"/>' % (LM, y, W - RM, y))
    for r in R.values():
        if r["family"] != fam:
            continue
        a, b = r[ref], r[s]
        if a["status"] == "ok" and b["status"] == "ok":
            ratio = b["min"] / a["min"]
            L.append('<circle cx="%.1f" cy="%.1f" r="3.2" fill="%s" fill-opacity="0.75"><title>%s: %.2f s vs %.2f s (%.2fx) %s</title></circle>' % (
                X(ratio), y, "#c0392b" if ratio > 2 else ("#2e7d32" if ratio < 0.9 else "#1f77b4"), e(r["formula"]), a["min"], b["min"], ratio, e(r["log"])))
        elif b["status"] == "timeout":
            L.append('<text x="%.1f" y="%.1f" text-anchor="middle" dominant-baseline="middle" fill="#c0392b" font-weight="bold">x<title>%s: %s %s, %s timeout</title></text>' % (
                W - RM + 12, y, e(r["formula"]), e(ref), ("%.2f s" % a["min"]) if a["status"] == "ok" else e(a["status"]), e(s)))
        elif a["status"] == "timeout":
            L.append('<text x="%.1f" y="%.1f" text-anchor="middle" dominant-baseline="middle" fill="#2e7d32" font-weight="bold">o<title>%s: %s timeout, %s %s</title></text>' % (
                LM - 100 + 88, y, e(r["formula"]), e(ref), e(s), e(b["status"])))
L.append("</svg>")
open(dst, "w").write("\n".join(L))
print("wrote", dst)
