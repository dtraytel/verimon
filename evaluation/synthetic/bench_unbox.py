# Benchmark driver for EFFICIENCY.md 20.37.  Repetitions are interleaved across
# configurations rather than grouped, so that drift in machine load hits every
# column equally instead of whichever one happens to run last.
#
# Setup (in a scratch directory):
#   python3 gen_log.py 8000 50 200 syn.log          # the 8.6 MB log of 20.18
#   cp custom.sig syn.sig; cp *.mfotl .
#   gen_log -policy P2 -event_rate 2000 -time_span 100 > P2.log    # likewise P3
#   cp ../../examples/sigs/P{2,3}.sig ../../examples/mfotl/P{2,3}.mfotl .
#   cp ../../_build/default/src/main.exe monpoly_now
#   git worktree add /tmp/was <commit before the unboxing>         # the "was" kernel
#   (cd /tmp/was && dune build src/) && cp /tmp/was/_build/default/src/main.exe monpoly_was
# then: python3 bench_unbox.py   ->  times36.json
import subprocess, time, json, sys

REPS = 9
SYN = ("syn.sig", "syn.log")
FORMULAS = [
    ("P2", "P2.mfotl", ("P2.sig", "P2.log")), ("P3", "P3.mfotl", ("P3.sig", "P3.log")),
    ("and", "and.mfotl", SYN), ("andnot", "andnot.mfotl", SYN),
    ("once", "once.mfotl", SYN), ("since", "since.mfotl", SYN),
    ("eventually", "eventually.mfotl", SYN), ("until", "until.mfotl", SYN),
    ("agg", "agg.mfotl", SYN), ("complex", "complex.mfotl", SYN),
    ("sincewide", "sincewide.mfotl", SYN), ("untilwide", "untilwide.mfotl", SYN),
    ("aggwide", "aggwide.mfotl", SYN),
    ("sincesub", "sincesub.mfotl", SYN), ("untilsub", "untilsub.mfotl", SYN),
    ("sincesub3", "sincesub3.mfotl", SYN),
]
CONFIGS = [
    ("monpoly",    "./monpoly_now", []),
    ("pure",       "./monpoly_now", ["-verified"]),
    ("dense (was)","./monpoly_was", ["-verified", "-dense"]),
    ("dense",      "./monpoly_now", ["-verified", "-dense"]),
    ("dense+h",    "./monpoly_now", ["-verified", "-dense", "-heap_maps"]),
]

res = {(f, c): [] for f, _, _ in FORMULAS for c, _, _ in CONFIGS}
devnull = open("/dev/null", "w")
for r in range(REPS):
    for fname, mf, (sig, log) in FORMULAS:
        for cname, binary, flags in CONFIGS:
            cmd = [binary] + flags + ["-sig", sig, "-formula", mf, "-log", log]
            t0 = time.perf_counter()
            subprocess.run(cmd, stdout=devnull, stderr=devnull, check=True)
            res[(fname, cname)].append(time.perf_counter() - t0)
    print("rep %d done" % (r + 1), flush=True)

json.dump({"%s|%s" % k: v for k, v in res.items()}, open("times36.json", "w"), indent=1)
print("written")
