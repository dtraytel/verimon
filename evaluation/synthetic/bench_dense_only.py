# Benchmark driver for EFFICIENCY.md 20.43: the dense monitor as the only one,
# against the unverified MonPoly kernel and against the kernel this session started
# from.  Repetitions are interleaved across configurations rather than grouped, so
# that drift in machine load hits every column equally.
#
# Setup (in a scratch directory), as for bench_unbox.py:
#   python3 gen_log.py 8000 50 200 syn.log          # the 8.6 MB log of 20.18
#   head -400 syn.log > syn_small.log               # for the quadratic freeze row
#   cp custom.sig syn.sig; cp *.mfotl .
#   gen_log -policy P2 -event_rate 2000 -time_span 100 > P2.log    # likewise P3
#   cp ../../examples/sigs/P{2,3}.sig ../../examples/mfotl/P{2,3}.mfotl .
#   cp ../../_build/default/src/main.exe monpoly_now
#   git worktree add /tmp/was <commit before 20.38>                # the "was" kernel
#   (cd /tmp/was && dune build src/) && cp /tmp/was/_build/default/src/main.exe monpoly_was
# then: python3 bench_dense_only.py 7   ->  times38.json (checked in as times_20_43.json)
#
# Note that "monpoly_was -verified -dense" is the only way to get the fallback node's
# behaviour: in monpoly_now the flag is an accepted no-op and the fallback is gone.
import subprocess, time, json, sys

REPS = int(sys.argv[1]) if len(sys.argv) > 1 else 7
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
    ("trigger", "trigger.mfotl", SYN), ("andtrigger", "andtrigger.mfotl", SYN),
    ("matchp", "matchp.mfotl", SYN), ("frz*", "frz.mfotl", ("syn.sig", "syn_small.log")),
    ("aggonce", "aggonce.mfotl", SYN),
]
# The unverified kernel does not monitor Trigger, MatchP or Frz; those rows have no
# "monpoly" column and the driver records nothing for them.
NO_MONPOLY = {"trigger", "andtrigger", "matchp", "frz*"}
CONFIGS = [
    ("monpoly",      "./monpoly_now", []),
    ("verimon(was)", "./monpoly_was", ["-verified"]),
    ("dense(was)",   "./monpoly_was", ["-verified", "-dense"]),
    ("verimon",      "./monpoly_now", ["-verified"]),
]

res = {}
devnull = open("/dev/null", "w")
for r in range(REPS):
    for fname, mf, (sig, log) in FORMULAS:
        for cname, binary, flags in CONFIGS:
            if cname == "monpoly" and fname in NO_MONPOLY:
                continue
            cmd = [binary] + flags + ["-sig", sig, "-formula", mf, "-log", log]
            t0 = time.perf_counter()
            subprocess.run(cmd, stdout=devnull, stderr=devnull, check=True)
            res.setdefault("%s|%s" % (fname, cname), []).append(time.perf_counter() - t0)
        print("  %s done" % fname, flush=True)
    print("rep %d done" % (r + 1), flush=True)
    json.dump(res, open("times38.json", "w"), indent=1)
print("written")
