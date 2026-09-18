import subprocess, time, json, statistics, sys

REPS = 5
SYN = ("syn.sig", "syn.log")
FORMULAS = [
    ("and", "f_and.mfotl", SYN), ("andnot", "f_andnot.mfotl", SYN),
    ("once", "f_once.mfotl", SYN), ("since", "f_since.mfotl", SYN),
    ("eventually", "f_eventually.mfotl", SYN), ("until", "f_until.mfotl", SYN),
    ("agg", "f_agg.mfotl", SYN), ("complex", "f_complex.mfotl", SYN),
    ("sincewide", "f_sincewide.mfotl", SYN), ("untilwide", "f_untilwide.mfotl", SYN),
    ("aggwide", "f_aggwide.mfotl", SYN),
    ("sincesub", "f_sincesub.mfotl", SYN), ("untilsub", "f_untilsub.mfotl", SYN),
    ("sincesub3", "f_sincesub3.mfotl", SYN),
    ("P2", "P2.mfotl", ("P2.sig", "P2.log")), ("P3", "P3.mfotl", ("P3.sig", "P3.log")),
]
CONFIGS = [
    ("monpoly",  "./monpoly-new", []),
    ("pure",     "./monpoly-new", ["-verified"]),
    ("dense-old","./monpoly-old", ["-verified", "-dense"]),
    ("dense",    "./monpoly-new", ["-verified", "-dense"]),
    ("dense+h",  "./monpoly-new", ["-verified", "-dense", "-heap_maps"]),
]

res = {(f, c): [] for f, _, _ in FORMULAS for c, _, _ in CONFIGS}
devnull = open("/dev/null", "w")
# round-robin over repetitions so that any drift in machine load hits every
# configuration equally rather than whichever one happens to run last
for r in range(REPS):
    for fname, mf, (sig, log) in FORMULAS:
        for cname, binary, flags in CONFIGS:
            cmd = [binary] + flags + ["-sig", sig, "-formula", mf, "-log", log]
            t0 = time.perf_counter()
            subprocess.run(cmd, stdout=devnull, stderr=devnull, check=True)
            res[(fname, cname)].append(time.perf_counter() - t0)
    print("rep %d done" % (r + 1), flush=True)

out = {"%s|%s" % k: v for k, v in res.items()}
json.dump(out, open("times.json", "w"), indent=1)
print("written")

# Reproduce: see EFFICIENCY.md 20.35.
#   python3 gen_log.py 8000 50 200 syn.log
#   gen_log -policy P2 -event_rate 2000 -time_span 100 > P2.log   (likewise P3)
# then place the formulas named in FORMULAS beside this script and run it.
