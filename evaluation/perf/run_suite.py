#!/usr/bin/env python3
"""Run the performance suite: every formula of suite.txt under each system, with a timeout per
run, a few interleaved repetitions, and a wall-clock budget for the whole suite.

  python3 run_suite.py --bin ../../_build/default/src/main.exe [--reps 3] [--timeout 5]
                       [--jobs 2] [--budget 1800] [--systems monpoly,verimon]
                       [--families once,since] [--out results]

Systems: monpoly is the binary without flags; verimon is `-verified`, the verified dense evaluator
of thys/MFODL_Monitor_Dense (reports before 2026-09-23 call it `vdense`, from when it needed
`-vdense` next to a second, unverified dense monitor under `-verified`; that monitor is no
longer in the binary).  Run against a build of master, `-verified` is the original VeriMon.

A run that exceeds the timeout is recorded as such and not repeated.  A non-zero exit is
classified as `refused` (outside the verified dense fragment), `unmonitorable` (the front end
rejected the formula) or `error`.  The verdicts of the systems are compared (a hash of the
output) and disagreements are reported.  Repetitions are interleaved across systems, and
formulas are handed to the workers in the suite's order.  When the projected wall time
exceeds the budget, the remaining formulas run with one repetition; when even that would
exceed it, the remaining formulas are skipped -- the report says so.

Writes <out>/results.json, <out>/results.csv and <out>/report.md.
"""
import argparse, concurrent.futures, csv, hashlib, json, math, os, statistics, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
SYSTEMS = {"monpoly": [], "verimon": ["-verified"]}


def read_suite(path):
    """suite.txt: '## family: description' opens a group; 'name | log | formula | note' is an entry."""
    suite, family, seen = [], None, set()
    for ln in open(path, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if ln.startswith("## "):
            family = ln[3:].split(":")[0].strip()
            continue
        if not ln.strip() or ln.lstrip().startswith("#"):
            continue
        parts = [p.strip() for p in ln.split("|")]
        if len(parts) < 3 or family is None:
            sys.exit("suite.txt: bad line: " + ln)
        name, log, formula = parts[:3]
        note = parts[3] if len(parts) > 3 else ""
        if name in seen:
            sys.exit("suite.txt: duplicate name " + name)
        seen.add(name)
        suite.append({"name": name, "family": family, "log": log, "formula": formula, "note": note})
    return suite


def run_once(binary, flags, sig, formula, log, timeout):
    """One monitor run: (status, seconds, output hash)."""
    cmd = [binary] + flags + ["-sig", sig, "-formula", formula, "-log", log]
    t0 = time.perf_counter()
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", timeout, None
    dt = time.perf_counter() - t0
    if p.returncode != 0:
        err = (p.stderr or b"").decode("utf-8", "replace") + (p.stdout or b"").decode("utf-8", "replace")
        if "outside the verified dense fragment" in err:
            return "refused", dt, None
        if "not monitorable" in err.lower() or "monitorable" in err.lower():
            return "unmonitorable", dt, None
        return "error", dt, err.strip().splitlines()[-1][:200] if err.strip() else "exit %d" % p.returncode
    if b"NOT monitorable" in p.stdout[:200]:
        return "unmonitorable", dt, None
    return "ok", dt, hashlib.md5(p.stdout).hexdigest()[:12]


def run_formula(entry, args, systems, reps_for):
    """All systems and repetitions of one formula, interleaved."""
    sig = os.path.join(args.logs, "perf.sig")
    log = os.path.join(args.logs, entry["log"] + ".log")
    formula = os.path.join(args.out, "mfotl", entry["name"] + ".mfotl")
    res = {s: {"times": [], "status": None, "hash": None, "detail": None} for s in systems}
    reps = reps_for()
    for r in range(reps):
        for s in systems:
            if r > 0 and res[s]["status"] != "ok":
                continue
            st, dt, h = run_once(args.bin, SYSTEMS[s], sig, formula, log, args.timeout)
            if st == "ok":
                res[s]["times"].append(dt)
                res[s]["status"] = "ok"
                res[s]["hash"] = h
            else:
                res[s]["status"] = st
                res[s]["detail"] = h if st == "error" else None
                if st == "timeout":
                    res[s]["times"].append(dt)
    return res


def geomean(xs):
    xs = [x for x in xs if x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", default=os.path.join(HERE, "..", "..", "_build", "default", "src", "main.exe"))
    ap.add_argument("--logs", default=os.path.join(HERE, "logs"))
    ap.add_argument("--suite", default=os.path.join(HERE, "suite.txt"))
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=float, default=5.0)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--budget", type=float, default=1800.0, help="wall-clock budget in seconds")
    ap.add_argument("--systems", default="monpoly,verimon")
    ap.add_argument("--families", default="", help="comma-separated subset of families")
    ap.add_argument("--names", default="", help="comma-separated subset of formula names")
    args = ap.parse_args()
    args.reps = max(1, min(3, args.reps))
    systems = args.systems.split(",")
    suite = read_suite(args.suite)
    if args.families:
        fams = set(args.families.split(","))
        suite = [e for e in suite if e["family"] in fams]
    if args.names:
        names = set(args.names.split(","))
        suite = [e for e in suite if e["name"] in names]
    if not os.path.exists(os.path.join(args.logs, "perf.sig")):
        sys.exit("no logs: run gen_logs.py first")
    os.makedirs(os.path.join(args.out, "mfotl"), exist_ok=True)
    for e in suite:
        with open(os.path.join(args.out, "mfotl", e["name"] + ".mfotl"), "w") as f:
            f.write(e["formula"] + "\n")

    t_start = time.perf_counter()
    lock = threading.Lock()
    state = {"done": 0, "spent": 0.0, "reduced": 0, "skipped": 0}
    n = len(suite)
    worst_per_formula = len(systems) * args.timeout  # what one repetition can cost at most

    def reps_for():
        # projected time for the rest at the average cost so far, over the workers
        with lock:
            elapsed = time.perf_counter() - t_start
            remaining = n - state["done"]
            if state["done"] < 10:  # no data yet: assume the target of about a second per run
                avg = len(systems) * 1.0
            else:
                avg = state["spent"] / state["done"]
            if elapsed + remaining * avg * args.reps / args.jobs <= args.budget:
                return args.reps
            state["reduced"] += 1
            if elapsed + remaining * avg / args.jobs <= args.budget:
                return 1
            return 0

    results = {}

    def work(entry):
        reps = reps_for()
        if reps == 0:
            with lock:
                state["skipped"] += 1
                state["done"] += 1
            return entry["name"], None
        t0 = time.perf_counter()
        r = run_formula(entry, args, systems, lambda: reps)
        with lock:
            state["done"] += 1
            state["spent"] += (time.perf_counter() - t0) / reps
            d = state["done"]
        if d % 20 == 0 or d == n:
            print("%d/%d formulas, %.0f s" % (d, n, time.perf_counter() - t_start), flush=True)
        return entry["name"], r

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for name, r in ex.map(work, suite):
            if r is not None:
                results[name] = r
    wall = time.perf_counter() - t_start

    # ---- results.json / results.csv
    out = {"args": vars(args), "wall_seconds": wall, "systems": systems, "reduced_reps": state["reduced"],
           "skipped": state["skipped"], "results": {}}
    rows = []
    for e in suite:
        r = results.get(e["name"])
        if r is None:
            continue
        rec = {"family": e["family"], "log": e["log"], "formula": e["formula"], "note": e["note"]}
        for s in systems:
            rec[s] = {"status": r[s]["status"], "min": min(r[s]["times"]) if r[s]["times"] else None,
                      "times": r[s]["times"], "hash": r[s]["hash"], "detail": r[s]["detail"]}
        hs = {r[s]["hash"] for s in systems if r[s]["status"] == "ok"}
        rec["agree"] = len(hs) <= 1
        out["results"][e["name"]] = rec
        row = [e["name"], e["family"], e["log"], e["formula"]]
        for s in systems:
            row += [rec[s]["status"], "%.3f" % rec[s]["min"] if rec[s]["min"] is not None else ""]
        row.append("yes" if rec["agree"] else "NO")
        rows.append(row)
    json.dump(out, open(os.path.join(args.out, "results.json"), "w"), indent=1)
    with open(os.path.join(args.out, "results.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "family", "log", "formula"] + sum([[s + "_status", s + "_min_s"] for s in systems], []) + ["agree"])
        w.writerows(rows)
    write_report(out, suite, systems, args, os.path.join(args.out, "report.md"))
    print("wall %.0f s; report in %s" % (wall, os.path.join(args.out, "report.md")))


def write_report(out, suite, systems, args, path):
    R = out["results"]
    ref, sysx = systems[0], systems[1:]
    L = []
    L.append("# Performance suite: %s\n" % " vs ".join(systems))
    L.append("%d formulas, %d families; %d repetitions (best of), timeout %.0f s per run, %d workers; "
             "wall time %.0f s (budget %.0f s).%s%s\n" % (
                 len(R), len({e["family"] for e in suite}), args.reps, args.timeout, args.jobs,
                 out["wall_seconds"], args.budget,
                 " %d formulas ran with one repetition to stay within the budget." % out["reduced_reps"] if out["reduced_reps"] else "",
                 " %d formulas were skipped to stay within the budget." % out["skipped"] if out["skipped"] else ""))
    for s in sysx:
        # overall
        both = [(n, r) for n, r in R.items() if r[ref]["status"] == "ok" and r[s]["status"] == "ok"]
        ratios = [r[s]["min"] / r[ref]["min"] for _, r in both]
        L.append("## %s against %s\n" % (s, ref))
        counts = {}
        for r in R.values():
            counts[r[s]["status"]] = counts.get(r[s]["status"], 0) + 1
        rcounts = {}
        for r in R.values():
            rcounts[r[ref]["status"]] = rcounts.get(r[ref]["status"], 0) + 1
        L.append("| | %s | %s |\n|---|---|---|" % (ref, s))
        for st in ["ok", "timeout", "refused", "unmonitorable", "error"]:
            L.append("| %s | %d | %d |" % (st, rcounts.get(st, 0), counts.get(st, 0)))
        L.append("")
        if ratios:
            L.append("Over the %d formulas both finish: geometric mean of %s/%s = **%.2f**, median %.2f, "
                     "%d where %s is faster, %d within 10%%, %d where %s is more than 2x slower, "
                     "%d more than 4x slower.\n" % (
                         len(ratios), s, ref, geomean(ratios), statistics.median(ratios),
                         sum(1 for x in ratios if x < 1), s, sum(1 for x in ratios if 0.9 <= x <= 1.1),
                         sum(1 for x in ratios if x > 2), s, sum(1 for x in ratios if x > 4)))
        dis = [n for n, r in both if not r["agree"]]
        L.append("Verdict disagreements: %s\n" % (", ".join(dis) if dis else "none"))
        # per family
        L.append("### By family\n")
        L.append("| family | n | both ok | geomean %s/%s | min | max | %s timeouts | %s timeouts | refused |" % (s, ref, ref, s))
        L.append("|---|---|---|---|---|---|---|---|---|")
        fams = []
        for e in suite:
            if e["family"] not in fams:
                fams.append(e["family"])
        for fam in fams:
            rs = [r for n, r in R.items() if r["family"] == fam]
            if not rs:
                continue
            rat = [r[s]["min"] / r[ref]["min"] for r in rs if r[ref]["status"] == "ok" and r[s]["status"] == "ok"]
            L.append("| %s | %d | %d | %s | %s | %s | %d | %d | %d |" % (
                fam, len(rs), len(rat), "%.2f" % geomean(rat) if rat else "-",
                "%.2f" % min(rat) if rat else "-", "%.2f" % max(rat) if rat else "-",
                sum(1 for r in rs if r[ref]["status"] == "timeout"),
                sum(1 for r in rs if r[s]["status"] == "timeout"),
                sum(1 for r in rs if r[s]["status"] == "refused")))
        L.append("")
        # extremes
        srt = sorted(both, key=lambda nr: nr[1][s]["min"] / nr[1][ref]["min"])
        for title, sel in [("Where %s is slowest relative to %s" % (s, ref), list(reversed(srt))[:15]),
                           ("Where %s is fastest relative to %s" % (s, ref), srt[:10])]:
            L.append("### %s\n" % title)
            L.append("| name | log | formula | %s s | %s s | ratio |\n|---|---|---|---|---|---|" % (ref, s))
            for n, r in sel:
                L.append("| %s | %s | `%s` | %.2f | %.2f | %.2f |" % (
                    n, r["log"], r["formula"], r[ref]["min"], r[s]["min"], r[s]["min"] / r[ref]["min"]))
            L.append("")
        # timeouts / refused / errors
        odd = [(n, r) for n, r in R.items() if r[s]["status"] != "ok" or r[ref]["status"] != "ok"]
        if odd:
            L.append("### Timeouts, refusals and errors\n")
            L.append("| name | log | formula | %s | %s |\n|---|---|---|---|---|" % (ref, s))
            for n, r in odd:
                def cell(x):
                    return ("%.2f s" % x["min"]) if x["status"] == "ok" else (x["status"] + (": " + x["detail"] if x["detail"] else ""))
                L.append("| %s | %s | `%s` | %s | %s |" % (n, r["log"], r["formula"], cell(r[ref]), cell(r[s])))
            L.append("")
    # full table
    L.append("## All formulas\n")
    L.append("| name | log | formula | " + " | ".join("%s s" % s for s in systems) + " | ratio | agree | why |")
    L.append("|---|---|---|" + "---|" * len(systems) + "---|---|---|")
    for e in suite:
        r = R.get(e["name"])
        if r is None:
            continue
        cells = []
        for s in systems:
            cells.append("%.2f" % r[s]["min"] if r[s]["status"] == "ok" else r[s]["status"])
        ratio = ("%.2f" % (r[sysx[0]]["min"] / r[ref]["min"])) if sysx and r[ref]["status"] == "ok" and r[sysx[0]]["status"] == "ok" else "-"
        L.append("| %s | %s | `%s` | %s | %s | %s | %s |" % (e["name"], e["log"], e["formula"], " | ".join(cells), ratio, "yes" if r["agree"] else "NO", e["note"]))
    open(path, "w").write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()
