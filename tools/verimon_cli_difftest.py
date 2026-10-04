#!/usr/bin/env python3
"""Differential test of verimon-cli against monpoly -verified.

Replays the commands of the cram tests (tests/*.t/run.t) in a copy of each test directory.
For every monpoly command (with -verified, or every one with -all), it runs

    monpoly ARGS -verified            (MonPoly's front end and the verified monitor)
    verimon-cli ARGS                  (the front end of thys/VeriMon_CLI)

where -verified, -verified_parser and -verified_log_parser are removed from ARGS, and compares
standard output, standard error and exit code.  Other commands (echo, cat, ...) are run as
they are, so that the files they create exist.

With -noformula, the lines in which MonPoly prints the input or the analyzed formula
(-verbose, -check),
which verimon-cli does not print, are removed from MonPoly's output before the comparison.

Usage: verimon_cli_difftest.py [-all] [-noformula] [-v] MONPOLY VERIMON_CLI [TEST_DIR...]
"""

import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

VERIFIED_OPTS = {"-verified", "-verified_parser", "-verified_log_parser"}


def commands(run_t):
    cmds, cur = [], None
    with open(run_t) as f:
        for line in f:
            if line.startswith("  $ "):
                if cur is not None:
                    cmds.append(cur)
                cur = line[4:].rstrip("\n")
            elif line.startswith("  > ") and cur is not None:
                cur += "\n" + line[4:].rstrip("\n")
            else:
                if cur is not None:
                    cmds.append(cur)
                cur = None
    if cur is not None:
        cmds.append(cur)
    return cmds


def strip_formula(out):
    lines, res, skip = out.split(b"\n"), [], False
    for l in lines:
        if l.startswith(b"The analyzed formula is:") or l.startswith(b"The input formula is:"):
            skip = True
            continue
        if skip and l.startswith(b"  "):
            continue
        skip = False
        res.append(l)
    return b"\n".join(res)


def run(cmd, cwd, env):
    p = subprocess.run(cmd, cwd=cwd, env=env, shell=True, capture_output=True, timeout=120)
    return p.stdout, p.stderr, p.returncode


def main():
    args = sys.argv[1:]
    all_cmds = "-all" in args
    verbose = "-v" in args
    noformula = "-noformula" in args
    args = [a for a in args if a not in ("-all", "-v", "-noformula")]
    monpoly, verimon = os.path.abspath(args[0]), os.path.abspath(args[1])
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests")
    dirs = args[2:] or sorted(
        os.path.join(root, d) for d in os.listdir(root) if d.endswith(".t"))
    env = dict(os.environ)
    total = same = 0
    for d in dirs:
        run_t = os.path.join(d, "run.t")
        if not os.path.exists(run_t):
            continue
        with tempfile.TemporaryDirectory() as tmp:
            work = os.path.join(tmp, "w")
            shutil.copytree(d, work)
            for cmd in commands(run_t):
                head = re.split(r" (?=\d?[<>])", cmd.split("|")[0], maxsplit=1)[0]
                words = shlex.split(head) if "monpoly" in cmd else []
                if not words or words[0] != "monpoly" or "\n" in cmd:
                    run(cmd.replace("monpoly", monpoly), work, env)
                    continue
                if "-verified" not in words and not all_cmds:
                    continue
                rest = [w for w in words[1:] if w not in VERIFIED_OPTS]
                tail = cmd[len(head):]
                m = run(shlex.join([monpoly] + rest + ["-verified"]) + tail, work, env)
                v = run(shlex.join([verimon] + rest) + tail, work, env)
                if noformula:
                    m = (strip_formula(m[0]), strip_formula(m[1]), m[2])
                total += 1
                if m == v:
                    same += 1
                    continue
                print(f"=== {os.path.basename(d)}: {cmd}")
                if verbose:
                    for name, a, b in zip(("stdout", "stderr", "exit"), m, v):
                        if a != b:
                            print(f"--- {name} monpoly:\n{a if isinstance(a, int) else a.decode(errors='replace')}")
                            print(f"--- {name} verimon-cli:\n{b if isinstance(b, int) else b.decode(errors='replace')}")
    print(f"{same}/{total} commands with the same output")
    return 0 if same == total else 1


if __name__ == "__main__":
    sys.exit(main())
