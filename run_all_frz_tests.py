#!/usr/bin/env python3
import subprocess
import sys
from pathlib import Path
from typing import Tuple

def run_monpoly(sig_file: str, formula_file: str, log_file: str, verified: bool = False) -> Tuple[str, int]:
    """Run MonPoly and return (output, return_code)."""
    cmd = [
        "dune", "exec", "--",
        "monpoly",
        "-sig", sig_file,
        "-formula", formula_file,
        "-log", log_file,
        "-nofilteremptytp",
    ]
    if verified:
        cmd.append("-verified")
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=10, cwd="/Users/kfx532/repos/verimon")
        return result.stdout, result.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", -1
    except Exception as e:
        return f"ERROR: {e}", -1

def normalize_output(output: str) -> str:
    """Normalize output for comparison."""
    lines = output.strip().split("\n")
    lines = [line.strip() for line in lines if line.strip()]
    return "\n".join(sorted(lines))

tests_dir = Path("/Users/kfx532/repos/verimon/tests")
test_dirs = []

for d in tests_dir.glob("frz*.t"):
    name = d.name.replace("frz", "").replace(".t", "")
    try:
        num = int(name)
        if num >= 40:
            test_dirs.append(d)
    except ValueError:
        pass

test_dirs.sort()

print(f"Running {len(test_dirs)} FRZ tests (frz40+)...\n")

passed = failed = 0
bugs = []

for test_dir in test_dirs:
    test_num = int(test_dir.name.replace("frz", "").replace(".t", ""))
    sig_file = test_dir / f"frz{test_num:02d}.sig"
    formula_file = test_dir / f"frz{test_num:02d}.mfotl"
    log_file = test_dir / f"frz{test_num:02d}.log"
    
    if not all(f.exists() for f in [sig_file, formula_file, log_file]):
        continue
    
    native_out, native_rc = run_monpoly(str(sig_file), str(formula_file), str(log_file), verified=False)
    verified_out, verified_rc = run_monpoly(str(sig_file), str(formula_file), str(log_file), verified=True)
    
    if native_rc != 0 or verified_rc != 0:
        status = "ERROR"
        if native_rc != 0 and verified_rc == 0:
            bugs.append((test_dir.name, "NATIVE CRASH", native_out[:100]))
        failed += 1
    elif normalize_output(native_out) != normalize_output(verified_out):
        status = "MISMATCH"
        bugs.append((test_dir.name, "OUTPUT MISMATCH", f"Native: {native_out[:50]}\nVerified: {verified_out[:50]}"))
        failed += 1
    else:
        status = "PASS"
        passed += 1
    
    print(f"{test_dir.name:20} {status}")

print(f"\n{'='*60}")
print(f"Results: {passed} passed, {failed} failed")

if bugs:
    print(f"\n🐛 BUGS FOUND:\n")
    for name, bug_type, detail in bugs:
        print(f"  {name}: {bug_type}")
        print(f"    {detail[:80]}")
        print()
