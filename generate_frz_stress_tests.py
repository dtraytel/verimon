#!/usr/bin/env python3
"""
Generate aggressive FRZ stress tests designed to hunt for bugs.
These tests push edge cases, boundary conditions, and complex interactions.
"""

import os
from pathlib import Path
from dataclasses import dataclass

@dataclass
class FrzTest:
    num: int
    name: str
    description: str
    signature: str
    formula: str
    log: str

def create_test_dir(test: FrzTest, base_path: str = "/Users/kfx532/repos/verimon/tests"):
    """Create a test directory."""
    test_dir = Path(base_path) / f"frz{test.num:02d}.t"
    test_dir.mkdir(exist_ok=True)

    with open(test_dir / f"frz{test.num:02d}.sig", "w") as f:
        f.write(test.signature)
        if not test.signature.endswith("\n"):
            f.write("\n")

    with open(test_dir / f"frz{test.num:02d}.mfotl", "w") as f:
        f.write(test.formula)
        if not test.formula.endswith("\n"):
            f.write("\n")

    with open(test_dir / f"frz{test.num:02d}.log", "w") as f:
        f.write(test.log)
        if not test.log.endswith("\n"):
            f.write("\n")

    run_content = f"""{test.description}
  $ monpoly -sig frz{test.num:02d}.sig -formula frz{test.num:02d}.mfotl -log frz{test.num:02d}.log -nofilteremptytp -verified
  $ monpoly -sig frz{test.num:02d}.sig -formula frz{test.num:02d}.mfotl -log frz{test.num:02d}.log -nofilteremptytp
"""
    with open(test_dir / "run.t", "w") as f:
        f.write(run_content)

    print(f"Created test frz{test.num:02d}: {test.name}")

# Stress tests designed to find bugs
tests = [
    FrzTest(
        num=60,
        name="Empty frozen snapshot",
        description="""Test FRZ where phi is never satisfied.
Frozen snapshot q(x) is always empty, psi should produce no output.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = a(x) IN ONCE[0,*) q(x)",
        log="""@0 b(1) b(2)
@1 b(3)
@2
@5""",
    ),

    FrzTest(
        num=61,
        name="All empty snapshots in trace",
        description="""Multiple timepoints with empty predicates.
Tests handling of empty relations at different times.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = a(x) IN ONCE[0,*) (b(x) AND q(x))",
        log="""@0
@1
@2 a(1) b(1)
@3
@4
@6""",
    ),

    FrzTest(
        num=62,
        name="Frozen snapshot changes at each timepoint",
        description="""phi is satisfied at each timepoint with different values.
Tests snapshot creation and reuse across many timepoints.""",
        signature="a(x:int)\nb(y:int)",
        formula="FRZ q(x) = a(x) IN (b(x) AND SINCE[0,*) q(x))",
        log="""@0 a(1) b(1)
@1 a(2) b(2)
@2 a(3) b(3)
@3 a(4) b(4)
@5 a(5) b(5)
@7 a(6) b(6)
@10""",
    ),

    FrzTest(
        num=63,
        name="Large arity predicates with FRZ",
        description="""Frozen predicate with many arguments.
Tests multi-argument frozen relations.""",
        signature="a(x:int,y:int,z:int)\nb(x:int)",
        formula="FRZ q(x,y,z) = a(x,y,z) IN (b(x) AND ONCE[0,*) q(x,y,z))",
        log="""@0 a(1,2,3) b(1)
@1 b(2) a(2,3,4)
@2 a(1,2,3)
@4""",
    ),

    FrzTest(
        num=64,
        name="Frozen predicate with repeated values",
        description="""phi contains duplicate tuples at same timepoint.
Tests handling of frozen relations with repeated elements.""",
        signature="a(x:int)",
        formula="FRZ q(x) = a(x) IN ONCE[0,*) q(x)",
        log="""@0 a(1) a(1) a(1) a(2) a(2)
@1
@2 a(3)
@5""",
    ),

    FrzTest(
        num=65,
        name="Rapidly changing snapshots with SINCE",
        description="""Frozen snapshots at consecutive timepoints used in SINCE.
Tests proper queue management with many snapshots.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = a(x) IN (b(x) SINCE[0,*) (c(x) AND q(x)))",
        log="""@0 a(1) c(1)
@1 a(2) b(2)
@2 a(3) c(3)
@3 a(4) b(4)
@4 a(5) c(5)
@6 a(6) b(6)
@10""",
    ),

    FrzTest(
        num=66,
        name="FRZ with variable not in psi",
        description="""Frozen phi binds variable that doesn't appear in psi.
Tests handling of unused frozen variables.""",
        signature="a(x:int,y:int)\nb(y:int)",
        formula="FRZ q(x,y) = a(x,y) IN b(y)",
        log="""@0 a(1,10) a(2,20) b(10)
@1 a(3,30) b(20)
@2 a(4,10) b(30)
@4""",
    ),

    FrzTest(
        num=67,
        name="Metric interval boundaries with frozen",
        description="""Test metric interval [a,b] at exact boundaries.
Snapshot at exact boundary of temporal interval.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = a(x) IN ONCE[2,5] (b(x) AND q(x))",
        log="""@0 a(1) b(1)
@2 c(1)
@3 c(2)
@4 c(3)
@5 c(4)
@6 c(5)
@8""",
    ),

    FrzTest(
        num=68,
        name="Overlapping SINCE intervals with frozen",
        description="""Multiple SINCE operators with overlapping temporal ranges.
Tests complex temporal interactions.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = a(x) IN (b(x) SINCE[0,5] q(x)) AND (c(x) SINCE[3,8] q(x))",
        log="""@0 a(1) b(1) c(1)
@2 b(1) c(1)
@4 b(1)
@6 c(1)
@10""",
    ),

    FrzTest(
        num=69,
        name="Nested EXISTS with FRZ",
        description="""Multiple levels of existential quantification with frozen predicates.
Tests complex variable scoping.""",
        signature="a(x:int)\nb(x:int,y:int,z:int)",
        formula="FRZ q(x) = a(x) IN EXISTS y. EXISTS z. (b(x,y,z) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1,2,3) b(1,4,5)
@1 b(2,3,4)
@3 a(2) b(2,5,6)
@5""",
    ),

    FrzTest(
        num=70,
        name="FRZ with NOT and live predicates",
        description="""Frozen predicate combined with negation of live predicates.
Tests safety constraints with negation.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = a(x) IN (q(x) AND NOT b(x))",
        log="""@0 a(1) c(1)
@1 a(1) b(1)
@2 a(1)
@3 a(2) b(2) c(2)
@5""",
    ),

    FrzTest(
        num=71,
        name="Timestamp gaps with frozen snapshots",
        description="""Large gaps between consecutive timepoints.
Tests snapshot persistence across long gaps.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = a(x) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1)
@100 b(2)
@200 a(3)
@300 b(3)
@1000""",
    ),

    FrzTest(
        num=72,
        name="Mixed temporal and frozen operators",
        description="""Complex formula with many temporal operators and frozen snapshots.
Tests comprehensive FRZ semantics.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)\nd(x:int)",
        formula="FRZ q(x) = a(x) IN ((ONCE[0,1] b(x)) OR (SINCE[0,2] (c(x) AND q(x)))) AND EVENTUALLY[0,3] d(x)",
        log="""@0 a(1) b(1) c(1) d(1)
@1 c(2) d(2)
@2 a(2) b(2)
@3 d(3)
@5""",
    ),

    FrzTest(
        num=73,
        name="Frozen predicate with single element at multiple times",
        description="""Same frozen element persists and is reused across timepoints.
Tests queue trimming and discharge.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = a(x) IN (ONCE[0,*) (b(x) AND q(x)))",
        log="""@0 a(42) b(42)
@1 b(100)
@2 b(200)
@3 b(300)
@4 b(400)
@5 b(500)
@10""",
    ),

    FrzTest(
        num=74,
        name="Triple FRZ with empty middle level",
        description="""Triple nesting where middle frozen predicate is sometimes empty.
Tests nesting with variable-size intermediate relations.""",
        signature="a(x:int)\nb(y:int)\nc(z:int)",
        formula="FRZ q(x) = a(x) IN FRZ r(y) = b(y) IN FRZ s(z) = c(z) IN (q(x) AND r(y) AND s(z))",
        log="""@0 a(1) b(2) c(3)
@1 b(4) c(5)
@2 a(2)
@3 b(6) c(7)
@5""",
    ),

    FrzTest(
        num=75,
        name="Very deep timestamp values",
        description="""Large timestamp values to test arithmetic correctness.
Tests handling of large time values in intervals.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = a(x) IN ONCE[1000,2000] (b(x) AND q(x))",
        log="""@500 a(1) b(1)
@1500 b(2)
@2000 a(2)
@3000 b(3)
@5000""",
    ),
]

if __name__ == "__main__":
    for test in tests:
        create_test_dir(test)
    print(f"\nGenerated {len(tests)} stress test cases (frz60-frz75)")
