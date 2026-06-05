#!/usr/bin/env python3
"""
Generate FRZ tests with complex phi (frozen formula).
Focus on cases where the snapshot itself is computed from complex formulas.
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

    run_content = f"""Complex frozen formula test.
  $ monpoly -sig frz{test.num:02d}.sig -formula frz{test.num:02d}.mfotl -log frz{test.num:02d}.log -nofilteremptytp -verified
  $ monpoly -sig frz{test.num:02d}.sig -formula frz{test.num:02d}.mfotl -log frz{test.num:02d}.log -nofilteremptytp
"""
    with open(test_dir / "run.t", "w") as f:
        f.write(run_content)

    print(f"Created test frz{test.num:02d}: {test.name}")

# Tests with COMPLEX PHI (frozen formula)
tests = [
    FrzTest(
        num=80,
        name="FRZ with conjunction in phi",
        description="""Frozen formula is a conjunction of predicates.
phi = a(x) AND b(x): snapshot contains only tuples satisfying both.
Tests that frozen snapshot correctly reflects conjunction semantics.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) AND b(x)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) a(2) b(1) b(3) c(1)
@1 a(1) b(1) c(2)
@2 b(2) c(3)
@4""",
    ),

    FrzTest(
        num=81,
        name="FRZ with disjunction in phi",
        description="""Frozen formula uses disjunction (OR).
phi = a(x) OR b(x): snapshot contains union of both relations.
Tests that frozen snapshot correctly reflects disjunction semantics.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) OR b(x)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(2) c(1) c(2)
@1 a(3) c(3)
@2 b(1) b(4) c(4)
@5""",
    ),

    FrzTest(
        num=82,
        name="FRZ with ONCE in phi",
        description="""Frozen phi itself contains temporal ONCE operator.
phi = ONCE[0,*) a(x): snapshot at time i contains a(x) that held at some past time.
Tests frozen snapshot from a temporal formula.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = ONCE[0,*) a(x) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1)
@1 a(2) b(1) b(2)
@2 b(3)
@4 a(3) b(3)
@6""",
    ),

    FrzTest(
        num=83,
        name="FRZ with SINCE in phi",
        description="""Frozen phi contains SINCE temporal operator.
phi = a(x) SINCE[0,*) b(x): a(x) has held since b(x) became true.
Tests frozen snapshot from complex temporal constraint.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) SINCE[0,*) b(x)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 b(1) c(1)
@1 a(1) c(2)
@2 a(2) c(3)
@3 c(4) b(2)
@5""",
    ),

    FrzTest(
        num=84,
        name="FRZ with negation in phi",
        description="""Frozen phi uses negation.
phi = a(x) AND NOT b(x): snapshot contains a(x) that are not in b(x).
Tests frozen snapshot with difference semantics.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) AND NOT b(x)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) a(2) a(3) b(2) c(1) c(2) c(3)
@1 b(3) c(4)
@2 a(4) c(5)
@5""",
    ),

    FrzTest(
        num=85,
        name="FRZ with EXISTS in phi",
        description="""Frozen phi contains existential quantifier.
phi = EXISTS y. p(x,y): snapshot at time i contains x where p(x,y) holds for some y.
Tests frozen snapshot from quantified formula.""",
        signature="a(x:int,y:int)\nb(x:int)",
        formula="FRZ q(x) = (EXISTS y. a(x,y)) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1,10) a(1,20) a(2,30) b(1) b(2)
@1 a(1,40) b(3)
@2 a(3,50) b(1)
@4""",
    ),

    FrzTest(
        num=86,
        name="FRZ with comparison in phi",
        description="""Frozen phi includes numeric constraints.
phi = a(x) AND x > 2: snapshot filtered by constraint.
Tests frozen snapshot with value-based filtering.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = (a(x) AND x > 2) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) a(2) a(3) a(4) b(3) b(4)
@1 a(2) a(5) b(2) b(5)
@2 b(1)
@5""",
    ),

    FrzTest(
        num=87,
        name="FRZ with nested temporal in phi",
        description="""Frozen phi contains nested temporal operators.
phi = ONCE[0,*) (a(x) AND b(x)): conjunction that held in the past.
Tests frozen snapshot from complex temporal-logical formula.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (ONCE[0,*) (a(x) AND b(x))) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1) c(1)
@1 a(2) c(2)
@2 b(2) c(3)
@3 c(4)
@5 a(3) b(3) c(5)
@7""",
    ),

    FrzTest(
        num=88,
        name="FRZ with SINCE and negation in phi",
        description="""Frozen phi combines multiple operators: SINCE with AND NOT.
phi = (a(x) SINCE[0,*) b(x)) AND NOT c(x)
Tests snapshot from complex multi-operator frozen formula.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)\nd(x:int)",
        formula="FRZ q(x) = ((a(x) SINCE[0,*) b(x)) AND NOT c(x)) IN (d(x) AND ONCE[0,*) q(x))",
        log="""@0 b(1) d(1)
@1 a(1) d(2)
@2 a(1) c(1) d(3)
@3 d(4) b(2)
@5""",
    ),

    FrzTest(
        num=89,
        name="FRZ with quantifier and temporal in phi",
        description="""Frozen phi combines EXISTS with temporal operator.
phi = EXISTS y. ONCE[0,*) p(x,y)
Tests frozen snapshot from quantified temporal formula.""",
        signature="a(x:int,y:int)\nb(x:int)",
        formula="FRZ q(x) = (EXISTS y. ONCE[0,*) a(x,y)) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1,10) a(2,20) b(1) b(2)
@1 b(1)
@2 a(1,30) a(3,40) b(3)
@4""",
    ),

    FrzTest(
        num=90,
        name="FRZ with complex Boolean tree in phi",
        description="""Frozen phi has deep Boolean structure.
phi = (a(x) AND b(x)) OR (c(x) AND NOT d(x))
Tests frozen snapshot from complex nested Boolean formula.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)\nd(x:int)\ne(x:int)",
        formula="FRZ q(x) = ((a(x) AND b(x)) OR (c(x) AND NOT d(x))) IN (e(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1) c(2) d(2) e(1) e(2)
@1 a(2) c(3) d(3) e(3)
@2 b(2) c(2) e(2)
@4""",
    ),

    FrzTest(
        num=91,
        name="FRZ with ONCE and disjunction in phi",
        description="""Frozen phi: ONCE of a disjunction.
phi = ONCE[0,*) (a(x) OR b(x))
Tests frozen snapshot where temporal applies to disjunction.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (ONCE[0,*) (a(x) OR b(x))) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) c(1)
@1 b(2) c(2)
@2 c(3)
@4 a(3) c(4)
@6""",
    ),

    FrzTest(
        num=92,
        name="FRZ with multiple constraints in phi",
        description="""Frozen phi has multiple numeric constraints.
phi = a(x) AND x > 1 AND x < 4
Tests frozen snapshot with compound constraints.""",
        signature="a(x:int)\nb(x:int)",
        formula="FRZ q(x) = (a(x) AND x > 1 AND x < 4) IN (b(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) a(2) a(3) a(4) b(2) b(3)
@1 a(5) b(5)
@2 b(1)
@5""",
    ),

    FrzTest(
        num=93,
        name="FRZ with SINCE in both phi and psi",
        description="""Both frozen formula and psi use SINCE operator.
Tests interaction when both parts have temporal structure.""",
        signature="a(x:int)\nb(x:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) SINCE[0,*) b(x)) IN (c(x) SINCE[0,*) q(x))",
        log="""@0 b(1)
@1 a(1) c(1)
@2 a(1) c(2)
@3 c(3) b(2)
@5""",
    ),

    FrzTest(
        num=94,
        name="FRZ with complex multi-variable phi",
        description="""Frozen phi involves complex multi-variable relationships.
phi = a(x) AND EXISTS y. b(x,y) AND y > x
Tests frozen snapshot from quantified multi-variable formula.""",
        signature="a(x:int)\nb(x:int,y:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) AND EXISTS y. (b(x,y) AND y > x)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) b(1,2) b(1,3) a(2) b(2,4) c(1) c(2)
@1 b(1,5) c(3)
@2 c(4)
@5""",
    ),

    FrzTest(
        num=95,
        name="FRZ with negated quantifier in phi",
        description="""Frozen phi uses negated existential.
phi = a(x) AND NOT EXISTS y. b(x,y)
Tests frozen snapshot with negated quantified constraint.""",
        signature="a(x:int)\nb(x:int,y:int)\nc(x:int)",
        formula="FRZ q(x) = (a(x) AND NOT EXISTS y. b(x,y)) IN (c(x) AND ONCE[0,*) q(x))",
        log="""@0 a(1) a(2) a(3) b(2,1) c(1) c(3)
@1 b(1,2) c(2)
@2 c(4)
@5""",
    ),
]

if __name__ == "__main__":
    for test in tests:
        create_test_dir(test)
    print(f"\nGenerated {len(tests)} complex phi tests (frz80-frz95)")
