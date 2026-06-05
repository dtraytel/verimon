# FRZ Complex Phi Tests - 16 Tests

## Overview

A comprehensive set of 16 tests focusing on **complex frozen formulas (phi)**, where the snapshot itself is computed from sophisticated logical and temporal constructs.

**Status**: ✅ **All 16 tests PASS** - Both native and verified implementations match perfectly

## Test Suite (frz80-frz95)

### 1. frz80: Conjunction in Phi
**Formula**: `FRZ q(x) = (a(x) AND b(x)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi is a conjunction
- Snapshot contains only tuples in both a and b
- Tests intersection semantics in frozen formula

### 2. frz81: Disjunction in Phi
**Formula**: `FRZ q(x) = (a(x) OR b(x)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi uses OR operator
- Snapshot contains union of a and b
- Tests union semantics in frozen formula

### 3. frz82: ONCE Temporal in Phi
**Formula**: `FRZ q(x) = ONCE[0,*) a(x) IN (b(x) AND ONCE[0,*) q(x))`
- Frozen phi contains ONCE operator
- Snapshot at time i: "a(x) that held at some past time"
- Tests temporal past within frozen formula

### 4. frz83: SINCE Temporal in Phi
**Formula**: `FRZ q(x) = (a(x) SINCE[0,*) b(x)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi uses SINCE operator
- Snapshot reflects "a has held since b became true"
- Tests complex temporal constraint in frozen formula

### 5. frz84: Negation in Phi
**Formula**: `FRZ q(x) = (a(x) AND NOT b(x)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi uses negation
- Snapshot is set difference: a \ b
- Tests safe negation in frozen formula

### 6. frz85: EXISTS Quantifier in Phi
**Formula**: `FRZ q(x) = (EXISTS y. a(x,y)) IN (b(x) AND ONCE[0,*) q(x))`
- Frozen phi contains existential quantifier
- Snapshot: "x where ∃y. a(x,y)"
- Tests quantified formula in frozen context

### 7. frz86: Numeric Constraints in Phi
**Formula**: `FRZ q(x) = (a(x) AND x > 2) IN (b(x) AND ONCE[0,*) q(x))`
- Frozen phi includes value constraints
- Snapshot filtered by comparison
- Tests constraint evaluation in frozen formula

### 8. frz87: Nested Temporal in Phi
**Formula**: `FRZ q(x) = (ONCE[0,*) (a(x) AND b(x))) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi has nested temporal-logical structure
- Tests complex formula composition in snapshot

### 9. frz88: SINCE with Negation in Phi
**Formula**: `FRZ q(x) = ((a(x) SINCE[0,*) b(x)) AND NOT c(x)) IN (d(x) AND ONCE[0,*) q(x))`
- Multiple operators combined: temporal AND negation
- Tests complex multi-operator frozen formula

### 10. frz89: EXISTS with Temporal in Phi
**Formula**: `FRZ q(x) = (EXISTS y. ONCE[0,*) a(x,y)) IN (b(x) AND ONCE[0,*) q(x))`
- Frozen phi combines quantification and temporality
- Tests interaction of quantifier and temporal operator

### 11. frz90: Complex Boolean Tree in Phi
**Formula**: `FRZ q(x) = ((a(x) AND b(x)) OR (c(x) AND NOT d(x))) IN (e(x) AND ONCE[0,*) q(x))`
- Deep nested Boolean structure
- Tests complex logical formula evaluation

### 12. frz91: ONCE of Disjunction in Phi
**Formula**: `FRZ q(x) = (ONCE[0,*) (a(x) OR b(x))) IN (c(x) AND ONCE[0,*) q(x))`
- Temporal operator applied to disjunction
- Tests operator precedence and scope in frozen formula

### 13. frz92: Multiple Constraints in Phi
**Formula**: `FRZ q(x) = (a(x) AND x > 1 AND x < 4) IN (b(x) AND ONCE[0,*) q(x))`
- Multiple numeric constraints chained
- Tests compound constraint filtering

### 14. frz93: SINCE in Both Phi and Psi
**Formula**: `FRZ q(x) = (a(x) SINCE[0,*) b(x)) IN (c(x) SINCE[0,*) q(x))`
- Temporal structure in both frozen and outer formula
- Tests interaction between frozen and outer temporal operators

### 15. frz94: Complex Multi-Variable Phi
**Formula**: `FRZ q(x) = (a(x) AND EXISTS y. (b(x,y) AND y > x)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi with quantified multi-variable constraints
- Tests complex variable relationships in frozen formula

### 16. frz95: Negated Quantifier in Phi
**Formula**: `FRZ q(x) = (a(x) AND NOT EXISTS y. b(x,y)) IN (c(x) AND ONCE[0,*) q(x))`
- Frozen phi with negated existential
- Tests safe negation of quantified formula

## Coverage Summary

### Logical Operators
- ✅ Conjunction (AND)
- ✅ Disjunction (OR)
- ✅ Negation (NOT)
- ✅ Complex Boolean trees

### Temporal Operators in Phi
- ✅ ONCE (past temporal)
- ✅ SINCE (past temporal with trigger)
- ✅ Nested temporal constructs

### Quantifiers in Phi
- ✅ Existential (EXISTS)
- ✅ Negated quantifiers (NOT EXISTS)
- ✅ Multi-variable quantification

### Constraints in Phi
- ✅ Numeric comparisons (>, <, etc.)
- ✅ Single constraints
- ✅ Compound constraints

### Combinations
- ✅ Temporal with negation
- ✅ Temporal with quantifiers
- ✅ Multiple operators nested

## Test Results

| Test | Operators | Status |
|------|-----------|--------|
| frz80 | AND | ✅ PASS |
| frz81 | OR | ✅ PASS |
| frz82 | ONCE | ✅ PASS |
| frz83 | SINCE | ✅ PASS |
| frz84 | NOT | ✅ PASS |
| frz85 | EXISTS | ✅ PASS |
| frz86 | Constraints | ✅ PASS |
| frz87 | Nested temporal | ✅ PASS |
| frz88 | SINCE + NOT | ✅ PASS |
| frz89 | EXISTS + ONCE | ✅ PASS |
| frz90 | Complex Boolean | ✅ PASS |
| frz91 | ONCE(OR) | ✅ PASS |
| frz92 | Multi-constraint | ✅ PASS |
| frz93 | SINCE(both) | ✅ PASS |
| frz94 | Multi-var EXISTS | ✅ PASS |
| frz95 | NOT EXISTS | ✅ PASS |

**Summary**: 16/16 PASS (100%)

## Key Insights

### 1. MonPoly Handles Complex Phi Well
All complex phi formulas are correctly evaluated and their snapshots properly maintained across timepoints.

### 2. Temporal Operators Compose Correctly
Combining temporal operators with logical operators in phi works as expected (frz82, frz83, frz87-89, frz91, frz93).

### 3. Quantification Works Properly
Existential quantifiers in phi produce correct frozen snapshots (frz85, frz89, frz94, frz95).

### 4. Constraint Evaluation is Correct
Numeric constraints properly filter the frozen snapshot (frz86, frz92).

### 5. Negation is Safe
Negation works correctly in phi when safe (frz84, frz88, frz95).

## Next Steps

These tests demonstrate that MonPoly correctly handles even very complex frozen formulas. Future testing could explore:

1. **Deeper nesting** of temporal operators in phi
2. **More complex quantifier patterns** (nested EXISTS, universal quantifiers)
3. **Unusual combinations** like SINCE in both phi and outer formula
4. **Performance tests** with large frozen snapshots from complex phi

## Files

- Tests: `tests/frz80.t/` through `tests/frz95.t/`
- Generator: `generate_frz_complex_phi_tests.py`
- Documentation: This file
