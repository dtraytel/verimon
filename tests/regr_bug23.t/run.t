Regression tests for bug2 and bug3: MonPoly's empty-time-point filter
incorrectly classified formulas containing tp/ts/tpts as filterable. These
special predicates hold at every time point — including empty ones — so they
must never be treated as false on an empty time point.

Log has empty time points at @1 and @3 (between the temp-fact time points).

Bug2: (ONCE (0,2) temp(x)) AND tp(t)
Before fix: MonPoly output nothing (skipped @1,@3 as "empty").
After fix:  satisfactions are correctly reported at @1 and @3.

  $ echo '((ONCE (0,2) temp(x)) AND tp(t))' > f.mfotl
  $ verimon -sig bug.sig -formula f.mfotl -log bug2.log
  @1 (time point 1): (5,1)
  @3 (time point 3): (10,3)

Bug3: (EVENTUALLY (0,2) temp(x)) AND tp(t)
Before fix: MonPoly reported results at @2,@4 (shifted — wrong time points)
instead of @1,@3.
After fix:  satisfactions correctly appear at @1 and @3.

  $ echo '((EVENTUALLY (0,2) temp(x)) AND tp(t))' > f.mfotl
  $ verimon -sig bug.sig -formula f.mfotl -log bug3.log
  @1 (time point 1): (10,1)
  @3 (time point 3): (8,3)
