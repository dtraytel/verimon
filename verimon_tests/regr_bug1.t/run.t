Regression test for bug1: unsound filter-map fusion of a projection (EXISTS)
into a temporal operator (ONCE).

The formula is (EXISTS y. ONCE[0,1] (p(y) AND y > 0)).
Log: @0 p(14); @1 p(5); @2 p(0);

At tp2 the only current tuple p(0) fails the filter y>0, but ONCE[0,1] still
sees tp1's p(5) which satisfies it. Before the fix MonPoly fused the EXISTS
projection into the ONCE auxiliary and removed the shared image () via set
difference when p(14) left the window, incorrectly suppressing tp2.

Both monitors must output true at all three time points.

  $ echo '(EXISTS y. ONCE [0, 1] (p(y) AND y > 0))' > f.mfotl
  $ monpoly -sig bug.sig -formula f.mfotl -log bug1.log
  @0 (time point 0): true
  @1 (time point 1): true
  @2 (time point 2): true
  $ monpoly -verified -sig bug.sig -formula f.mfotl -log bug1.log
  @0 (time point 0): true
  @1 (time point 1): true
  @2 (time point 2): true
