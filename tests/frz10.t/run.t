Shadowing (nested FRZ): FRZ q(x) = a(x) IN FRZ q(x) = b(x) IN q(x).
The inner FRZ binds q to b(x), shadowing the outer binding to a(x) inside the innermost psi.
Output must be b(x) at each timepoint, not a(x).
  $ monpoly -verified -sig frz10.sig -formula frz10.mfotl -log frz10.log
  @0 (time point 0): (2)
  @1 (time point 1): (4)
