Shadowing (LET + FRZ): LET q(x) = a(x) IN FRZ q(x) = q(x) IN q(x) AND b(x).
In phi, q resolves to the outer LET-bound q = a(x); frozen snapshot = a(x) at timepoint i.
In psi, the frozen q is intersected with b(x).
  $ monpoly -verified -sig frz11.sig -formula frz11.mfotl -log frz11.log
  @0 (time point 0): (2)
  @1 (time point 1): (4)
  $ monpoly -sig frz11.sig -formula frz11.mfotl -log frz11.log -nofilteremptytp
  @0 (time point 0): (2)
  @1 (time point 1): (4)
