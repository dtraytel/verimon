Shadowing (free relation): FRZ q(x) = q(x) IN q(x) where q is also declared in the signature.
In phi, q resolves to the free DB relation; the frozen snapshot in psi equals q at that timepoint.
Previously this formula was rejected; it must now run correctly.
  $ monpoly -verified -sig frz09.sig -formula frz09.mfotl -log frz09.log
  @0 (time point 0): (1)
  @1 (time point 1): (2)
