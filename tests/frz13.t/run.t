Static psi with negation: FRZ q(x) = a(x) IN b(x) AND NOT q(x).
At time 0: q={1}, b={1,2}; b-minus-q={2}. At time 1: q={3}, b={3,4}; b-minus-q={4}.
  $ monpoly -sig frz13.sig -formula frz13.mfotl -log frz13.log -verified
  @0 (time point 0): (2)
  @1 (time point 1): (4)
  $ monpoly -sig frz13.sig -formula frz13.mfotl -log frz13.log -nofilteremptytp
  @0 (time point 0): (2)
  @1 (time point 1): (4)
