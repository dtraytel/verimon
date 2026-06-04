LET inside psi: FRZ q(x) = a(x) IN LET r(x) = b(x) IN q(x) AND r(x).
q is frozen to a at outer tp; r is a live LET binding for b inside psi.
At tp 0: q={1,2}, r=b={2}; q AND r={2}. At tp 1: q={3}, r=b={3,4}; q AND r={3}.
  $ monpoly -sig frz25.sig -formula frz25.mfotl -log frz25.log -verified
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  $ monpoly -sig frz25.sig -formula frz25.mfotl -log frz25.log -nofilteremptytp
  @0 (time point 0): (2)
  @1 (time point 1): (3)
