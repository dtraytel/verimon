EVENTUALLY[0,2] in psi (per-instance, no live predicates): FRZ q(x) = a(x) IN EVENTUALLY[0,2] q(x).
Per-instance mode drives from neval0; q is constant so EVENTUALLY holds immediately at its outer tp.
At tp 0: q={1}, EVENTUALLY finds q at ts=0 in [0,2] => (1). At tp 1: q empty => false.
At tp 2: q={2}, EVENTUALLY finds q at ts=2 in [2,4] => (2). At tp 3: q empty.
  $ monpoly -sig frz33.sig -formula frz33.mfotl -log frz33.log -verified
  @0 (time point 0): (1)
  @2 (time point 2): (2)
  $ monpoly -sig frz33.sig -formula frz33.mfotl -log frz33.log -nofilteremptytp
  @0 (time point 0): (1)
  @2 (time point 2): (2)
