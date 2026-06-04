Triple nesting: FRZ q = a IN FRZ r = b IN FRZ s = c IN q(x) AND r(x) AND s(x).
Three independently frozen predicates; psi is their 3-way intersection.
At tp 0: q={1}, r={1}, s={1}; intersection={1}. At tp 1: q={2}, r={2}, s={3}; empty.
  $ monpoly -sig frz27.sig -formula frz27.mfotl -log frz27.log -verified
  @0 (time point 0): (1)
  $ monpoly -sig frz27.sig -formula frz27.mfotl -log frz27.log -nofilteremptytp
  @0 (time point 0): (1)
