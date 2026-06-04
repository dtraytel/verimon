Two FRZ under AND: (FRZ q(x) = a(x) IN q(x)) AND (FRZ r(x) = b(x) IN r(x)).
Both FRZ expressions evaluate independently; result is their natural join.
At tp 0: q={1}, r={1}; join={1}. At tp 1: q={2}, r={3}; join empty (disjoint). No tp 2 output.
  $ monpoly -sig frz26.sig -formula frz26.mfotl -log frz26.log -verified
  @0 (time point 0): (1)
  $ monpoly -sig frz26.sig -formula frz26.mfotl -log frz26.log -nofilteremptytp
  @0 (time point 0): (1)
