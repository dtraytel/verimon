UNTIL[0,2] with live predicate b (per-instance, future operator): FRZ q(x) = a(x) IN q(x) UNTIL[0,2] b(x).
q is frozen per outer tp; inner UNTIL sees q as constant and b from the real database.
tp 0: q={1,2}, b holds at ts=1(x=1) and ts=2(x=2) within [0,2]; output (1)(2).
tp 1: q={} (a absent), b(1) at ts=1 within [1,3] with zero-lag; output (1).
tp 2: q={} (a absent), b(2) at ts=2 within [2,4] with zero-lag; output (2).
  $ monpoly -sig frz33.sig -formula frz33.mfotl -log frz33.log -verified
  @0 (time point 0): (1) (2)
  @1 (time point 1): (1)
  @2 (time point 2): (2)
  $ monpoly -sig frz33.sig -formula frz33.mfotl -log frz33.log -nofilteremptytp
  @0 (time point 0): (1) (2)
  @1 (time point 1): (1)
  @2 (time point 2): (2)
