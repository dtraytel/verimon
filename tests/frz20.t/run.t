Temporal phi with NEXT (static psi): FRZ q(x) = NEXT[0,1] a(x) IN q(x).
phi is NEXT a, so q at outer tp i is a at tp i+1; psi = q(x) is static.
At outer tp 0: NEXT a = a at tp 1 = {2}; q={2}; output (2).
At outer tp 1: NEXT a = a at tp 2 = {3}; q={3}; output (3).
At outer tp 2: NEXT a = a at tp 3 = {}; q empty; no output.
  $ monpoly -sig frz20.sig -formula frz20.mfotl -log frz20.log -verified
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  $ monpoly -sig frz20.sig -formula frz20.mfotl -log frz20.log -nofilteremptytp
  @0 (time point 0): (2)
  @1 (time point 1): (3)
