Static psi with equality filter: FRZ q(x) = a(x) IN EXISTS x. (q(x) AND x > 0).
At each outer tp, frozen q is filtered by x > 0; EXISTS makes this a boolean result.
At tp 0: q={1,2}, both positive => true. At tp 1: q={0} (zero), x>0 fails => false.
At tp 2: q={3}, positive => true. At tp 3: q empty => false.
  $ monpoly -sig frz32.sig -formula frz32.mfotl -log frz32.log -verified
  @0 (time point 0): true
  @2 (time point 2): true
  $ monpoly -sig frz32.sig -formula frz32.mfotl -log frz32.log -nofilteremptytp
  @0 (time point 0): true
  @2 (time point 2): true
