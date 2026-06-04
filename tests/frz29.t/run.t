Temporal phi (NEXT) with per-instance ONCE psi: FRZ q(x) = NEXT[0,1] a(x) IN ONCE[0,*) q(x).
phi is future-looking; q at outer tp i is a at tp i+1; psi is ONCE q (per-instance).
At tp 0: q = a(tp1) = {2}; inner ONCE q immediately holds; output (2).
At tp 1: q = a(tp2) = {3}; inner ONCE q holds; output (3).
At tp 2: q = a(tp3) = {}; q empty, ONCE never holds; no output.
  $ monpoly -sig frz29.sig -formula frz29.mfotl -log frz29.log -verified
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  $ monpoly -sig frz29.sig -formula frz29.mfotl -log frz29.log -nofilteremptytp
  @0 (time point 0): (2)
  @1 (time point 1): (3)
