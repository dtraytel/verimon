PREV[0,*) in psi (per-instance mode): FRZ q(x) = a(x) IN PREV[0,1000] q(x).
q is frozen per outer tp; PREV looks at q at the previous inner timepoint.
Since q is constant, PREV(q) = q at every tp except tp=0 (no previous exists).
At tp 0: PREV has no previous => no output. At tp 1: q={2}, PREV(q)={2}.
At tp 2: q={} (a absent), PREV(q)={} => no output.
  $ monpoly -sig frz31.sig -formula frz31.mfotl -log frz31.log -verified
  @1 (time point 1): (2)
  $ monpoly -sig frz31.sig -formula frz31.mfotl -log frz31.log -nofilteremptytp
  @1 (time point 1): (2)
