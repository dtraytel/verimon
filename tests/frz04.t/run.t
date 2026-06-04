FRZ with empty timepoints: at time 0 and 2 the frozen snapshot of a is empty,
so q is empty and psi produces no output. Only time 1 has a(1).
  $ monpoly -sig frz04.sig -formula frz04.mfotl -log frz04.log -verified
  @1 (time point 1): (1)
  $ monpoly -sig frz04.sig -formula frz04.mfotl -log frz04.log -nofilteremptytp
  @1 (time point 1): (1)
