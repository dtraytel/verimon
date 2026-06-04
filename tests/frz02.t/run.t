FRZ with ONCE: q is frozen to a(x) at outer time i, so ONCE q(x) under j uses
the snapshot from outer time i for all inner times j. At time 2 and 3 the frozen
snapshot is empty, producing no output.
  $ monpoly -sig frz02.sig -formula frz02.mfotl -log frz02.log -verified
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  $ monpoly -sig frz02.sig -formula frz02.mfotl -log frz02.log -nofilteremptytp
  @0 (time point 0): (1)
  @1 (time point 1): (2)
