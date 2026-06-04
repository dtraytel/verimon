Basic FRZ: frozen predicate q(x) is bound to a(x) at each outer timepoint i.
At time 0: a={1}, so q={1}; at time 1: a={2}, so q={2}; at time 2: a={}, no output.
  $ monpoly -sig frz01.sig -formula frz01.mfotl -log frz01.log -verified
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  $ monpoly -sig frz01.sig -formula frz01.mfotl -log frz01.log -nofilteremptytp
  @0 (time point 0): (1)
  @1 (time point 1): (2)
