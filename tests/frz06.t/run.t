Nested FRZ: two independently frozen predicates q and r.
At time 0: q={1}, r={1}, intersection={1}.
At time 1: q={2}, r={3}, intersection={}; no output.
At time 2: both empty; no output.
  $ monpoly -sig frz06.sig -formula frz06.mfotl -log frz06.log -verified
  @0 (time point 0): (1)
  $ monpoly -sig frz06.sig -formula frz06.mfotl -log frz06.log -nofilteremptytp
  @0 (time point 0): (1)
