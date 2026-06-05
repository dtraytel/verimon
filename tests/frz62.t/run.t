Test FRZ stress case.
  $ monpoly -sig frz62.sig -formula frz62.mfotl -log frz62.log -nofilteremptytp -verified
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  @2 (time point 2): (3)
  @3 (time point 3): (4)
  @5 (time point 4): (5)
  @7 (time point 5): (6)
  $ monpoly -sig frz62.sig -formula frz62.mfotl -log frz62.log -nofilteremptytp
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  @2 (time point 2): (3)
  @3 (time point 3): (4)
  @5 (time point 4): (5)
  @7 (time point 5): (6)
