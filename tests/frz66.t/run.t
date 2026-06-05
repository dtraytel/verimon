Test FRZ stress case.
  $ monpoly -sig frz66.sig -formula frz66.mfotl -log frz66.log -nofilteremptytp -verified
  @0 (time point 0): (10)
  @1 (time point 1): (20)
  @2 (time point 2): (30)
  $ monpoly -sig frz66.sig -formula frz66.mfotl -log frz66.log -nofilteremptytp
  @0 (time point 0): (10)
  @1 (time point 1): (20)
  @2 (time point 2): (30)
