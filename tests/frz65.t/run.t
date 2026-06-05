Test FRZ stress case.
  $ monpoly -sig frz65.sig -formula frz65.mfotl -log frz65.log -nofilteremptytp -verified
  @0 (time point 0): (1)
  @2 (time point 2): (3)
  @4 (time point 4): (5)
  $ monpoly -sig frz65.sig -formula frz65.mfotl -log frz65.log -nofilteremptytp
  @0 (time point 0): (1)
  @2 (time point 2): (3)
  @4 (time point 4): (5)
