Test FRZ stress case.
  $ monpoly -sig frz63.sig -formula frz63.mfotl -log frz63.log -nofilteremptytp -verified
  @0 (time point 0): (1,2,3)
  @1 (time point 1): (2,3,4)
  $ monpoly -sig frz63.sig -formula frz63.mfotl -log frz63.log -nofilteremptytp
  @0 (time point 0): (1,2,3)
  @1 (time point 1): (2,3,4)
