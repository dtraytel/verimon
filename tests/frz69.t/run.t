Test FRZ stress case.
  $ monpoly -sig frz69.sig -formula frz69.mfotl -log frz69.log -nofilteremptytp -verified
  @0 (time point 0): (1)
  @3 (time point 2): (2)
  $ monpoly -sig frz69.sig -formula frz69.mfotl -log frz69.log -nofilteremptytp
  @0 (time point 0): (1)
  @3 (time point 2): (2)
