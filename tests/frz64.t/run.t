Test FRZ stress case.
  $ monpoly -sig frz64.sig -formula frz64.mfotl -log frz64.log -nofilteremptytp -verified
  @0 (time point 0): (1) (2)
  @2 (time point 2): (3)
  $ monpoly -sig frz64.sig -formula frz64.mfotl -log frz64.log -nofilteremptytp
  @0 (time point 0): (1) (2)
  @2 (time point 2): (3)
