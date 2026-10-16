Stress test for trimmed future-operator FRZ replay: repeated timestamps (several
time-points share a timestamp) exercise the d=0 window edge, where the per-instance
window [ts_i, ts_i] spans multiple time-points.  Native (-nofilteremptytp) must match
the verified monitor byte-for-byte.
  $ verimon -sig frz96.sig -formula frz96.mfotl -log frz96.log
  @0 (time point 0): (1,10) (1,11) (1,20) (1,21) (1,30)
  @2 (time point 2): (2,20) (2,21) (2,30) (2,40)
  @2 (time point 4): (3,30) (3,40)
  @7 (time point 6): (4,40)
