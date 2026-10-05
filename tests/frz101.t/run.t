Phase-3 NEXT windowing: repeated ts=0 and a gap (3->9) beyond the [0,5] window.
Native (trimmed, window starts at the diagonal ts) must match the verified monitor.
  $ verimon -sig frz101.sig -formula frz101.mfotl -log frz101.log
  @0 (time point 0): (1,2)
  @0 (time point 1): (2,1)
  @9 (time point 3): (3,1)
  @10 (time point 4): (1,4)
