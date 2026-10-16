Phase-3 PREV windowing: big timestamp gaps (0->9, 10->17) put the immediate
predecessor time-point outside the [ts-5,ts] window, and repeated ts=10 exercises
the window edge.  Native (trimmed) must match the verified monitor byte-for-byte.
  $ verimon -sig frz100.sig -formula frz100.mfotl -log frz100.log
  @1 (time point 1): (2,1)
  @2 (time point 2): (1,2)
  @10 (time point 4): (1,3) (2,3)
