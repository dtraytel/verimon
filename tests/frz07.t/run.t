FRZ where phi is temporal: phi = ONCE a(x) accumulates all a values seen up to
outer time i. At time 0: q={1}. At time 1: q={1,2}. At times 2 and 3: q={1,2}
(no new a events, but accumulation is preserved from the past).
  $ verimon -sig frz07.sig -formula frz07.mfotl -log frz07.log
  @0 (time point 0): (1)
  @1 (time point 1): (1) (2)
  @2 (time point 2): (1) (2)
  @3 (time point 3): (1) (2)
