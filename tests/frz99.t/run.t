Adversarial: bounded-past (ONCE[0,3]) nested inside a future operator (EVENTUALLY[0,5])
gives a non-zero past_reach window under a future root.  Native must match verified.
  $ verimon -sig frz99.sig -formula frz99.mfotl -log frz99.log
  @0 (time point 0): (1,1) (1,2)
  @2 (time point 1): (2,2) (2,3)
  @5 (time point 3): (3,1) (3,3)
  @9 (time point 5): (4,4)
