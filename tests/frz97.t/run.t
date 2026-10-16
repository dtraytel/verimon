Adversarial: ALL time-points share timestamp 0, so every future-op instance window
[ts_i, ts_i] spans the whole trace (extreme d=0).  Native must match verified.
  $ verimon -sig frz97.sig -formula frz97.mfotl -log frz97.log
  @0 (time point 0): (1,5) (1,6) (1,7) (1,8) (1,9)
  @0 (time point 1): (2,6) (2,7) (2,8) (2,9)
  @0 (time point 3): (3,8) (3,9)
