FRZ with NEXT: even under a future operator, q remains frozen to outer time i.
At outer time 0: q is frozen to a at time 0 = {1}; NEXT looks ahead but q is
still {1}, so output is (1). Similarly at time 1: q frozen to {2}.
  $ verimon -sig frz05.sig -formula frz05.mfotl -log frz05.log
  @0 (time point 0): (1)
  @1 (time point 1): (2)
