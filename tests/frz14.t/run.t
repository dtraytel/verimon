Static psi with OR: FRZ q(x) = a(x) IN q(x) OR b(x).
At time 0: q={1}, b={2}; union={1,2}. At time 1: q empty, b={3}; output {3}.
At time 2: q={4}, b={4}; union={4}. At time 3: both empty; no output.
  $ verimon -sig frz14.sig -formula frz14.mfotl -log frz14.log
  @0 (time point 0): (1) (2)
  @1 (time point 1): (3)
  @2 (time point 2): (4)
