Static psi with existential: FRZ q(x) = a(x) IN EXISTS x. q(x).
At time 0: q={1}, non-empty, so EXISTS is true. At time 1: q empty, no output.
At time 2: q={3}, EXISTS is true again.
  $ verimon -sig frz15.sig -formula frz15.mfotl -log frz15.log
  @0 (time point 0): true
  @2 (time point 2): true
