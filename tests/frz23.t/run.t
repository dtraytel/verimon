Bounded ONCE[0,3] in psi (per-instance): FRZ q(x) = a(x) IN ONCE[0,3] q(x).
q is frozen per outer tp; inner ONCE[0,3] sees only the frozen constant q.
Timestamps are 0,2,4,6 so the window [0,3] covers only the current tp (q is constant).
At each tp with non-empty a, ONCE[0,3] q immediately holds for those values.
  $ verimon -sig frz23.sig -formula frz23.mfotl -log frz23.log
  @0 (time point 0): (1)
  @2 (time point 1): (2)
  @4 (time point 2): (3)
