Sometimes-empty phi: FRZ q(x) = a(x) IN ONCE[0,*) q(x).
Alternating empty and non-empty phi: only timepoints where phi is non-empty produce output.
At tp 0: q={1}, ONCE q immediately holds; output (1). At tp 1: q empty, no output.
At tp 2: q={3}, ONCE q immediately holds; output (3). At tp 3: q empty, no output.
  $ verimon -sig frz22.sig -formula frz22.mfotl -log frz22.log
  @0 (time point 0): (1)
  @2 (time point 2): (3)
