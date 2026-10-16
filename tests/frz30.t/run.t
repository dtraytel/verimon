Long trace (8 timepoints) with static psi: FRZ q(x) = a(x) IN q(x) AND b(x).
Checks correctness across many timepoints with varying a and b, including empty tps.
tp 0: q={1,2}, b={2}; out {2}. tp 1: q={3}, b={3}; out {3}. tp 2: q empty; no out.
tp 3: q={4,5}, b={5}; out {5}. tp 4: q={6}, b={6}; out {6}. tp 5: q empty; no out.
tp 6: q={7}, b={7}; out {7}. tp 7: q empty; no out.
  $ verimon -sig frz30.sig -formula frz30.mfotl -log frz30.log
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  @3 (time point 3): (5)
  @4 (time point 4): (6)
  @6 (time point 6): (7)
