2-ary frozen predicate: FRZ q(x,y) = e(x,y) IN q(x,y).
Frozen snapshot captures binary tuples at each outer timepoint.
At time 0: e={(1,2),(3,4)}. At time 1: e={(5,6)}. At time 2: empty.
  $ verimon -sig frz16.sig -formula frz16.mfotl -log frz16.log
  @0 (time point 0): (1,2) (3,4)
  @1 (time point 1): (5,6)
