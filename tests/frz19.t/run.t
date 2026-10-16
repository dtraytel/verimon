Temporal phi with SINCE: FRZ q(x) = (b(x) SINCE[0,*) a(x)) IN q(x).
phi accumulates x values where b has held since a was last true.
At time 0: a(1) true, so SINCE true for x=1; q={1}. At time 1: b(1),b only, and a(2)
restarts; q={1,2}. At time 2: b(1),b(2) hold, a absent, SINCE still holds; q={1,2}.
At time 3: no new events, SINCE still holds from time 2; q={1,2}.
  $ verimon -sig frz19.sig -formula frz19.mfotl -log frz19.log
  @0 (time point 0): (1)
  @1 (time point 1): (1) (2)
  @2 (time point 2): (1) (2)
