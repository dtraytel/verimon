Frozen q used twice with different vars: FRZ q(x) = a(x) IN EXISTS y. (q(x) AND q(y) AND b(y)).
q appears for both x and y; psi checks that x is in q and there exists some y in q that b(y) holds.
At tp 0: q={1,2}, b={2}; y=2 is in q and b(2) holds, so x can be 1 or 2; output {1,2}.
At tp 1: q={3}, b={1}; 1 is not in q, so no y in q with b(y); no output.
  $ verimon -sig frz28.sig -formula frz28.mfotl -log frz28.log
  @0 (time point 0): (1) (2)
