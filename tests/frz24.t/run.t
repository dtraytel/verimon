SINCE in psi (per-instance): FRZ q(x) = a(x) IN (b(x) SINCE[0,*) q(x)).
q is the frozen snapshot of a at outer tp i; inner SINCE evaluates with this constant q.
At tp 0: q={1}, b(1) holds and q(1) just held (SINCE trivially true at i=0); output (1).
At tp 1: q empty (a absent), SINCE never has q holding, so no output.
At tp 2: q={2}, b(2) holds and q(2) holds at i=0; output (2). At tp 3: q empty, no output.
  $ verimon -sig frz24.sig -formula frz24.mfotl -log frz24.log
  @0 (time point 0): (1)
  @2 (time point 2): (2)
