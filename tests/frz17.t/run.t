2-ary frozen pred with static psi join: FRZ q(x,y) = e(x,y) IN EXISTS x. (q(x,y) AND f(y)).
Freezes edge relation e(x,y); psi joins with live f(y) and projects out x.
At time 0: e={(1,10),(2,20)}, f={10}; y=10 has a matching x=1, output (10).
At time 1: e={(3,30)}, f={30,40}; y=30 matches, output (30).
  $ verimon -sig frz17.sig -formula frz17.mfotl -log frz17.log
  @0 (time point 0): (10)
  @1 (time point 1): (30)
