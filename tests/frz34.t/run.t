EVENTUALLY[0,5] in psi with live predicates (the rq4_rule17 pattern, future operator + live b).
FRZ q(x) = a(x) IN (a(x) AND (EVENTUALLY[0,5] ((q(x) AND b(y)) AND 0 < x))).
At outer tp 0: q={3}, a(3) holds; EVENTUALLY[0,5] needs q(3) AND b(y) within ts 0..5;
b at tp0(7),tp1(8),tp5(9) all within window; output (3,7)(3,8)(3,9).
At outer tp 5 (tp index 4): q={4}, a(4) holds; b at tp5(9),tp6(2) within window; output (4,2)(4,9).
Regression test: per-instance EVENTUALLY must drive each instance from neval0 to stay in
lockstep with its internal lookahead, so instances for tp>0 produce output (not just tp=0).
  $ monpoly -sig frz34.sig -formula frz34.mfotl -log frz34.log -verified
  @0 (time point 0): (3,7) (3,8) (3,9)
  @5 (time point 4): (4,2) (4,9)
  $ monpoly -sig frz34.sig -formula frz34.mfotl -log frz34.log -nofilteremptytp
  @0 (time point 0): (3,7) (3,8) (3,9)
  @5 (time point 4): (4,2) (4,9)
