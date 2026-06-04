UNTIL[0,5] in psi with live predicates (future operator + live b on both sides).
FRZ q(x) = a(x) IN (a(x) AND (b(y) UNTIL[0,5] ((q(x) AND b(y)) AND 0 < x))).
At outer tp 0: q={3}, a(3) holds; b(y) UNTIL (q(3) AND b(y)) holds for y=7 at tp0
(right side true immediately with q(3),b(7)); output (3,7).
At outer tp 5 (tp index 4): q={4}, a(4) holds; right side q(4) AND b(9) true at tp5; output (4,9).
Regression test: per-instance UNTIL must drive from neval0 in lockstep with its lookahead.
  $ monpoly -sig frz35.sig -formula frz35.mfotl -log frz35.log -verified
  @0 (time point 0): (3,7)
  @5 (time point 4): (4,9)
  $ monpoly -sig frz35.sig -formula frz35.mfotl -log frz35.log -nofilteremptytp
  @0 (time point 0): (3,7)
  @5 (time point 4): (4,9)
