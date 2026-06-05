Triple-nested FRZ regression test.
FRZ q(x) = a(x) IN FRZ r(y) = b(y) IN FRZ s(z) = c(z) IN (ONCE[0,*) (q(x) AND r(y) AND s(z))).
At outer tp 0: q={1}, r={2}, s={3}; ONCE sees q(1) AND r(2) AND s(3); output (1,2,3).
Regression test: a nested per-instance FRZ must inherit its parent's db history so that
a grandchild live predicate (here c(z), the phi of the innermost FRZ) is seeded for the
timepoints that elapsed before the enclosing instance was created.  Previously this crashed
with an assertion failure in the native engine (only at triple or deeper nesting).
  $ monpoly -sig frz_bug_triple_nest.sig -formula frz_bug_triple_nest.mfotl -log frz_bug_triple_nest.log -nofilteremptytp -verified
  @0 (time point 0): (1,2,3)
  $ monpoly -sig frz_bug_triple_nest.sig -formula frz_bug_triple_nest.mfotl -log frz_bug_triple_nest.log -nofilteremptytp
  @0 (time point 0): (1,2,3)
