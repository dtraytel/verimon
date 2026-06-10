Regression test for empty-time-point filtering with the special predicates
tp/ts/tpts (bug2/bug3). These predicates hold at every time point, including
empty ones, so MonPoly must not skip empty time points for formulas that
depend on them. Each formula must agree across MonPoly, VeriMon, and
VeriMon -no_mw. The trace deliberately contains empty time points (@1,@3,@5).

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   monpoly                  -sig et.sig -formula f.mfotl -log et.log > m.txt  2>/dev/null
  >   monpoly -verified        -sig et.sig -formula f.mfotl -log et.log > v.txt  2>/dev/null
  >   monpoly -verified -no_mw -sig et.sig -formula f.mfotl -log et.log > v2.txt 2>/dev/null
  >   if diff -q m.txt v.txt > /dev/null && diff -q v.txt v2.txt > /dev/null
  >   then echo "OK   $phi"
  >   else echo "MISMATCH $phi"; diff m.txt v.txt; diff v.txt v2.txt; fi
  > done < formulas.txt
  OK   tp(t)
  OK   ts(t)
  OK   tpts(i,t)
  OK   temp(x) AND tp(t)
  OK   temp(x) AND tp(t) AND ts(s)
  OK   (ONCE (0,2) temp(x)) AND tp(t)
  OK   (EVENTUALLY (0,2) temp(x)) AND tp(t)
  OK   (ONCE [0,2] temp(x)) AND tp(t)
  OK   (EVENTUALLY [0,2] temp(x)) AND ts(t)
  OK   (ONCE [1,2] temp(x)) AND tp(t)
  OK   (EVENTUALLY [1,3] temp(x)) AND tp(t)
  OK   (temp(x) SINCE [0,3] p(x)) AND tp(t)
  OK   tp(t) AND ONCE[0,2] temp(x)
  OK   ONCE[0,2] (temp(x) AND tp(t))
  OK   EVENTUALLY[0,2] (temp(x) AND tp(t))
  OK   (EXISTS x. temp(x)) AND tp(t)
