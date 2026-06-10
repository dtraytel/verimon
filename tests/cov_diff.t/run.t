Differential tests: every formula in formulas.txt is evaluated by BOTH the
unverified (MonPoly) and the verified (VeriMon) kernel on the same trace; the
two outputs must coincide. This exercises the shared algorithm/optimized_mtl
code paths in MonPoly and the verified kernel together.

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   monpoly                  -sig cov.sig -formula f.mfotl -log cov.log > m.txt  2>/dev/null
  >   monpoly -verified        -sig cov.sig -formula f.mfotl -log cov.log > v.txt  2>/dev/null
  >   monpoly -verified -no_mw -sig cov.sig -formula f.mfotl -log cov.log > v2.txt 2>/dev/null
  >   if diff -q m.txt v.txt > /dev/null && diff -q v.txt v2.txt > /dev/null
  >   then echo "OK   $phi"
  >   else echo "MISMATCH $phi"; diff m.txt v.txt; diff v.txt v2.txt; fi
  > done < formulas.txt
  OK   P(x,y) SINCE[0,*) Q(x,y)
  OK   P(x,y) SINCE[1,3] Q(x,y)
  OK   P(x,y) SINCE[1,*) Q(x,y)
  OK   P(x,y) SINCE(1,4] Q(x,y)
  OK   P(x,y) SINCE[2,2] Q(x,y)
  OK   (NOT P(x,y)) SINCE[0,2] Q(x,y)
  OK   (NOT P(x,y)) SINCE[0,*) Q(x,y)
  OK   (NOT R(x)) SINCE[0,2] S(x)
  OK   P(x,y) SINCE[1,*) T(x,y,z)
  OK   P(x,y) SINCE[1,3] T(x,y,z)
  OK   (NOT P(x,y)) SINCE[0,*) T(x,y,z)
  OK   R(x) SINCE[0,*) S(x)
  OK   A() SINCE[0,*) B()
  OK   A() SINCE[1,3] B()
  OK   (EXISTS x. R(x)) SINCE[0,2] (EXISTS y. S(y))
  OK   EXISTS z. (P(x,y) SINCE[1,*) T(x,y,z))
  OK   EXISTS x. (R(x) SINCE[0,2] S(x))
  OK   P(x,y) UNTIL[0,2] Q(x,y)
  OK   P(x,y) UNTIL[1,3] Q(x,y)
  OK   (NOT P(x,y)) UNTIL[0,2] Q(x,y)
  OK   EXISTS y. (P(x,y) UNTIL[0,2] Q(x,y))
  OK   ONCE[0,2] R(x)
  OK   ONCE[1,*) R(x)
  OK   ONCE[2,4] P(x,y)
  OK   ONCE[0,0] R(x)
  OK   EVENTUALLY[0,3] R(x)
  OK   EVENTUALLY[1,3] P(x,y)
  OK   EVENTUALLY[0,0] R(x)
  OK   PREV[0,*) R(x)
  OK   PREV[1,2] R(x)
  OK   NEXT[0,2] R(x)
  OK   NEXT[1,*) P(x,y)
  OK   EXISTS y. ONCE[0,2] P(x,y)
  OK   EXISTS y. EVENTUALLY[0,2] P(x,y)
  OK   (ONCE[0,2] P(x,y)) AND x > 1
  OK   (EVENTUALLY[0,3] R(x)) AND x > 1
  OK   (P(x,y) SINCE[0,*) Q(x,y)) AND x > 1
  OK   R(x) AND x > 2
  OK   R(x) AND x >= 2
  OK   R(x) AND x = 2
  OK   R(x) AND NOT x = 2
  OK   P(x,y) AND NOT Q(x,y)
  OK   P(x,y) AND NOT x = y
  OK   R(x) AND S(x)
  OK   R(x) AND (R(x) AND S(x))
  OK   P(x,y) AND Q(x,y)
  OK   P(x,y) AND Q(y,x)
  OK   T(x,y,z) AND P(x,y)
  OK   R(x) OR S(x)
  OK   (R(x) AND x>1) OR (S(x) AND x<5)
  OK   EXISTS y. P(x,y)
  OK   EXISTS x, y. P(x,y)
  OK   NOT (EXISTS x. R(x))
  OK   Str(x) AND x = "x"
  OK   R(x) AND r = x
  OK   y <- CNT x R(x)
  OK   y <- SUM x R(x)
  OK   y <- MIN x R(x)
  OK   y <- MAX x R(x)
  OK   y <- AVG x R(x)
  OK   y <- MED x R(x)
  OK   y <- CNT x; z R(x) AND S(z)
  OK   y <- SUM x ONCE[0,2] R(x)
  OK   y <- CNT x ONCE[0,2] R(x)
  OK   y <- MAX x ONCE[1,3] R(x)
  OK   y <- AVG x; g (P(g,x))
  OK   LET foo(x) = R(x) AND x>1 IN foo(x)
  OK   LET foo(x,y) = P(x,y) IN ONCE[0,2] foo(x,y)
  OK   LET foo(x) = R(x) IN foo(x) SINCE[0,2] S(x)
  OK   LET foo(x) = R(x) IN (foo(x) AND S(x))
  OK   LET foo(x,y) = P(x,y) IN EXISTS y. foo(x,y)
  OK   LET foo(x) = R(x) IN NEXT[0,1] foo(x)
  OK   LET foo(x) = R(x) IN PREV[0,1] foo(x)
  OK   LET foo(x) = R(x) IN foo(x) UNTIL[0,2] S(x)
  OK   LET foo(x) = R(x) IN y <- CNT x foo(x)
  OK   LET foo(x) = R(x) IN y <- CNT x ONCE[0,2] foo(x)
  OK   LET foo(x) = R(x) IN EXISTS x. ONCE[0,2] foo(x)
  OK   LET foo() = A() IN ONCE[0,2] (NOT foo())
  OK   P(x,y) OR Q(y,x)
  OK   (R(x) AND x>0) OR (S(x))
  OK   EXISTS x. (NOT (EXISTS y. P(x,y)))
  OK   y <- MED x ONCE[0,2] R(x)
  OK   y <- MIN x ONCE[0,2] R(x)
  OK   y <- SUM x; g (P(g,x))
  OK   (EXISTS y. P(x,y)) AND NOT R(x)
  OK   NEXT[0,1] (P(x,y) AND x > 1)
  OK   R(x) AND y = x + 1
  OK   R(x) AND y = x - 2
  OK   R(x) AND y = x * 2
  OK   R(x) AND y = x MOD 2
  OK   R(x) AND y = -x
  OK   R(x) AND P(x,y) AND z = x + y
  OK   F(x) AND y = x + 1.0
  OK   F(x) AND x < 2.0
  OK   F(x) AND x <= 2.5
  OK   z <- SUM x F(x)
  OK   z <- AVG x F(x)
  OK   z <- MED x F(x)
  OK   z <- MIN x F(x)
  OK   z <- MAX x F(x)
  OK   R(x) AND y = i2f(x)
  OK   F(x) AND y = f2i(x)
  OK   ONCE[0,2] (F(x) AND x < 3.0)
  OK   F(x) SINCE[0,2] F(x)
