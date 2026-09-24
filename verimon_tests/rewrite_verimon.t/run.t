VeriMon's preparation of the formula in the verified monitor (-verified): the
formula is type checked and, if it is not monitorable, normalized and rewritten
by the verified rewriting (Rewriting.thy, Dense_VeriMon.thy), which freezes the
conjunct that range-restricts the variables under the temporal operator.  All
but the third formula are monitorable only after rewriting.  Each formula is
run through the verified monitor and through MonPoly's own algorithm, whose
front end rewrites the formula itself; where MonPoly accepts it, the two must
agree.  With -no_rw, the verified monitor rejects the formulas that need
rewriting.

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   echo "=== $phi"
  >   monpoly -verified -sig cov.sig -formula f.mfotl -log cov.log > b.txt 2>&1
  >   monpoly           -sig cov.sig -formula f.mfotl -log cov.log > a.txt 2>&1
  >   cat b.txt
  >   if grep -q "^@" a.txt; then
  >     diff -q a.txt b.txt > /dev/null || { echo "MONPOLY MISMATCH"; diff a.txt b.txt; }
  >   fi
  >   monpoly -verified -no_rw -sig cov.sig -formula f.mfotl -log cov.log 2>&1 | head -1
  > done < formulas.txt
  === R(x) AND ONCE[1,3] (NOT S(x))
  @3 (time point 3): (3)
  @4 (time point 4): (2)
  @7 (time point 5): (1)
  @9 (time point 7): (9)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === R(x) AND EVENTUALLY[0,2] (NOT S(x))
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  @1 (time point 2): (2)
  @3 (time point 3): (3)
  @4 (time point 4): (2)
  @7 (time point 5): (1)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === R(x) AND ((NOT S(x)) SINCE[1,3] R(x))
  @4 (time point 4): (2)
  @4 (time point 4): (2)
  === R(x) AND (R(x) SINCE[1,3] (NOT S(x)))
  @3 (time point 3): (3)
  @4 (time point 4): (2)
  @7 (time point 5): (1)
  @9 (time point 7): (9)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === P(x,y) AND ONCE[0,4] (NOT Q(x,y))
  @0 (time point 0): (1,2)
  @1 (time point 1): (1,2) (3,4)
  @1 (time point 2): (5,5)
  @3 (time point 3): (1,2)
  @4 (time point 4): (2,3) (3,4)
  @7 (time point 6): (1,2)
  @9 (time point 7): (5,6)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === P(x,y) AND (NOT Q(x,y) OR S(x))
  @0 (time point 0): (1,2) (2,3)
  @1 (time point 1): (1,2)
  @3 (time point 3): (1,2)
  @4 (time point 4): (2,3) (3,4)
  @7 (time point 6): (1,2)
  @9 (time point 7): (5,6)
  The formula is NOT monitorable. Use the -check or -verbose flags.
