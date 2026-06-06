Verified-kernel-only operators (Trigger/Release/Historically/Always/PastAlways,
temporal regex MatchP/MatchF, LetPast). These are not monitorable by the
unverified MonPoly kernel, so only VeriMon (-verified) is run; the output is
captured as a regression baseline.

Each formula is also run through the second verified kernel (-no_mw); the two
must agree.

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   echo "=== $phi"
  >   monpoly -verified        -sig cov.sig -formula f.mfotl -log cov.log > a.txt 2>&1
  >   monpoly -verified -no_mw -sig cov.sig -formula f.mfotl -log cov.log > b.txt 2>&1
  >   cat a.txt
  >   diff -q a.txt b.txt > /dev/null || echo "NO_MW MISMATCH"
  > done < formulas.txt
  === P(x,y) TRIGGER[0,2] Q(x,y)
  @0 (time point 0): (2,3)
  @1 (time point 1): (3,4)
  @1 (time point 2): (5,5)
  @7 (time point 5): (2,3)
  === P(x,y) TRIGGER[1,3] Q(x,y)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === R(x) TRIGGER[0,*) S(x)
  @0 (time point 0): (2)
  @1 (time point 1): (2)
  @9 (time point 7): (9)
  === (NOT R(x)) TRIGGER[0,2] S(x)
  @0 (time point 0): (2)
  @1 (time point 1): (2)
  @3 (time point 3): (7)
  @7 (time point 5): (2)
  === EXISTS y. (P(x,y) TRIGGER[0,2] Q(x,y))
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  @1 (time point 2): (5)
  @7 (time point 5): (2)
  === P(x,y) RELEASE[0,2] Q(x,y)
  @0 (time point 0): (2,3)
  @1 (time point 1): (3,4)
  @1 (time point 2): (5,5)
  @4 (time point 4): (9,9)
  @9 (time point 7): (6,5)
  === P(x,y) RELEASE[1,3] Q(x,y)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === (NOT P(x,y)) RELEASE[0,2] Q(x,y)
  @3 (time point 3): (2,3)
  @4 (time point 4): (9,9)
  @7 (time point 5): (2,3)
  @9 (time point 7): (6,5)
  === HISTORICALLY[0,2] R(x)
  @0 (time point 0): (1)
  @7 (time point 5): (1)
  === HISTORICALLY[1,*) R(x)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === PAST_ALWAYS[0,2] R(x)
  @0 (time point 0): (1)
  @7 (time point 5): (1)
  === ALWAYS[0,2] R(x)
  @4 (time point 4): (2)
  @9 (time point 7): (9)
  === ALWAYS[1,3] R(x)
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === ONCE[0,*) R(x)
  @0 (time point 0): (1)
  @1 (time point 1): (1) (2)
  @1 (time point 2): (1) (2)
  @3 (time point 3): (1) (2) (3)
  @4 (time point 4): (1) (2) (3)
  @7 (time point 5): (1) (2) (3)
  @7 (time point 6): (1) (2) (3)
  @9 (time point 7): (1) (2) (3) (9)
  === MATCHP[0,2] R(x)?
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  @1 (time point 2): (2)
  @3 (time point 3): (3)
  @4 (time point 4): (2)
  @7 (time point 5): (1)
  @9 (time point 7): (9)
  === MATCHF[0,2] R(x)?
  @0 (time point 0): (1)
  @1 (time point 1): (2)
  @1 (time point 2): (2)
  @3 (time point 3): (3)
  @4 (time point 4): (2)
  @7 (time point 5): (1)
  @9 (time point 7): (9)
  === MATCHP[0,4] (R(x)? .)*
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === MATCHF[0,4] (S(x)? .)*
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === MATCHP[0,*) (R(x)? + S(x)?)
  @0 (time point 0): (1) (2)
  @1 (time point 1): (2)
  @1 (time point 2): (2)
  @3 (time point 3): (3) (7)
  @4 (time point 4): (2)
  @7 (time point 5): (1) (2)
  @9 (time point 7): (9)
  === R(x) AND MATCHP[0,2] (R(x)? .)*
  The formula is NOT monitorable. Use the -check or -verbose flags.
  === R(x) SINCE[0,2] (R(x) TRIGGER[0,2] S(x))
  @0 (time point 0): (2)
  @1 (time point 1): (2)
  @1 (time point 2): (2)
  @7 (time point 5): (2)
  @9 (time point 7): (9)
  === R(x) AND EVENTUALLY[0,2] (R(x) UNTIL[0,2] S(x))
  @1 (time point 1): (2)
  @9 (time point 7): (9)
  === LETPAST foo(x) = S(x) OR (EXISTS y. P(x,y) AND PREV[0,*) foo(y)) IN foo(x)
  @0 (time point 0): (2)
  @1 (time point 1): (1) (2)
  @3 (time point 3): (7)
  @7 (time point 5): (2)
  @7 (time point 6): (1)
  @9 (time point 7): (9)
