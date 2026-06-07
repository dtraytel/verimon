Differential tests for the regex temporal operators (MATCHP / MATCHF). Each
formula in formulas.txt is evaluated by BOTH the unverified (MonPoly) and the
verified (VeriMon, with and without multi-way joins) kernels on the same trace;
the outputs must coincide. This exercises the regex eval added to MonPoly's own
algorithm (algorithm.ml: EMatchP/EMatchF) against the verified reference.

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
  OK   MATCHP[0,2] R(x)?
  OK   MATCHF[0,2] R(x)?
  OK   MATCHP[0,*) R(x)?
  OK   MATCHF[0,4] R(x)?
  OK   MATCHP(0,4] R(x)?
  OK   MATCHP[1,3] R(x)?
  OK   MATCHP[2,2] R(x)?
  OK   MATCHP[0,2] .
  OK   MATCHF[0,2] .
  OK   MATCHP[0,2] R(x)? .
  OK   MATCHF[0,2] R(x)? .
  OK   MATCHP[0,4] (R(x)? .)*
  OK   MATCHF[0,4] (R(x)? .)*
  OK   MATCHP[0,*) (R(x)? + S(x)?)
  OK   MATCHF[0,*) (R(x)? + S(x)?)
  OK   MATCHP[0,4] (R(x)? + S(x)?)
  OK   MATCHP[0,4] (R(x)? . S(x)?)
  OK   MATCHF[0,4] (R(x)? . S(x)?)
  OK   MATCHP[0,4] (R(x)? .) (S(x)? .)
  OK   MATCHP[0,4] ((R(x)? + S(x)?) .)*
  OK   MATCHP[0,2] (R(x) AND S(x))?
  OK   MATCHF[0,2] (R(x) AND S(x))?
  OK   MATCHP[0,2] (P(x,y))?
  OK   MATCHF[0,2] (P(x,y))?
  OK   MATCHP[0,4] (P(x,y)? .)*
  OK   MATCHP[0,2] (R(x)?)*
  OK   MATCHF[0,2] (R(x)?)*
  OK   MATCHP[0,5] (R(x)? + (S(x)? .))
  OK   R(x) AND MATCHP[0,2] (R(x)? .)*
  OK   EXISTS x. MATCHP[0,2] R(x)?
  OK   ONCE[0,2] (MATCHP[0,2] R(x)?)
  OK   MATCHP[0,*) (A()? .)*
  OK   MATCHF[0,2] (A()? + B()?)
  OK   MATCHP[0,4] (R(x)? . . S(x)?)
  OK   (MATCHP[0,2] R(x)?) SINCE[0,3] S(x)
