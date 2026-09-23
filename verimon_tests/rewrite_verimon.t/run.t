VeriMon's preparation of the formula in the verified monitor (-verified): the
formula is type checked and, if it is not monitorable, normalized and rewritten
by the verified rewriting (Rewriting.thy, Dense_VeriMon.thy), which freezes the
conjunct that range-restricts the variables under the temporal operator.  Each
formula below is monitorable only after rewriting.  It is run through the
verified monitor and through MonPoly's own algorithm, whose front end rewrites
the formula itself; where MonPoly accepts it, the two must agree.  With -no_rw,
the verified monitor rejects the formula.

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
