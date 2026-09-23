VeriMon's preparation of the formula in the verified dense evaluator (-vdense):
the formula is type checked and, if it is not monitorable, normalized and
rewritten by the verified rewriting (Rewriting.thy, Dense_VeriMon.thy), which
freezes the conjunct that range-restricts the variables under the temporal
operator.  Each formula below is monitorable only after rewriting.  It is run
through the shipping verified monitor, whose front end rewrites the formula
itself, and through -vdense; where both accept it, they must agree.  With
-no_rw, -vdense rejects the formula.

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   echo "=== $phi"
  >   monpoly -verified         -sig cov.sig -formula f.mfotl -log cov.log > a.txt 2>&1
  >   monpoly -verified -vdense -sig cov.sig -formula f.mfotl -log cov.log > b.txt 2>&1
  >   cat b.txt
  >   if grep -q "^@" a.txt; then
  >     diff -q a.txt b.txt > /dev/null || { echo "VDENSE MISMATCH"; diff a.txt b.txt; }
  >   fi
  >   monpoly -verified -vdense -no_rw -sig cov.sig -formula f.mfotl -log cov.log 2>&1 | head -1
  > done < formulas.txt
