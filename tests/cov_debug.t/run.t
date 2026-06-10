Run MonPoly with -debug eval on a variety of operators to exercise the
Dbg_eval tracing branches in the evaluator. The trace itself is verbose and
not asserted (discarded); we only check the runs succeed.

  $ while IFS= read -r phi; do
  >   [ -z "$phi" ] && continue
  >   printf '%s\n' "$phi" > f.mfotl
  >   monpoly -debug eval -sig cov.sig -formula f.mfotl -log cov.log > /dev/null 2>&1
  >   echo "$? $phi"
  > done < formulas.txt
  0 (P(x,y) SINCE[0,2] Q(x,y)) AND R(x)
  0 (R(x) OR S(x))
  0 P(x,y) UNTIL[0,2] Q(x,y)
  0 y <- CNT x R(x)
  0 y <- SUM x ONCE[0,2] R(x)
  0 EXISTS y. ONCE[0,2] P(x,y)
  0 EVENTUALLY[0,2] R(x)
  0 PREV[0,1] R(x)
  0 NEXT[0,1] R(x)
  0 NOT (EXISTS x. R(x))
  0 P(x,y) AND NOT Q(x,y)
