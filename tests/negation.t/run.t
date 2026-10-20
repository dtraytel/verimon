Formulas that become monitorable only once the negations are pushed in: a double negation is
removed before a negation is pushed into a conjunction, and the conjunctions are nested to the
left, so that a negated conjunct follows the conjuncts that bind its variables. Each formula
(with -negate where marked) is followed by an explicit monitorable formula with the same
verdicts.

  $ while read -r neg phi; do
  >   printf '%s\n' "$phi" > f.mfotl
  >   echo "=== $neg $phi"
  >   if [ "$neg" = - ]; then verimon -sig neg.sig -formula f.mfotl -log neg.log 2>&1
  >   else verimon -sig neg.sig -formula f.mfotl -log neg.log "$neg" 2>&1; fi
  > done < formulas.txt
  === - NOT NOT (P(x) AND Q(x))
  @0 (time point 0): (1)
  @1 (time point 1): (3)
  === - P(x) AND Q(x)
  @0 (time point 0): (1)
  @1 (time point 1): (3)
  === - NOT NOT (R(x,y) AND NOT (x = y))
  @0 (time point 0): (1,2)
  @1 (time point 1): (2,5) (3,4)
  @2 (time point 2): (5,3)
  === - R(x,y) AND NOT (x = y)
  @0 (time point 0): (1,2)
  @1 (time point 1): (2,5) (3,4)
  @2 (time point 2): (5,3)
  === - NOT ((R(x,y) AND NOT (x = y)) IMPLIES FALSE)
  @0 (time point 0): (1,2)
  @1 (time point 1): (2,5) (3,4)
  @2 (time point 2): (5,3)
  === -negate (R(x,y) AND NOT (x = y)) IMPLIES EVENTUALLY[0,3] Q(y)
  @0 (time point 0): (1,2)
  @1 (time point 1): (3,4)
  @2 (time point 2): (5,3)
  === - (R(x,y) AND NOT (x = y)) AND NOT EVENTUALLY[0,3] Q(y)
  @0 (time point 0): (1,2)
  @1 (time point 1): (3,4)
  @2 (time point 2): (5,3)
  === -negate P(x) IMPLIES ((ONCE[1,*) Q(x)) OR ((NOT Q(x)) SINCE R(x,x)))
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  === - P(x) AND NOT ((ONCE[1,*) Q(x)) OR ((NOT Q(x)) SINCE R(x,x)))
  @0 (time point 0): (2)
  @1 (time point 1): (3)
  === - P(x) AND ((NOT ONCE Q(x)) AND (NOT EVENTUALLY[0,2] Q(x)))
  @0 (time point 0): (2)
  @2 (time point 2): (4)
  === - (P(x) AND NOT ONCE Q(x)) AND NOT EVENTUALLY[0,2] Q(x)
  @0 (time point 0): (2)
  @2 (time point 2): (4)
