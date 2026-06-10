Regression test for the MOD operator-precedence fix in formula_parser.mly.

MOD was missing from the precedence table, so it bound looser than every other
arithmetic operator and right-associatively: `x MOD y + z` parsed as
`x MOD (y + z)`. After adding MOD to the multiplicative level it parses as
`(x MOD y) + z`, like a normal modulo operator.

Log: @0 p3(7,3,10). The free variable r = (7 mod 3) + 10 = 11 (fixed); the old
parse gave 7 mod (3 + 10) = 7. Both monitors must agree on 11.

  $ echo '(p3(x,y,z) AND r = x MOD y + z)' > mod.mfotl
  $ monpoly -sig prec.sig -formula mod.mfotl -log mod.log
  @0 (time point 0): (7,3,10,11)
  $ monpoly -verified -sig prec.sig -formula mod.mfotl -log mod.log
  @0 (time point 0): (7,3,10,11)
