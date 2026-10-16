Regression test for the regex concatenation-vs-alternation precedence fix.

The old flat regex grammar was ambiguous and resolved `a b + c` as `a (b + c)`
(alternation binding tighter than concatenation). The stratified grammar binds
concatenation tighter, like standard regex: `R(x)? S(x)? + T(x)?` parses as
`(R(x)? S(x)?) + T(x)?`.

Log: @0 T(5); @1 R(9) S(9). At tp0 only T holds, so the `+ T(x)?` branch matches
under the new parse and outputs 5; the old parse `R(x)? (S(x)? + T(x)?)` needs R
and produced nothing at tp0. At tp1 both R and S hold, so the `R(x)? S(x)?`
branch matches under both parses (output 9).

  $ echo 'MATCHF[0,5] (R(x)? S(x)? + T(x)?)' > regex.mfotl
  $ verimon -sig regex.sig -formula regex.mfotl -log regex.log
  @0 (time point 0): (5)
  @1 (time point 1): (9)
