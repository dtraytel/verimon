Characterization test for how the regex grammar disambiguates the bare-formula
juxtaposition boundary. The grammar is inherently ambiguous here (e.g.
`MATCHF[I] R(x) AND p()` could group AND inside or outside the regex), so a
disambiguation policy is fixed by the precedence declarations in
formula_parser.mly (REDUCE_CONCAT + the regex-atom-start terminal group). These
checks pin the resulting parse via `-verbose -check`, which echoes the parsed
formula, so any future change to that policy shows up as a wrong grouping here.

Bare atom `R(x)` is sugar for `R(x)? .` (test then a wildcard step):

  $ echo 'MATCHF[0,5] R(x)' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    |>[0,5]((R(x)?) .)

Juxtaposition is greedy, right-associative concatenation:

  $ echo 'MATCHF[0,5] R(x) S(y)' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    |>[0,5](((R(x)?) .) ((S(y)?) .))

  $ echo 'MATCHF[0,5] R(x)? S(y)? .' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    |>[0,5]((R(x)?) ((S(y)?) .))

Concatenation binds tighter than alternation:

  $ echo 'MATCHF[0,5] R(x)? S(y)? + T(z)?' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    |>[0,5](((R(x)?) S(y)?) + T(z)?)

The ambiguous case `R(x) AND p()` resolves with AND OUTSIDE the regex:

  $ echo 'MATCHF[0,5] R(x) AND p()' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    (|>[0,5]((R(x)?) .)) AND p()

Parenthesised regex with star and alternation (past variant):

  $ echo 'MATCHP[0,*) ((R(x)? .)* + S(y)?)' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    <|[0,*)((((R(x)?) .)*) + S(y)?)
