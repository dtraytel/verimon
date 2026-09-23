The verified formula parser (thys/MFODL_Parser), selected with -verified_parser,
builds the same formula as MonPoly's parser:

  $ echo 'T(x) OR R(x) AND S(x) SINCE [0,5] PREV T(x) AND NOT R(x)' > f.mfotl
  $ monpoly -check -verbose -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    (T(x) OR (R(x) AND S(x))) SINCE[0,5] PREVIOUS[0,*) (T(x) AND (NOT R(x)))
  $ monpoly -check -verbose -verified_parser -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    (T(x) OR (R(x) AND S(x))) SINCE[0,5] PREVIOUS[0,*) (T(x) AND (NOT R(x)))

  $ echo 'MATCHF[0,5] R(x) S(y)? + T(z)? AND p()' > f.mfotl
  $ monpoly -check -verbose -verified_parser -sig regex.sig -formula f.mfotl 2>&1 | grep -A1 'analyzed formula is:'
  The analyzed formula is:
    (|>[0,5]((((R(x)?) .) S(y)?) + T(z)?)) AND p()

Formulas it rejects are reported as parse errors:

  $ echo 'R(x) AND' > f.mfotl
  $ monpoly -check -verified_parser -sig regex.sig -formula f.mfotl 2>&1 | head -2
  [Main.main] Failed to parse formula file
  Fatal error: exception Failure("[Main.main] the verified parser rejects the formula")

Differential test against MonPoly's parser on random formulas (few, since the
verified parser takes about a second per formula): the two agree on
every formula both accept, and the verified parser accepts nothing MonPoly
rejects (vp-only: 0). mp-only counts the documented differences
(thys/MFODL_Parser/README.md).

  $ parser_difftest -n 40 -seed 1 | tail -1
  inputs: 40  same: 40 (both accept: 36)  differ: 0  mp-only: 0  vp-only: 0
  $ parser_difftest -lex -n 20000 -seed 1 | tail -1
  lexed: 20000  same: 20000  differ: 0
