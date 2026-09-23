Under -verified, the log is read, converted and monitored by the code of
thys/MFODL_Monitor_Dense/Log_Monitor.thy.  The parser drops the events of the predicates that
are in the signature but whose names do not occur freely in the formula before it stores them:
their fields are neither converted nor checked.

  $ echo 'P(x)' > p.mfotl
  $ printf '@1 P(1) Q(1) R(1) R(a,b) F(x)\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): (1)
  @2 (time point 1): (2)

With -nofilterrel, all events are converted:

  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log -nofilterrel
  ERROR while parsing log:
  l.log:1:1: Wrong tuple length for predicate R (expected: 2, actual: 1)
  [1]

A predicate occurs freely by its name and arity, and a LET binds only the arity it defines:
here the R of the signature, with two arguments, occurs freely, although R with one argument
is bound, so the parser keeps the events of R.  (MonPoly's own filter, which binds names, drops
them.)

  $ echo 'LET R(x) = P(x) IN R(x) AND EXISTS y. R(x,y)' > let.mfotl
  $ printf '@1 P(1) R(1,2)\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula let.mfotl -log l.log
  @1 (time point 0): (1)
  $ monpoly -verified -sig s.sig -formula let.mfotl -log l.log -old_log_parser

When all occurrences of R are bound, the events of R are dropped:

  $ echo 'LET R(x) = P(x) IN R(x)' > let1.mfotl
  $ printf '@1 P(1) R(1) R(a,b)\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula let1.mfotl -log l.log
  @1 (time point 0): (1)
  @2 (time point 1): (2)

A predicate of the signature with an argument of type regexp, which the verified kernel does not
support, may be declared if the formula does not mention it:

  $ printf 'P(int)\nX(regexp)\n' > rx.sig
  $ printf '@1 P(1) X("a.*")\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig rx.sig -formula p.mfotl -log l.log
  @1 (time point 0): (1)
  @2 (time point 1): (2)

Events of predicates that the signature does not declare, events of the formula's
predicates of another arity or with fields of another type, and entries with a timestamp
that is not a natural number are reported, at the entry's '@'; with -ignore_parse_errors,
the entry is dropped:

  $ printf '@1 P(1) S(2)\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  ERROR while parsing log:
  l.log:1:1: Predicate S was not defined in the signature.
  [1]
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  ERROR while parsing log:
  l.log:1:1: Predicate S was not defined in the signature.
  @2 (time point 0): (2)
  $ printf '@1 P(1,2)\n@2 P(a)\n@3 P(3)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  ERROR while parsing log:
  l.log:1:1: Wrong tuple length for predicate P (expected: 1, actual: 2)
  ERROR while parsing log:
  l.log:2:1: Expected type int for predicate P, field number 1
  @3 (time point 0): (3)
  $ echo 'F(x)' > f.mfotl
  $ printf '@1 F(1.5) F(-2e3)\n@2 F(1.5) F(x)\n@3 F(nan)\n' > l.log
  $ monpoly -verified -sig s.sig -formula f.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): (-2000) (1.5)
  ERROR while parsing log:
  l.log:2:1: Expected type float for predicate F, field number 1
  @3 (time point 1): (nan)

Timestamps are natural numbers, and integers are written as for Zarith's Z.of_string, in
decimal or with the prefixes 0x, 0o and 0b, with underscores after the first digit, except
that a digit is required after the sign and the prefix:

  $ printf '@0x10 P(1)\n@-1 P(2)\n@1_7 P(3_0)\n@0b1_0010 P(-0x1f)\n@0o40 P("+5")\n@_1 P(6)\n@33 P(0x)\n@34 P(1)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @16 (time point 0): (1)
  ERROR while parsing log:
  l.log:2:1: Cannot convert -1 into a timestamp
  @17 (time point 1): (30)
  @18 (time point 2): (-31)
  @32 (time point 3): (5)
  ERROR while parsing log:
  l.log:6:1: Cannot convert _1 into a timestamp
  ERROR while parsing log:
  l.log:7:1: Expected type int for predicate P, field number 1
  @34 (time point 4): (1)

Timestamps must not decrease, and the verified kernel does not support commands:

  $ printf '@2 P(1)\n@1 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @2 (time point 0): (1)
  ERROR: Out of order timestamp 1 (previous: 2)
  [1]
  $ printf '@1 P(1)\n> get_pos <\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): (1)
  ERROR: Commands are not supported by the verified kernel
  [1]

The errors of an entry are checked for in the order of MonPoly's parser: its predicates are
looked up before the order of the timestamps is checked, and its fields are converted after:

  $ printf '@2 P(1)\n@1 S(1)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @2 (time point 0): (1)
  ERROR while parsing log:
  l.log:2:1: Predicate S was not defined in the signature.
  [1]
  $ printf '@2 P(1)\n@1 P(a)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @2 (time point 0): (1)
  ERROR: Out of order timestamp 1 (previous: 2)
  [1]

In a large signature, the predicates are looked up in a mapping, and those whose events are
skipped in a set:

  $ for i in $(seq 1 40); do echo "A$i(int)"; done > big.sig
  $ echo 'A7(x) AND NOT A8(x)' > big.mfotl
  $ printf '@1 A7(1) A7(2) A8(2) A9(x) A40(1,2)\n@2 A7(3) A1(1)\n@3 A7(a)\n' > l.log
  $ monpoly -verified -sig big.sig -formula big.mfotl -log l.log
  @1 (time point 0): (1)
  @2 (time point 1): (3)
  ERROR while parsing log:
  l.log:3:1: Expected type int for predicate A7, field number 1
  [1]
  $ monpoly -verified -sig big.sig -formula big.mfotl -log l.log -nofilterrel
  ERROR while parsing log:
  l.log:1:1: Wrong tuple length for predicate A40 (expected: 1, actual: 2)
  [1]
  $ printf '@1 A7(1) A7(2) A8(2)\n@2 A7(3) B(1)\n' > l.log
  $ monpoly -verified -sig big.sig -formula big.mfotl -log l.log
  @1 (time point 0): (1)
  ERROR while parsing log:
  l.log:2:1: Predicate B was not defined in the signature.
  [1]

Syntax errors are reported as MonPoly's parser reports them:

  $ printf '@1 P(1)\n@2 P(2 \n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): (1)
  ERROR while parsing log:
  l.log:3:1: Expected ',' or ')' but saw <EOF>
  [1]

For a formula with future operators, the log ends with a time point with no events at the
largest timestamp, unless -nonewlastts:

  $ echo 'P(x) AND EVENTUALLY[0,5] P(x)' > ev.mfotl
  $ printf '@1 P(1)\n@4 P(1)\n@20 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula ev.mfotl -log l.log
  @1 (time point 0): (1)
  @4 (time point 1): (1)
  @20 (time point 2): (2)
  $ monpoly -verified -sig s.sig -formula ev.mfotl -log l.log -nonewlastts
  @1 (time point 0): (1)
  @4 (time point 1): (1)
