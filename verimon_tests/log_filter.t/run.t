Under -verified, the log is read, converted and monitored by the code of
thys/MFODL_Monitor_Dense/Log_Monitor.thy.  The parser drops the events of the predicates that
are in the signature but that the formula does not mention before it stores them: their
fields are neither converted nor checked.

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

The formula mentions a predicate by its name and arity, and a LET binds only the arity it
defines: here the R of the signature, with two arguments, is read, although R with one
argument is bound.  (MonPoly's own filter, which binds names, drops the events of R.)

  $ echo 'LET R(x) = P(x) IN R(x) AND EXISTS y. R(x,y)' > let.mfotl
  $ printf '@1 P(1) R(1,2)\n@2 P(2)\n' > l.log
  $ monpoly -verified -sig s.sig -formula let.mfotl -log l.log
  @1 (time point 0): (1)
  $ monpoly -verified -sig s.sig -formula let.mfotl -log l.log -old_log_parser

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

Timestamps are natural numbers, in decimal or with the prefixes 0x, 0o and 0b, without signs
and underscores:

  $ printf '@0x10 P(1)\n@-1 P(2)\n@1_0 P(3)\n@0b11111 P(4)\n@0o40 P(5)\n' > l.log
  $ monpoly -verified -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @16 (time point 0): (1)
  ERROR while parsing log:
  l.log:2:1: Cannot convert -1 into a timestamp
  ERROR while parsing log:
  l.log:3:1: Cannot convert 1_0 into a timestamp
  @31 (time point 1): (4)
  @32 (time point 2): (5)

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
