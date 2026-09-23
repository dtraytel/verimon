The log is read by the verified parser of session Log_Parser (thys/Log_Parser), and by
MonPoly's hand-written parser with -old_log_parser.

  $ echo 'P(x)' > p.mfotl
  $ echo 'Q(i, x)' > q.mfotl
  $ echo 'E()' > e.mfotl

Simple strings; quoted strings, which may contain white space and escapes, and are kept as
written; the same with an r in front; comments, which end at a line end or at the end of the
input; line ends as "\n", "\r", or "\r\n"; and ';' after an entry:

  $ printf '@1 P(a) P("b c") P(r"d\\"e") # a comment @2 P(x)\r\n@2; @3 P ( [x]/y:z-1.! ) ;\r@4 P(a)(b) # the end' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): ("a") ("b c") ("d\"e")
  @3 (time point 2): ("[x]/y:z-1.!")
  @4 (time point 3): ("a") ("b")
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -old_log_parser
  @1 (time point 0): ("a") ("b c") ("d\"e")
  @3 (time point 2): ("[x]/y:z-1.!")
  @4 (time point 3): ("a") ("b")
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -verified
  @1 (time point 0): ("a") ("b c") ("d\"e")
  @3 (time point 2): ("[x]/y:z-1.!")
  @4 (time point 3): ("a") ("b")
  $ monpoly -sig s.sig -formula p.mfotl < l.log
  @1 (time point 0): ("a") ("b c") ("d\"e")
  @3 (time point 2): ("[x]/y:z-1.!")
  @4 (time point 3): ("a") ("b")

Predicates without arguments, with or without parentheses, and time points without events:

  $ printf '@1 E @2 E() @3 @4 E' > l.log
  $ monpoly -sig s.sig -formula e.mfotl -log l.log
  @1 (time point 0): true
  @2 (time point 1): true
  @4 (time point 3): true
  $ monpoly -sig s.sig -formula e.mfotl -log l.log -verified
  @1 (time point 0): true
  @2 (time point 1): true
  @4 (time point 3): true

Several tuples after a predicate, and tokens without white space between them:

  $ printf '@1 Q(1,a)(2,"b")Q(3,c)@2 Q(4,d)' > l.log
  $ monpoly -sig s.sig -formula q.mfotl -log l.log
  @1 (time point 0): (1,"a") (2,"b") (3,"c")
  @2 (time point 1): (4,"d")

Commands between time points; MonPoly's parser skips the token after a command's '<':

  $ printf '@1 P(a)\n> get_pos <\n@2 P(b)\n>get_pos<@3 P(c)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): ("a")
  Current timepoint: 0
  @2 (time point 1): ("b")
  Current timepoint: 1
  @3 (time point 2): ("c")
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -old_log_parser
  @1 (time point 0): ("a")
  Current timepoint: 0
  ERROR while parsing log:
  l.log:3:2: Expected '@' or '>' but saw "2"
  [1]

Syntax errors, with the position of the offending token; with -ignore_parse_errors, the parser
drops the entry and resumes at the next '@', ';', or '>':

  $ printf '@1 P(a)\n@2 P(b,\n@3 P(c)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:3:1: Expected a tuple field but saw '@'
  [1]
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:3:1: Expected a tuple field but saw '@'
  @3 (time point 1): ("c")
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -old_log_parser
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:3:1: Expected a tuple field but saw '@'
  [1]
  $ printf '@1 P(a) $ @2 P(b)' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  ERROR while parsing log:
  l.log:1:9: Expected a predicate, '@', ';', or '>' but saw <unrecognized> ($)
  @2 (time point 0): ("b")
  $ printf '@1 P(a) @ @2 P(b)' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:1:11: Expected a time-stamp but saw '@'
  @2 (time point 1): ("b")
  $ printf '@1 P(a)\n@2 P("b)' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:6: Unterminated quoted string
  $ printf '@1 P(a)\n@2 P(b' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:7: Expected ',' or ')' but saw <EOF>
  $ printf '@1 P(a) > <' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:1:11: Expected a command name but saw '<'

Errors in an entry that the grammar leaves to the monitor, located at the entry's '@': a
predicate outside the signature and a timestamp that is not a number.  The entry is dropped:

  $ printf '@1 P(a)\n@2 P(b)\n  X(c)\n@3 P(d)\n@x P(e)\n@4 P(f)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:1: Predicate X was not defined in the signature.
  @3 (time point 1): ("d")
  ERROR while parsing log:
  l.log:5:1: Cannot convert x into a timestamp
  @4 (time point 2): ("f")
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -verified -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:1: Predicate X was not defined in the signature.
  @3 (time point 1): ("d")
  ERROR while parsing log:
  l.log:5:1: Cannot convert x into a timestamp
  @4 (time point 2): ("f")

A predicate named by the empty quoted string is looked up like any other:

  $ printf '@1 ""() P(b)\n@2 P(c)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  ERROR while parsing log:
  l.log:1:1: Predicate  was not defined in the signature.
  @2 (time point 0): ("c")

A quoted string that is not closed contains the rest of the log, also after an error:

  $ printf '@1 P(a)\n@2 P(b c")\n@3 P(c)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:8: Expected ',' or ')' but saw "c"
  ERROR while parsing log:
  l.log:2:9: Unterminated quoted string

The parameters of commands:

  $ printf '@1 P(a)\n> get_pos a {b} <\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:1: Expected a string or '<' but saw '{'
  [1]
  $ printf '@1 P(a)\n> set_slicer {{(1,(a))},{(1,2)},{(3,4)}} <\n@2 P(b)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log
  @1 (time point 0): ("a")
  Slicing parameters updated
  @2 (time point 1): ("b")
  $ printf '@1 P(a)\n> set_slicer {{(x,(a))},{(1,2)},{(3,4)}} <\n@2 P(b)\n' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  @1 (time point 0): ("a")
  ERROR while parsing log:
  l.log:2:1: Expected an integer but saw "x"
  @2 (time point 1): ("b")

The log is read in chunks of 4096 bytes.  Lexemes, entries, and line counts across chunks:

  $ awk 'BEGIN { s = ""; for (i = 0; i < 10000; i++) s = s "x"; printf "@1 P(%s) P(\"%s\\\\\\\" %s\")\n", s, s, s }' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log | cut -c 1-40
  @1 (time point 0): ("xxxxxxxxxxxxxxxxxxx
  $ monpoly -sig s.sig -formula p.mfotl -log l.log | md5sum
  8073434702d3730fd5463ec8f97965c7  -
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -old_log_parser | md5sum
  8073434702d3730fd5463ec8f97965c7  -
  $ awk 'BEGIN { for (i = 0; i < 5000; i++) printf "@%d P(a%d)\r\n", i, i; print "@5000 P(,)" }' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log 2> /dev/null | wc -l
  5000
  $ monpoly -sig s.sig -formula p.mfotl -log l.log > /dev/null
  ERROR while parsing log:
  l.log:5001:9: Expected a tuple field or ')' but saw ','
  [1]
  $ awk 'BEGIN { printf "\n\n@1"; for (i = 0; i < 5000; i++) printf " P(a%d)\n", i; print "X(a) @2 P(b)" }' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log -ignore_parse_errors
  ERROR while parsing log:
  l.log:3:1: Predicate X was not defined in the signature.
  @2 (time point 0): ("b")

A lexeme that spans many chunks takes time linear in its length (here about 1000 chunks):

  $ awk 'BEGIN { s = "x"; for (i = 0; i < 22; i++) s = s s; printf "@1 P(\"%s\") @2 P(b)\n", s }' > l.log
  $ monpoly -sig s.sig -formula p.mfotl -log l.log | wc -c
  4194353
