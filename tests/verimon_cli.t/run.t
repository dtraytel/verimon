The verified monitor with MonPoly's command line (thys/VeriMon_CLI): the formula is parsed by
the verified parser, the signature read by the verified reader, and the monitor started and
run as by monpoly -verified.

  $ echo 'P(x) AND NOT Q(x)' > f1.mfotl
  $ verimon-cli -sig s.sig -formula f1.mfotl -log good.log
  @110 (time point 1): (3)
  @120 (time point 2): (3)
  $ verimon-cli -sig s.sig -formula f1.mfotl -log good.log -verbose
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3))
  At time point 2:
  @120 (time point 2): ((3))
  At time point 3:
  @130 (time point 3): ()
  $ verimon-cli -sig s.sig -formula f1.mfotl -log good.log -negate -check
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable
  $ echo 'ONCE[0,20] R(x,y)' > f2.mfotl
  $ verimon-cli -sig s.sig -formula f2.mfotl -log good.log -unix
  @70-0-1 0:1:40 (time point 0): (1,"a")
  @70-0-1 0:1:50 (time point 1): (1,"a")
  @70-0-1 0:2:0 (time point 2): (1,"a") (3,"b c")
  @70-0-1 0:2:10 (time point 3): (3,"b c")
  $ verimon-cli -sig s.sig -formula f2.mfotl -sigout
  x:int, y:string
  $ echo 'EVENTUALLY[0,10] P(x)' > f3.mfotl
  $ verimon-cli -sig s.sig -formula f3.mfotl -log good.log
  @100 (time point 0): (1) (2) (3)
  @110 (time point 1): (2) (3)
  @120 (time point 2): (3)
  $ verimon-cli -sig s.sig -formula f3.mfotl -log good.log -nonewlastts
  @100 (time point 0): (1) (2) (3)
  @110 (time point 1): (2) (3)
  $ echo 'c <- CNT x; y ONCE[0,20] R(x,y)' > f4.mfotl
  $ verimon-cli -sig s.sig -formula f4.mfotl -log good.log
  @100 (time point 0): (1,"a")
  @110 (time point 1): (1,"a")
  @120 (time point 2): (1,"a") (1,"b c")
  @130 (time point 3): (1,"b c")

Errors in the log, with MonPoly's messages and positions:

  $ verimon-cli -sig s.sig -formula f1.mfotl -log bad.log
  ERROR while parsing log:
  bad.log:2:10: Expected ',' or ')' but saw "Q"
  [1]
  $ verimon-cli -sig s.sig -formula f1.mfotl -log bad.log -ignore_parse_errors
  ERROR while parsing log:
  bad.log:2:10: Expected ',' or ')' but saw "Q"
  @120 (time point 1): (3)
  $ verimon-cli -sig s.sig -formula f1.mfotl -log order.log
  @100 (time point 0): (1)
  ERROR: Out of order timestamp 90 (previous: 100)
  [1]
  $ verimon-cli -sig s.sig -formula f1.mfotl -log order.log -unix
  @70-0-1 0:1:40 (time point 0): (1)
  ERROR: Out of order timestamp 70-0-1 0:1:30 (previous: 70-0-1 0:1:40)
  [1]

MonPoly's checks of the input formula and the verified preparation:

  $ echo 'P(x) AND S(x)' > e1.mfotl
  $ verimon-cli -sig s.sig -formula e1.mfotl -log good.log
  Fatal error: exception Failure("[Rewriting.check_syntax] unknown predicate S/1 in input formula")
  [2]
  $ echo 'ONCE[3,2] P(x)' > e2.mfotl
  $ verimon-cli -sig s.sig -formula e2.mfotl -log good.log
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]
  $ echo 'EVENTUALLY P(x)' > e3.mfotl
  $ verimon-cli -sig s.sig -formula e3.mfotl -log good.log
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains an unbounded future temporal operator. It is hence not monitorable.")
  [2]
  $ echo 'P(x) OR Q(y)' > e4.mfotl
  $ verimon-cli -sig s.sig -formula e4.mfotl -log good.log
  The formula is NOT monitorable. Use the -check or -verbose flags.
  $ verimon-cli -sig s.sig -formula e4.mfotl -log good.log -check
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable
  $ echo 'P(x) AND x = "a"' > e5.mfotl
  $ verimon-cli -sig s.sig -formula e5.mfotl -log good.log
  Fatal error: exception Failure("Error during the verified preparation of the formula: clash of types string and int")
  [2]
  $ echo 'P(x) AND' > e6.mfotl
  $ verimon-cli -sig s.sig -formula e6.mfotl -log good.log
  [Main.main] Failed to parse formula file
  Fatal error: exception Failure("[Main.main] the verified parser rejects the formula")
  [2]
  $ echo 'P(x:int) Q(' > e.sig
  $ verimon-cli -sig e.sig -formula f1.mfotl -log good.log
  Fatal error: exception Failure("Error while parsing signature: Expected a string or ')' but saw <EOF>")
  [2]

The command line:

  $ verimon-cli -formula f1.mfotl
  Usage: verimon -sig <file> -formula <file> [-negate] [-log <file>]
                 [-help] [-version] [-verbose] [-no_rw] [-no_mw]
                 [-check] [-sigout] [-unix] [-mem] [-nonewlastts] [-nofilterrel]
                 [-ignore_parse_errors] [-stop_at_first_viol]
  [2]
  $ verimon-cli -sig s.sig -formula f1.mfotl -frobnicate
  verimon-cli: unknown option '-frobnicate'.
  Usage: verimon -sig <file> -formula <file> [-negate] [-log <file>]
                 [-help] [-version] [-verbose] [-no_rw] [-no_mw]
                 [-check] [-sigout] [-unix] [-mem] [-nonewlastts] [-nofilterrel]
                 [-ignore_parse_errors] [-stop_at_first_viol]
    -sig 		Choose the signature file
    -formula 	Choose the formula file
    -negate 	Analyze the negation of the input formula
    -log 		Choose the log file
    -version 	Display the version (and exit)
    -debug 	Accepted and ignored by the verified monitor
    -verbose 	Turn on verbose mode
    -check 	Check if formula is monitorable (and exit)
    -no_rw 	No formula rewrite
    -no_trigger 	Accepted and ignored by the verified monitor
    -sigout 	Show the output signature (and exit)
    -unix 	Timestamps represent Unix time
    -mem 		Show maximum memory usage on stderr
    -nonewlastts 	Do not add a last maximal timestamp
    -nofilterrel 	Disable filter_rel module
    -nofilteremptytp 	Accepted and ignored by the verified monitor
    -stats 		Accepted and ignored by the verified monitor
    -ignore_parse_errors 	Ignore log parse errors
    -old_log_parser 	Accepted and ignored: the verified monitor reads the log with the verified parser
    -verified_log_parser 	Read the log with the verified parser (thys/Log_Parser; always)
    -stop_at_out_of_order_ts 	Accepted and ignored: the verified monitor stops at an out-of-order timestamp
    -stop_at_first_viol 	Stop at first encountered violation
    -load 	Not supported by the verified monitor
    -combine 	Not supported by the verified monitor
    -verified_parser 	Parse the formula with the verified parser (thys/MFODL_Parser; always)
    -verified 	Run the verified monitor (always)
    -dense 	Deprecated, accepted and ignored
    -heap_maps 	Deprecated, accepted and ignored
    -vdense 	Deprecated, accepted and ignored
    -heap_join_min 	Deprecated, accepted and ignored
    -bulk_min 	Deprecated, accepted and ignored
    -heap_since 	Deprecated, accepted and ignored
    -gc_space_overhead 	OCaml GC space_overhead in percent (default: 500); larger values trade memory for speed
    -gc_minor_heap 	OCaml GC minor_heap_size in words (default: 768k under OCaml 4, 4M under OCaml 5)
    -no_mw 	No multi-way join
    -generic_join 	Deprecated, accepted and ignored
    -imperative_join 	Deprecated, accepted and ignored
    -unfold_let {no|full|smart}	Accepted and ignored by the verified monitor
    -strcache 	Accepted and ignored by the verified monitor
    -profile 	Accepted and ignored by the verified monitor
    -help   Display this list of options
    --help   Display this list of options
  [2]
  $ verimon-cli -sig s.sig -formula f1.mfotl -load x.sta
  Fatal error: exception Failure("-load and -combine are not supported by the verified monitor")
  [2]
