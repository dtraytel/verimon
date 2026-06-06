Exercise MonPoly's special log-stream commands and the state save/load driver
(MonPoly-only functionality). Commands are accepted at end-of-log, so each is
run in its own invocation.

  $ echo 'ONCE[0,2] R(x)' > f.mfotl

get_pos reports the current time-point:

  $ printf '@0 R(1);\n@1 R(2);\n>get_pos<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log 2>&1 | grep -v 'time point'
  Current timepoint: 1

print dumps the current extended formula (to stderr):

  $ printf '@0 R(1);\n>print<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log 2>&1 | grep -v 'time point'
  Current extended formula:
  SINCE[???]: sinf={srel2=None; saux=???}
   ERel
   R(x): inf=()
  


terminate and print_and_exit stop processing:

  $ printf '@0 R(1);\n@1 R(2);\n>terminate<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log 2>&1 | grep Terminated
  Terminated at timepoint: 1
  $ printf '@0 R(1);\n>print_and_exit<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log 2>&1 | grep Terminated
  Terminated at timepoint: 0

LATENCY prints timing stats (timestamp is non-deterministic, so discard output
but still exercise the handler):

  $ printf '@0 R(1);\n>LATENCY tag<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log > /dev/null 2>&1
  $ echo $?
  0

save_and_exit marshals the state; -load resumes from it:

  $ printf '@0 R(1);\n@1 R(2);\n>save_and_exit st.sta<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log 2>&1 | grep -v 'time point'
  Saved state
  $ printf '@2 R(3);\n@3 R(1);\n' > l2.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l2.log -load st.sta 2>&1 | grep -v 'time point'
  Loaded state

An unrecognized command is reported; -ignore_parse_errors keeps going:

  $ printf '@0 R(1);\n>bogus<\n' > l.log
  $ monpoly -sig cov.sig -formula f.mfotl -log l.log -ignore_parse_errors 2>&1 | grep -i 'Unrecognized'
  ERROR: Unrecognized command: bogus

-stop_at_first_viol halts after the first non-empty result:

  $ echo 'R(x)' > g.mfotl
  $ printf '@0 R(1) R(2);\n@1 R(3);\n' > l.log
  $ monpoly -sig cov.sig -formula g.mfotl -log l.log -stop_at_first_viol 2>&1
  @0 (time point 0): (1)
