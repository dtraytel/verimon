The formula file is read by the verified formula parser (thys/MFODL_Parser). Formulas it
rejects are reported as parse errors, with MonPoly's messages:

  $ echo 'R(x) AND' > f.mfotl
  $ verimon -check -sig regex.sig -formula f.mfotl 2>&1 | head -2
  [Main.main] Failed to parse formula file
  Fatal error: exception Failure("[Main.main] the verified parser rejects the formula")
