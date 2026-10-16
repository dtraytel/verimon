Verimon should not process the new last timestamp when formula is past-only.
This was the case when the -no_rw flag was set
  $ echo 'ONCE[0,*) A()' > test42.mfotl
  $ verimon -sig test42.sig -formula test42.mfotl -log test42.log -no_rw
  @0 (time point 0): true
  $ verimon -sig test42.sig -formula test42.mfotl -log test42.log
  @0 (time point 0): true
