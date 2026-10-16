  $ echo 'LET a(s) = s <- SUM x p(x) IN a(5)' > test40_1.mfotl
  $ verimon -sig test40.sig -formula test40_1.mfotl -log test40.log -unfold_let no
  @2 (time point 1): true
  $ verimon -sig test40.sig -formula test40_1.mfotl -log test40.log -unfold_let full
  @2 (time point 1): true

  $ echo 'LET a(s) = s <- SUM x p(x) IN a(2 + 3)' > test40_2.mfotl
  $ verimon -sig test40.sig -formula test40_2.mfotl -log test40.log -unfold_let no
  @2 (time point 1): true
  $ verimon -sig test40.sig -formula test40_2.mfotl -log test40.log -unfold_let full
  @2 (time point 1): true

  $ echo 'LET a(s, y) = s <- SUM x; y q(x, y) IN a(s, 0)' > test40_3.mfotl
  $ verimon -sig test40.sig -formula test40_3.mfotl -log test40.log -unfold_let no
  @1 (time point 0): (4)
  $ verimon -sig test40.sig -formula test40_3.mfotl -log test40.log -unfold_let full
  @1 (time point 0): (4)
