  $ echo 'S(y) AND ((NOT P(y) AND Q(x)) SINCE[10,12] R(x,y))' > test34_1.mfotl
  $ verimon -sig test34.sig -formula test34_1.mfotl -log test34.log
  The formula is NOT monitorable. Use the -check or -verbose flags.
