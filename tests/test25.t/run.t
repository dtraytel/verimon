  $ echo '(EVENTUALLY[0,1]  (EVENTUALLY [0,1] Q(x)))' > test25_1.mfotl
  $ verimon -sig test25.sig -formula test25_1.mfotl -log test25.log -verbose -nonewlastts
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  @0 (time point 0): ((42))
  At time point 4:
  @1 (time point 1): ((42))
  At time point 5:
  @2 (time point 2): ((42))

  $ echo '((NOT (0 = 1)) UNTIL[0,1]  (EVENTUALLY [0,1] Q(x)))' > test25_2.mfotl
  $ verimon -sig test25.sig -formula test25_2.mfotl -log test25.log -verbose -nonewlastts
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  @0 (time point 0): ((42))
  At time point 4:
  @1 (time point 1): ((42))
  At time point 5:
  @2 (time point 2): ((42))
