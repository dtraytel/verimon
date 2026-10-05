  $ echo '(NEXT[0,0] (NEXT[0,0] (PREVIOUS (EVENTUALLY[0,0] FALSE))))' > test38.mfotl
  $ verimon -sig test38.sig -formula test38.mfotl -log test38.log -verbose -nonewlastts
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
