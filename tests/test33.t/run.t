Propagation of guarding conjunctions below quantifiers must not capture bound variables.

  $ echo 'P(x, y) AND EXISTS x. NOT Q(x, y)' > test33_1.mfotl
  $ verimon -sig test33.sig -formula test33_1.mfotl -log test33.log -verbose -nonewlastts
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

In capture-avoiding substitution, the fresh variables must also avoid variables introduced by the substitution.
(This test is brittle because _x1 must be one of the automatically generated variable names.)

  $ echo 'R(x,y,z) AND (EXISTS x, y. NOT EXISTS _x1. EXISTS _x1. S(x,y,_x1))' > test33_2.mfotl
  $ verimon -sig test33.sig -formula test33_2.mfotl -check
  The sequence of free variables is: (x,y,z)
  The analyzed formula is NOT monitorable: not monitorable
