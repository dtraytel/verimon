Safe-range:
  $ echo 'P(x) AND ( 0 =  0)' > test4_1.mfotl
  $ verimon -sig test4.sig -formula test4_1.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 =  1)' > test4_2.mfotl
  $ verimon -sig test4.sig -formula test4_2.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x =  0)' > test4_3.mfotl
  $ verimon -sig test4.sig -formula test4_3.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 = x)' > test4_4.mfotl
  $ verimon -sig test4.sig -formula test4_4.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x = x)' > test4_5.mfotl
  $ verimon -sig test4.sig -formula test4_5.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Domain independent but not safe-range:
  $ echo 'P(x) AND (x = y)' > test4_6.mfotl
  $ verimon -sig test4.sig -formula test4_6.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 <  0)' > test4_7.mfotl
  $ verimon -sig test4.sig -formula test4_7.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 <  1)' > test4_8.mfotl
  $ verimon -sig test4.sig -formula test4_8.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x <  0)' > test4_9.mfotl
  $ verimon -sig test4.sig -formula test4_9.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x <  1)' > test4_10.mfotl
  $ verimon -sig test4.sig -formula test4_10.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 < x)' > test4_11.mfotl
  $ verimon -sig test4.sig -formula test4_11.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x < x)' > test4_12.mfotl
  $ verimon -sig test4.sig -formula test4_12.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Domain dependent:
  $ echo 'P(x) AND (x < y)' > test4_13.mfotl
  $ verimon -sig test4.sig -formula test4_13.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'P(y) AND (x =  0)' > test4_14.mfotl
  $ verimon -sig test4.sig -formula test4_14.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,0))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(y) AND ( 0 = x)' > test4_15.mfotl
  $ verimon -sig test4.sig -formula test4_15.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,0))
  At time point 2:
  @300 (time point 2): ()

Domain dependent:
  $ echo 'P(y) AND (x = x)' > test4_16.mfotl
  $ verimon -sig test4.sig -formula test4_16.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain independent but not safe-range:
  $ echo 'P(y) AND (x = y)' > test4_17.mfotl
  $ verimon -sig test4.sig -formula test4_17.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,1))
  At time point 2:
  @300 (time point 2): ()

Domain dependent (integers):
  $ echo 'P(y) AND (x <  0)' > test4_18.mfotl
  $ verimon -sig test4.sig -formula test4_18.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo 'P(y) AND (x <  1)' > test4_19.mfotl
  $ verimon -sig test4.sig -formula test4_19.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND ( 0 < x)' > test4_20.mfotl
  $ verimon -sig test4.sig -formula test4_20.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'P(y) AND (x < x)' > test4_21.mfotl
  $ verimon -sig test4.sig -formula test4_21.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo 'P(y) AND (x < y)' > test4_22.mfotl
  $ verimon -sig test4.sig -formula test4_22.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'P(x) AND NOT ( 0 =  0)' > test4_23.mfotl
  $ verimon -sig test4.sig -formula test4_23.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 =  1)' > test4_24.mfotl
  $ verimon -sig test4.sig -formula test4_24.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x =  0)' > test4_25.mfotl
  $ verimon -sig test4.sig -formula test4_25.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 = x)' > test4_26.mfotl
  $ verimon -sig test4.sig -formula test4_26.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x = x)' > test4_27.mfotl
  $ verimon -sig test4.sig -formula test4_27.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Domain dependent:
  $ echo 'P(x) AND NOT (x = y)' > test4_28.mfotl
  $ verimon -sig test4.sig -formula test4_28.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'P(x) AND NOT ( 0 <  0)' > test4_29.mfotl
  $ verimon -sig test4.sig -formula test4_29.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 <  1)' > test4_30.mfotl
  $ verimon -sig test4.sig -formula test4_30.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x <  0)' > test4_31.mfotl
  $ verimon -sig test4.sig -formula test4_31.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x <  1)' > test4_32.mfotl
  $ verimon -sig test4.sig -formula test4_32.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 < x)' > test4_33.mfotl
  $ verimon -sig test4.sig -formula test4_33.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x < x)' > test4_34.mfotl
  $ verimon -sig test4.sig -formula test4_34.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Domain dependent (integers):
  $ echo 'P(x) AND NOT (x < y)' > test4_35.mfotl
  $ verimon -sig test4.sig -formula test4_35.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x =  0)' > test4_36.mfotl
  $ verimon -sig test4.sig -formula test4_36.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT ( 0 = x)' > test4_37.mfotl
  $ verimon -sig test4.sig -formula test4_37.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'P(y) AND NOT (x = x)' > test4_38.mfotl
  $ verimon -sig test4.sig -formula test4_38.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x = y)' > test4_39.mfotl
  $ verimon -sig test4.sig -formula test4_39.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x <  0)' > test4_40.mfotl
  $ verimon -sig test4.sig -formula test4_40.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x <  1)' > test4_41.mfotl
  $ verimon -sig test4.sig -formula test4_41.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo 'P(y) AND NOT ( 0 < x)' > test4_42.mfotl
  $ verimon -sig test4.sig -formula test4_42.mfotl -log test4.log -verbose -nonewlastts
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x < x)' > test4_43.mfotl
  $ verimon -sig test4.sig -formula test4_43.mfotl -log test4.log -verbose -nonewlastts
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'P(y) AND NOT (x < y)' > test4_44.mfotl
  $ verimon -sig test4.sig -formula test4_44.mfotl -log test4.log -verbose -nonewlastts
  The sequence of free variables is: (y,x)
  The analyzed formula is NOT monitorable: not monitorable
