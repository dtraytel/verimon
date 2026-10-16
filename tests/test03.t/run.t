Safe-range:
  $ echo '( 0 =  0)' > test3_1.mfotl
  $ verimon -sig test3.sig -formula test3_1.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @200 (time point 1): true

Safe-range:
  $ echo '( 0 =  1)' > test3_2.mfotl
  $ verimon -sig test3.sig -formula test3_2.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): false
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo '(x =  0)' > test3_3.mfotl
  $ verimon -sig test3.sig -formula test3_3.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((0))

Safe-range:
  $ echo '( 0 = x)' > test3_4.mfotl
  $ verimon -sig test3.sig -formula test3_4.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((0))

Domain dependent:
  $ echo '(x = x)' > test3_5.mfotl
  $ verimon -sig test3.sig -formula test3_5.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo '(x = y)' > test3_6.mfotl
  $ verimon -sig test3.sig -formula test3_6.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo '( 0 <  0)' > test3_7.mfotl
  $ verimon -sig test3.sig -formula test3_7.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: ()
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo '( 0 <  1)' > test3_8.mfotl
  $ verimon -sig test3.sig -formula test3_8.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: ()
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo '(x <  0)' > test3_9.mfotl
  $ verimon -sig test3.sig -formula test3_9.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo '(x <  5)' > test3_10.mfotl
  $ verimon -sig test3.sig -formula test3_10.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo '( 0 < x)' > test3_11.mfotl
  $ verimon -sig test3.sig -formula test3_11.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo '(x < x)' > test3_12.mfotl
  $ verimon -sig test3.sig -formula test3_12.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo '(x < y)' > test3_13.mfotl
  $ verimon -sig test3.sig -formula test3_13.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND ( 0 =  0)' > test3_14.mfotl
  $ verimon -sig test3.sig -formula test3_14.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo 'T() AND ( 0 =  1)' > test3_15.mfotl
  $ verimon -sig test3.sig -formula test3_15.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): false
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo 'T() AND (x =  0)' > test3_16.mfotl
  $ verimon -sig test3.sig -formula test3_16.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()

Safe-range:
  $ echo 'T() AND ( 0 = x)' > test3_17.mfotl
  $ verimon -sig test3.sig -formula test3_17.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()

Domain dependent:
  $ echo 'T() AND (x = x)' > test3_18.mfotl
  $ verimon -sig test3.sig -formula test3_18.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND (x = y)' > test3_19.mfotl
  $ verimon -sig test3.sig -formula test3_19.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND ( 0 <  0)' > test3_20.mfotl
  $ verimon -sig test3.sig -formula test3_20.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): false
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo 'T() AND ( 0 <  1)' > test3_21.mfotl
  $ verimon -sig test3.sig -formula test3_21.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @200 (time point 1): false

Domain dependent (integers):
  $ echo 'T() AND (x <  0)' > test3_22.mfotl
  $ verimon -sig test3.sig -formula test3_22.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo 'T() AND (x <  1)' > test3_23.mfotl
  $ verimon -sig test3.sig -formula test3_23.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND ( 0 < x)' > test3_24.mfotl
  $ verimon -sig test3.sig -formula test3_24.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND (x < x) ' > test3_25.mfotl
  $ verimon -sig test3.sig -formula test3_25.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND (x < y)' > test3_26.mfotl
  $ verimon -sig test3.sig -formula test3_26.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND NOT ( 0 =  0)' > test3_27.mfotl
  $ verimon -sig test3.sig -formula test3_27.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): false
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo 'T() AND NOT ( 0 =  1)' > test3_28.mfotl
  $ verimon -sig test3.sig -formula test3_28.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @200 (time point 1): false

Domain dependent:
  $ echo 'T() AND NOT (x =  0)' > test3_29.mfotl
  $ verimon -sig test3.sig -formula test3_29.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND NOT ( 0 = x)' > test3_30.mfotl
  $ verimon -sig test3.sig -formula test3_30.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND NOT (x = x) ' > test3_31.mfotl
  $ verimon -sig test3.sig -formula test3_31.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND NOT (x = y)' > test3_32.mfotl
  $ verimon -sig test3.sig -formula test3_32.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable

Safe-range:
  $ echo 'T() AND NOT ( 0 <  0)' > test3_33.mfotl
  $ verimon -sig test3.sig -formula test3_33.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @200 (time point 1): false

Safe-range:
  $ echo 'T() AND NOT ( 0 <  1)' > test3_34.mfotl
  $ verimon -sig test3.sig -formula test3_34.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): false
  At time point 1:
  @200 (time point 1): false

Domain dependent:
  $ echo 'T() AND NOT (x <  0)' > test3_35.mfotl
  $ verimon -sig test3.sig -formula test3_35.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND NOT (x <  1)' > test3_36.mfotl
  $ verimon -sig test3.sig -formula test3_36.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent (integers):
  $ echo 'T() AND NOT ( 5 < x)' > test3_37.mfotl
  $ verimon -sig test3.sig -formula test3_37.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND NOT (x < x)' > test3_38.mfotl
  $ verimon -sig test3.sig -formula test3_38.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable: not monitorable

Domain dependent:
  $ echo 'T() AND NOT (x < y)' > test3_39.mfotl
  $ verimon -sig test3.sig -formula test3_39.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable: not monitorable
