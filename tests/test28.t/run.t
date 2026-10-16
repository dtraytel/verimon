  $ echo 'PREVIOUS (0,0) P(x)' > test28_1.mfotl
  $ verimon -sig test28.sig -formula test28_1.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS [0,0) P(x)' > test28_2.mfotl
  $ verimon -sig test28.sig -formula test28_2.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS (0,0] P(x)' > test28_3.mfotl
  $ verimon -sig test28.sig -formula test28_3.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (0,0) P(x)' > test28_4.mfotl
  $ verimon -sig test28.sig -formula test28_4.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT [0,0) P(x)' > test28_5.mfotl
  $ verimon -sig test28.sig -formula test28_5.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (0,0] P(x)' > test28_6.mfotl
  $ verimon -sig test28.sig -formula test28_6.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(0,0) Q(x)' > test28_7.mfotl
  $ verimon -sig test28.sig -formula test28_7.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE[0,0) Q(x)' > test28_8.mfotl
  $ verimon -sig test28.sig -formula test28_8.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(0,0] Q(x)' > test28_9.mfotl
  $ verimon -sig test28.sig -formula test28_9.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(0,0) Q(x)' > test28_10.mfotl
  $ verimon -sig test28.sig -formula test28_10.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL[0,0) Q(x)' > test28_11.mfotl
  $ verimon -sig test28.sig -formula test28_11.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(0,0] Q(x)' > test28_12.mfotl
  $ verimon -sig test28.sig -formula test28_12.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(0,0) Q(x)' > test28_13.mfotl
  $ verimon -sig test28.sig -formula test28_13.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL[0,0) Q(x)' > test28_14.mfotl
  $ verimon -sig test28.sig -formula test28_14.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(0,0] Q(x)' > test28_15.mfotl
  $ verimon -sig test28.sig -formula test28_15.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (0,0) P(x)' > test28_16.mfotl
  $ verimon -sig test28.sig -formula test28_16.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE [0,0) P(x)' > test28_17.mfotl
  $ verimon -sig test28.sig -formula test28_17.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (0,0] P(x)' > test28_18.mfotl
  $ verimon -sig test28.sig -formula test28_18.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (0,0) P(x)' > test28_19.mfotl
  $ verimon -sig test28.sig -formula test28_19.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY [0,0) P(x)' > test28_20.mfotl
  $ verimon -sig test28.sig -formula test28_20.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (0,0] P(x)' > test28_21.mfotl
  $ verimon -sig test28.sig -formula test28_21.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (0,0) P(x)' > test28_22.mfotl
  $ verimon -sig test28.sig -formula test28_22.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS [0,0) P(x)' > test28_23.mfotl
  $ verimon -sig test28.sig -formula test28_23.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (0,0] P(x)' > test28_24.mfotl
  $ verimon -sig test28.sig -formula test28_24.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (0,0) P(x)' > test28_25.mfotl
  $ verimon -sig test28.sig -formula test28_25.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS [0,0) P(x)' > test28_26.mfotl
  $ verimon -sig test28.sig -formula test28_26.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (0,0] P(x)' > test28_27.mfotl
  $ verimon -sig test28.sig -formula test28_27.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS (4,1) P(x)' > test28_28.mfotl
  $ verimon -sig test28.sig -formula test28_28.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS [4,1) P(x)' > test28_29.mfotl
  $ verimon -sig test28.sig -formula test28_29.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS (4,1] P(x)' > test28_30.mfotl
  $ verimon -sig test28.sig -formula test28_30.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (4,1) P(x)' > test28_31.mfotl
  $ verimon -sig test28.sig -formula test28_31.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT [4,1) P(x)' > test28_32.mfotl
  $ verimon -sig test28.sig -formula test28_32.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (4,1] P(x)' > test28_33.mfotl
  $ verimon -sig test28.sig -formula test28_33.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(4,1) Q(x)' > test28_34.mfotl
  $ verimon -sig test28.sig -formula test28_34.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE[4,1) Q(x)' > test28_35.mfotl
  $ verimon -sig test28.sig -formula test28_35.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(4,1] Q(x)' > test28_36.mfotl
  $ verimon -sig test28.sig -formula test28_36.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(4,1) Q(x)' > test28_37.mfotl
  $ verimon -sig test28.sig -formula test28_37.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL[4,1) Q(x)' > test28_38.mfotl
  $ verimon -sig test28.sig -formula test28_38.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(4,1] Q(x)' > test28_39.mfotl
  $ verimon -sig test28.sig -formula test28_39.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(4,1) Q(x)' > test28_40.mfotl
  $ verimon -sig test28.sig -formula test28_40.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL[4,1) Q(x)' > test28_41.mfotl
  $ verimon -sig test28.sig -formula test28_41.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(4,1] Q(x)' > test28_42.mfotl
  $ verimon -sig test28.sig -formula test28_42.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (4,1) P(x)' > test28_43.mfotl
  $ verimon -sig test28.sig -formula test28_43.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE [4,1) P(x)' > test28_44.mfotl
  $ verimon -sig test28.sig -formula test28_44.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (4,1] P(x)' > test28_45.mfotl
  $ verimon -sig test28.sig -formula test28_45.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (4,1) P(x)' > test28_46.mfotl
  $ verimon -sig test28.sig -formula test28_46.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY [4,1) P(x)' > test28_47.mfotl
  $ verimon -sig test28.sig -formula test28_47.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (4,1] P(x)' > test28_48.mfotl
  $ verimon -sig test28.sig -formula test28_48.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (4,1) P(x)' > test28_49.mfotl
  $ verimon -sig test28.sig -formula test28_49.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS [4,1) P(x)' > test28_50.mfotl
  $ verimon -sig test28.sig -formula test28_50.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (4,1] P(x)' > test28_51.mfotl
  $ verimon -sig test28.sig -formula test28_51.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (4,1) P(x)' > test28_52.mfotl
  $ verimon -sig test28.sig -formula test28_52.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS [4,1) P(x)' > test28_53.mfotl
  $ verimon -sig test28.sig -formula test28_53.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (4,1] P(x)' > test28_54.mfotl
  $ verimon -sig test28.sig -formula test28_54.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS (-4,-1) P(x)' > test28_55.mfotl
  $ verimon -sig test28.sig -formula test28_55.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS [-4,-1) P(x)' > test28_56.mfotl
  $ verimon -sig test28.sig -formula test28_56.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PREVIOUS (-4,-1] P(x)' > test28_57.mfotl
  $ verimon -sig test28.sig -formula test28_57.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (-4,-1) P(x)' > test28_58.mfotl
  $ verimon -sig test28.sig -formula test28_58.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT [-4,-1) P(x)' > test28_59.mfotl
  $ verimon -sig test28.sig -formula test28_59.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'NEXT (-4,-1] P(x)' > test28_60.mfotl
  $ verimon -sig test28.sig -formula test28_60.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(-4,-1) Q(x)' > test28_61.mfotl
  $ verimon -sig test28.sig -formula test28_61.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE[-4,-1) Q(x)' > test28_62.mfotl
  $ verimon -sig test28.sig -formula test28_62.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) SINCE(-4,-1] Q(x)' > test28_63.mfotl
  $ verimon -sig test28.sig -formula test28_63.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(-4,-1) Q(x)' > test28_64.mfotl
  $ verimon -sig test28.sig -formula test28_64.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL[-4,-1) Q(x)' > test28_65.mfotl
  $ verimon -sig test28.sig -formula test28_65.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'P(x) UNTIL(-4,-1] Q(x)' > test28_66.mfotl
  $ verimon -sig test28.sig -formula test28_66.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(-4,-1) Q(x)' > test28_67.mfotl
  $ verimon -sig test28.sig -formula test28_67.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL[-4,-1) Q(x)' > test28_68.mfotl
  $ verimon -sig test28.sig -formula test28_68.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo '(NOT P(x)) UNTIL(-4,-1] Q(x)' > test28_69.mfotl
  $ verimon -sig test28.sig -formula test28_69.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (-4,-1) P(x)' > test28_70.mfotl
  $ verimon -sig test28.sig -formula test28_70.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE [-4,-1) P(x)' > test28_71.mfotl
  $ verimon -sig test28.sig -formula test28_71.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ONCE (-4,-1] P(x)' > test28_72.mfotl
  $ verimon -sig test28.sig -formula test28_72.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (-4,-1) P(x)' > test28_73.mfotl
  $ verimon -sig test28.sig -formula test28_73.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY [-4,-1) P(x)' > test28_74.mfotl
  $ verimon -sig test28.sig -formula test28_74.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'EVENTUALLY (-4,-1] P(x)' > test28_75.mfotl
  $ verimon -sig test28.sig -formula test28_75.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (-4,-1) P(x)' > test28_76.mfotl
  $ verimon -sig test28.sig -formula test28_76.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS [-4,-1) P(x)' > test28_77.mfotl
  $ verimon -sig test28.sig -formula test28_77.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'PAST_ALWAYS (-4,-1] P(x)' > test28_78.mfotl
  $ verimon -sig test28.sig -formula test28_78.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (-4,-1) P(x)' > test28_79.mfotl
  $ verimon -sig test28.sig -formula test28_79.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS [-4,-1) P(x)' > test28_80.mfotl
  $ verimon -sig test28.sig -formula test28_80.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]

  $ echo 'ALWAYS (-4,-1] P(x)' > test28_81.mfotl
  $ verimon -sig test28.sig -formula test28_81.mfotl -log test28.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.check_wff] The formula contains a negative or empty interval")
  [2]
