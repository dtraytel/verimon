  $ echo '(NOT (NEXT P())) UNTIL[1,1] Q()' > test36_1.mfotl
  $ verimon -sig test36.sig -formula test36_1.mfotl -log test36.log

  $ echo '(NOT P()) UNTIL[1,1] (NEXT Q())' > test36_2.mfotl
  $ verimon -sig test36.sig -formula test36_2.mfotl -log test36.log

  $ echo '(NEXT P()) UNTIL[1,1] Q()' > test36_3.mfotl
  $ verimon -sig test36.sig -formula test36_3.mfotl -log test36.log

  $ echo 'P() UNTIL[1,1] (NEXT Q())' > test36_4.mfotl
  $ verimon -sig test36.sig -formula test36_4.mfotl -log test36.log
