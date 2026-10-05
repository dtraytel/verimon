FRZ with nullary predicate: q() is true iff a(1) holds at outer time i.
At time 0: a(1) present, q() true. At time 1: only a(2), so a(1) absent, q() false.
At time 2: a absent; q() false. Only time 0 produces output.
  $ verimon -sig frz08.sig -formula frz08.mfotl -log frz08.log
  @0 (time point 0): true
