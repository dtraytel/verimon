Error case: FRZ q(x) = undeclared(x) IN q(x) where undeclared is not in the signature.
The type-checker must reject this with an unknown-predicate error.
  $ monpoly -verified -sig frz12.sig -formula frz12.mfotl -log frz12.log
  Fatal error: exception Failure("[Rewriting.check_syntax] unknown predicate undeclared/1 in input formula")
  [2]
