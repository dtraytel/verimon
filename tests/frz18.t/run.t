Multi-predicate AND in phi: FRZ q(x) = (a(x) AND b(x)) IN q(x).
phi is the intersection of a and b; only values in both are frozen into q.
At time 0: a={1,2}, b={1,3}; q=a AND b={1}. At time 1: a={4}, b={4,5}; q={4}.
  $ monpoly -sig frz18.sig -formula frz18.mfotl -log frz18.log -verified
  @0 (time point 0): (1)
  @1 (time point 1): (4)
  $ monpoly -sig frz18.sig -formula frz18.mfotl -log frz18.log -nofilteremptytp
  @0 (time point 0): (1)
  @1 (time point 1): (4)
