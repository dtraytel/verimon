Always-empty phi produces no output: FRZ q(x) = a(x) IN ONCE[0,*) q(x).
When phi is empty at every timepoint, q is always empty and psi never matches.
  $ monpoly -sig frz21.sig -formula frz21.mfotl -log frz21.log -verified
  $ monpoly -sig frz21.sig -formula frz21.mfotl -log frz21.log -nofilteremptytp
