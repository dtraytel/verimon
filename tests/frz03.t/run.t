FRZ with AND: frozen q(x) intersected with live b(x) at the same timepoint.
At time 0: q={1,2}, b={2}, intersection={2}.
At time 1: q={3}, b={1}, intersection={}; no output.
At time 2: both empty; no output.
  $ monpoly -sig frz03.sig -formula frz03.mfotl -log frz03.log -verified
  @0 (time point 0): (2)
  $ monpoly -sig frz03.sig -formula frz03.mfotl -log frz03.log -nofilteremptytp
  @0 (time point 0): (2)
