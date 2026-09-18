The dense fragment's short forms of the assignment, the time point and the
timestamp, monitored by the verified kernel.  Both -verified and -verified -dense
are run so that the differential comparison covers the nodes.

  $ monpoly -verified -sig dense_nodes.sig -formula assign1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,2) (2,3)
  @2 (time point 1): (2,3) (3,4)
  @3 (time point 2): (3,4)
  @5 (time point 3): (1,2) (4,5)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula assign1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,2) (2,3)
  @2 (time point 1): (2,3) (3,4)
  @3 (time point 2): (3,4)
  @5 (time point 3): (1,2) (4,5)
  $ monpoly -verified -sig dense_nodes.sig -formula assign2.mfotl -log dense_nodes.log
  @1 (time point 0): (2) (4)
  @2 (time point 1): (4) (6)
  @3 (time point 2): (6)
  @5 (time point 3): (2) (8)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula assign2.mfotl -log dense_nodes.log
  @1 (time point 0): (2) (4)
  @2 (time point 1): (4) (6)
  @3 (time point 2): (6)
  @5 (time point 3): (2) (8)
  $ monpoly -verified -sig dense_nodes.sig -formula assign3.mfotl -log dense_nodes.log
  @1 (time point 0): (1,3) (2,4)
  @2 (time point 1): (2,4) (3,5)
  @3 (time point 2): (3,5)
  @5 (time point 3): (1,3) (4,6)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula assign3.mfotl -log dense_nodes.log
  @1 (time point 0): (1,3) (2,4)
  @2 (time point 1): (2,4) (3,5)
  @3 (time point 2): (3,5)
  @5 (time point 3): (1,3) (4,6)
  $ monpoly -verified -sig dense_nodes.sig -formula assign4.mfotl -log dense_nodes.log
  @1 (time point 0): (1,10) (2,20)
  @2 (time point 1): (2,20) (3,30)
  @3 (time point 2): (1,11) (3,30)
  @5 (time point 3): (4,40)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula assign4.mfotl -log dense_nodes.log
  @1 (time point 0): (1,10) (2,20)
  @2 (time point 1): (2,20) (3,30)
  @3 (time point 2): (1,11) (3,30)
  @5 (time point 3): (4,40)
  $ monpoly -verified -sig dense_nodes.sig -formula tp1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0) (2,0)
  @2 (time point 1): (2,1) (3,1)
  @3 (time point 2): (3,2)
  @5 (time point 3): (1,3) (4,3)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula tp1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0) (2,0)
  @2 (time point 1): (2,1) (3,1)
  @3 (time point 2): (3,2)
  @5 (time point 3): (1,3) (4,3)
  $ monpoly -verified -sig dense_nodes.sig -formula ts1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,1) (2,1)
  @2 (time point 1): (2,2) (3,2)
  @3 (time point 2): (3,3)
  @5 (time point 3): (1,5) (4,5)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula ts1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,1) (2,1)
  @2 (time point 1): (2,2) (3,2)
  @3 (time point 2): (3,3)
  @5 (time point 3): (1,5) (4,5)
  $ monpoly -verified -sig dense_nodes.sig -formula tpts1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0,1) (2,0,1)
  @2 (time point 1): (2,1,2) (3,1,2)
  @3 (time point 2): (3,2,3)
  @5 (time point 3): (1,3,5) (4,3,5)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula tpts1.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0,1) (2,0,1)
  @2 (time point 1): (2,1,2) (3,1,2)
  @3 (time point 2): (3,2,3)
  @5 (time point 3): (1,3,5) (4,3,5)
  $ monpoly -verified -sig dense_nodes.sig -formula tp2.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0) (2,0)
  @2 (time point 1): (1,0) (2,0) (2,1) (3,1)
  @3 (time point 2): (1,0) (2,0) (2,1) (3,1) (3,2)
  @5 (time point 3): (1,3) (3,2) (4,3)
  $ monpoly -verified -dense -sig dense_nodes.sig -formula tp2.mfotl -log dense_nodes.log
  @1 (time point 0): (1,0) (2,0)
  @2 (time point 1): (1,0) (2,0) (2,1) (3,1)
  @3 (time point 2): (1,0) (2,0) (2,1) (3,1) (3,2)
  @5 (time point 3): (1,3) (3,2) (4,3)
  $ monpoly -verified -sig dense_nodes.sig -formula tp3.mfotl -log dense_nodes.log
  @3 (time point 2): true
  $ monpoly -verified -dense -sig dense_nodes.sig -formula tp3.mfotl -log dense_nodes.log
  @3 (time point 2): true
