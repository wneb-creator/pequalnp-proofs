import FastDirectCofactorPools
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
example : PEqualNP.Outside.L_meta_2373_aux.Cert18.FastDirectCofactorPools.checkNode 5229 = true := by
  decide +kernel
