import PackedDirect
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : checkNode 292 = true := by decide +kernel
