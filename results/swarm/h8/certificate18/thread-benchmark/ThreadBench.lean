import PackedDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.ThreadProbe

set_option maxRecDepth 32768
set_option maxHeartbeats 0

lemma checked4992 : (List.range 4).all (fun j =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 (4992+j))) = true := by
  decide +kernel

lemma checked4996 : (List.range 4).all (fun j =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 (4996+j))) = true := by
  decide +kernel

lemma checked5000 : (List.range 4).all (fun j =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 (5000+j))) = true := by
  decide +kernel

lemma checked5004 : (List.range 4).all (fun j =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 (5004+j))) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2373_aux.Cert18.ThreadProbe
