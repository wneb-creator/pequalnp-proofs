import PackedDirect

namespace H2PackedReplay
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed

def blockCheck (start count : Nat) : Bool :=
  (List.range count).all fun j => checkNode (Fin.ofNat 5230 (start + j))

lemma blockCheck_at (start count : Nat) (h : blockCheck start count = true)
    (j : Nat) (hj : j < count) :
    checkNode (Fin.ofNat 5230 (start + j)) = true :=
  List.all_eq_true.mp h j (List.mem_range.mpr hj)

end H2PackedReplay
