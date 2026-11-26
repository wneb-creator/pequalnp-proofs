import PackedDirect
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks
open Replay.DirectMode.Packed
lemma range_all_sound {start count : Nat}
    (checked : (List.range count).all (fun d =>
      checkNode (Fin.ofNat 5230 (start+d))) = true)
    (i : Fin 5230) (lo : start ≤ i.val) (hi : i.val < start+count) :
    checkNode i = true := by
  have delta : i.val-start < count := by omega
  have raw := List.all_eq_true.mp checked (i.val-start) (List.mem_range.mpr delta)
  have same : Fin.ofNat 5230 (start+(i.val-start)) = i := by
    apply Fin.ext
    change (start+(i.val-start)) % 5230 = i.val
    rw [Nat.add_sub_of_le lo, Nat.mod_eq_of_lt i.isLt]
  rw [same] at raw
  exact raw
#print axioms range_all_sound
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks
