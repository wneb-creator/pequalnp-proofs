import H2ChunkDefs
namespace H2PackedReplay
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
lemma check_interval (start count : Nat) (h : blockCheck start count = true)
    (i : Fin 5230) (hlo : start ≤ i.val) (hhi : i.val < start + count) :
    checkNode i = true := by
  have hj : i.val - start < count := by omega
  have h' := blockCheck_at start count h (i.val - start) hj
  have heq : start + (i.val - start) = i.val := by omega
  rw [heq] at h'
  have hi : Fin.ofNat 5230 i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  simpa only [hi] using h'
end H2PackedReplay
#print axioms H2PackedReplay.check_interval
