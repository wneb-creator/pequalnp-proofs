import PackedDirect
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5

def block (start count : Nat) : Prop :=
  ∀ i : Fin count, checkNode (Fin.ofNat 5230 (start + i.val)) = true

lemma block_add (start left right : Nat) (hl : block start left)
    (hr : block (start + left) right) : block start (left + right) := by
  intro i
  by_cases hi : i.val < left
  · exact hl ⟨i.val, hi⟩
  · have hj : i.val - left < right := by omega
    have h := hr ⟨i.val - left, hj⟩
    change checkNode (Fin.ofNat 5230 (start + left + (i.val - left))) = true at h
    rw [show start + left + (i.val - left) = start + i.val by omega] at h
    exact h

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
