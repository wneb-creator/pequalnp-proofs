import PackedDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed

def slice (lo count : Nat) : Bool :=
  (List.range count).all (fun j => checkNode (Fin.ofNat 5230 (lo+j)))

lemma blocks_sound (lo len width chunks : Nat) (positive : 0 < width)
    (covered : len ≤ chunks*width)
    (checked : ∀ q : Fin chunks,
      slice (lo+width*q.val) (min width (len-width*q.val)) = true) :
    ∀ i : Fin 5230, lo ≤ i.val → i.val < lo+len → checkNode i = true := by
  intro i lower upper
  let q := (i.val-lo)/width
  let r := (i.val-lo)%width
  have remainder : r < width := Nat.mod_lt _ positive
  have identity : r + width*q = i.val-lo := Nat.mod_add_div _ _
  have qlt : q < chunks := (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  have rlt : r < min width (len-width*q) := by omega
  have h := List.all_eq_true.mp (checked ⟨q,qlt⟩) r (List.mem_range.mpr rlt)
  have eq : Fin.ofNat 5230 (lo+width*q+r) = i := by
    apply Fin.ext
    change (lo+width*q+r)%5230 = i.val
    omega
  exact eq ▸ h

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
