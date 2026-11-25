namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def tripleRows (i j c d : Fin 10) : Row × Row :=
  let weights := ([512,128,32,256,64,16,4,1,8,2] : List Nat)
  let base := weights.getD j.val 0 + weights.getD c.val 0 + weights.getD d.val 0
  (Fin.ofNat 1024 base, Fin.ofNat 1024 (base + weights.getD i.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tripleChecked : ∀ (i j c d : Fin 10), ([i,j,c,d] : List (Fin 10)).Nodup →
    petAdjacent j c = false → petAdjacent j d = false → petAdjacent c d = false →
    (petAdjacent i j = true ∨ petAdjacent i c = true ∨ petAdjacent i d = true) →
    let rs := tripleRows i j c d
    bit rs.1 target ≠ bit rs.2 target ∧
    (∀ v ∈ [j,c,d],
      bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD v.val zero)) =
        bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD v.val zero))) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma triple_ors_keep_input (i j c d : Fin 10) (nd : ([i,j,c,d] : List (Fin 10)).Nodup)
    (jc : petAdjacent j c = false) (jd : petAdjacent j d = false) (cd : petAdjacent c d = false)
    (neighbor : petAdjacent i j = true ∨ petAdjacent i c = true ∨ petAdjacent i d = true)
    {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ pins ∨ ∃ w ∈ [j,c,d],
      v = bin 1 (pins.getD i.val zero) (pins.getD w.val zero))
    (run : Live true target k S) : pins.getD i.val zero ∈ S := by
  by_contra missing
  obtain ⟨diff, gatesSame, othersSame⟩ := tripleChecked i j c d nd jc jd cd neighbor
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with ordinary | ⟨w, hw, rfl⟩
  · obtain ⟨q, eq⟩ := (pin_mem v).mp ordinary
    have qi : q ≠ i := by
      rintro rfl
      exact missing (eq.symm ▸ hv)
    exact changed (eq ▸ othersSame q qi)
  · exact changed (gatesSame w hw)

end PEqualNP.Outside.L_meta_2592.Signed.Extended
