namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def pairOrAndBase (i j : Fin 10) : Nat :=
  ([
  0,4,1,8,2,1,2,2,4,1,4,0,1,4,2,1,2,2,16,1,
  1,1,0,1,1,8,1,2,1,4,8,4,1,0,2,1,2,2,4,1,
  2,2,1,2,0,1,8,16,2,1,1,1,8,1,1,0,1,2,1,4,
  2,2,1,2,8,1,0,8,2,1,2,2,2,2,16,2,8,0,2,4,
  4,16,1,4,2,1,2,2,0,1,1,1,4,1,1,4,1,4,1,0] : List Nat).getD (10*i.val + j.val) 0

def pairOrAndRows (i j : Fin 10) : Row × Row :=
  (Fin.ofNat 1024 (pairOrAndBase i j +
    ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0),
   Fin.ofNat 1024 (pairOrAndBase i j +
    ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD j.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairOrAndChecked : ∀ (i j : Fin 10), i ≠ j →
    let rs := pairOrAndRows i j
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    bit rs.1 (bin 0 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 0 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ q : Fin 10, q ≠ i → q ≠ j →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma pair_or_and_keep_input (i j : Fin 10) (ij : i ≠ j)
    {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ pins ∨
      v = bin 1 (pins.getD i.val zero) (pins.getD j.val zero) ∨
      v = bin 0 (pins.getD i.val zero) (pins.getD j.val zero))
    (run : Live true target k S) : pins.getD i.val zero ∈ S ∨ pins.getD j.val zero ∈ S := by
  by_contra missing
  push_neg at missing
  obtain ⟨diff, leftSame, rightSame, othersSame⟩ := pairOrAndChecked i j ij
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with ordinary | rfl | rfl
  · obtain ⟨q, eq⟩ := (pin_mem v).mp ordinary
    have qi : q ≠ i := by
      rintro rfl
      exact missing.1 (eq.symm ▸ hv)
    have qj : q ≠ j := by
      rintro rfl
      exact missing.2 (eq.symm ▸ hv)
    exact changed (eq ▸ othersSame q qi qj)
  · exact changed leftSame
  · exact changed rightSame

end PEqualNP.Outside.L_meta_2592.Signed.Extended
