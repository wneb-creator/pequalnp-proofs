namespace PEqualNP.Outside.L_meta_2592_aux.ReadBudget

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

def readers (D : U2Circuit) (v : Fin 10) : Finset (Fin D.gates.length) :=
  Finset.univ.filter fun j => D.gates[j.val].a = v.val ∨ D.gates[j.val].b = v.val

lemma reader_bound (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (v : Fin 10) : (readers D v).card + 15 ≤ D.gates.length := by
  obtain ⟨hwf, hev, hlen, hEv, _⟩ := restrictU2_spec D hmin.1 v false
  have hc : HasU2Size (fun x => pet (Function.update x v false))
      (restrictU2 D v false).gates.length :=
    ⟨restrictU2 D v false, hwf, le_rfl, fun x => (hev x).trans (hmin.2.1 _)⟩
  have hf := floor v _ hc
  have hs : readers D v ⊆ elimSet D v false := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with ha | hb
    · left
      rw [ha, hEv]
      rfl
    · right
      rw [hb, hEv]
      rfl
  have hcard := Finset.card_le_card hs
  omega

lemma at_most_two_readers (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (v : Fin 10) : (readers D v).card ≤ 2 := by
  have h := reader_bound floor D hmin v
  omega

lemma at_most_three_readers (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 18) (v : Fin 10) : (readers D v).card ≤ 3 := by
  have h := reader_bound floor D hmin v
  omega

lemma repeated_positive_impossible (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 18)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = false) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = false)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_4_same hmin h0 v false hr0 j hj hpos hr1
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma positive_first_later_negative (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 18)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    (D.gates[j].a = v.val → D.gates[j].pa = true) ∧
    (D.gates[j].b = v.val → D.gates[j].pb = true) := by
  constructor
  · intro ha
    cases hp : D.gates[j].pa
    · exact False.elim (repeated_positive_impossible floor D hmin small h0 v hr0 j hj hpos
        (Or.inl ⟨ha, hp⟩))
    · rfl
  · intro hb
    cases hp : D.gates[j].pb
    · exact False.elim (repeated_positive_impossible floor D hmin small h0 v hr0 j hj hpos
        (Or.inr ⟨hb, hp⟩))
    · rfl

end PEqualNP.Outside.L_meta_2592_aux.ReadBudget
