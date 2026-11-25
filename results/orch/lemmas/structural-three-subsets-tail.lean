namespace PEqualNP.Outside.L_meta_6659_aux

theorem three_subsets_full {α : Type*} [DecidableEq α]
    (S A B C : Finset α) (hS : S.card ≤ 2)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hCS : C ⊆ S)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hAB : A = B → A.card ≤ 1 → False)
    (hAC : A = C → A.card ≤ 1 → False)
    (hBC : B = C → B.card ≤ 1 → False) :
    (A.card = 2 ∧ A = S) ∨ (B.card = 2 ∧ B = S) ∨ (C.card = 2 ∧ C = S) := by
  have ca := Finset.card_le_card hAS
  have cb := Finset.card_le_card hBS
  have cc := Finset.card_le_card hCS
  by_cases ha2 : A.card = 2
  · exact Or.inl ⟨ha2,Finset.eq_of_subset_of_card_le hAS (by omega)⟩
  by_cases hb2 : B.card = 2
  · exact Or.inr (Or.inl ⟨hb2,Finset.eq_of_subset_of_card_le hBS (by omega)⟩)
  by_cases hc2 : C.card = 2
  · exact Or.inr (Or.inr ⟨hc2,Finset.eq_of_subset_of_card_le hCS (by omega)⟩)
  have pa := Finset.card_pos.mpr hA
  have pb := Finset.card_pos.mpr hB
  have pc := Finset.card_pos.mpr hC
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (by omega : A.card = 1)
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (by omega : B.card = 1)
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (by omega : C.card = 1)
  have aS : a ∈ S := hAS (by rw [ha]; exact Finset.mem_singleton_self a)
  have bS : b ∈ S := hBS (by rw [hb]; exact Finset.mem_singleton_self b)
  have cS : c ∈ S := hCS (by rw [hc]; exact Finset.mem_singleton_self c)
  have ab : a ≠ b := by
    intro equal
    exact hAB (by rw [ha,hb,equal]) (by omega)
  have ac : a ≠ c := by
    intro equal
    exact hAC (by rw [ha,hc,equal]) (by omega)
  have bc : b ≠ c := by
    intro equal
    exact hBC (by rw [hb,hc,equal]) (by omega)
  have large := Finset.two_lt_card.mpr ⟨a,aS,b,bS,c,cS,ab,ac,bc⟩
  omega

end PEqualNP.Outside.L_meta_6659_aux
