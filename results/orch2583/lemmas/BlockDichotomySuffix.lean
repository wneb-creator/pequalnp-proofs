namespace PEqualNP.Outside.L_meta_2583_aux.BlockGeometry

def blockEdges {N : ℕ} (A Bp C Bl D : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  ((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl))

lemma blockEdges_eq_star {N : ℕ} (A Bp C Bl D : Finset (Fin N)) (hac : A ⊆ C) :
    blockEdges A Bp C Bl D = C ×ˢ D := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨hp,hl⟩ := Finset.mem_product.mp h
      apply Finset.mem_product.mpr ⟨?_,hl⟩
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hp
      · exact hac (Finset.mem_inter.mp hp).1
    · obtain ⟨hp,hl⟩ := Finset.mem_product.mp h
      exact Finset.mem_product.mpr ⟨hac hp,(Finset.mem_inter.mp hl).1⟩
  · intro he
    obtain ⟨hp,hl⟩ := Finset.mem_product.mp he
    exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_union_left _ hp,hl⟩)

lemma added_clause_dichotomy {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A Bp C Bl D : Finset (Fin N)) (hc : C.Nonempty)
    (inside : ∀ e ∈ blockEdges A Bp C Bl D, I e.1 e.2) :
    D.card ≤ 1 ∨
      (C.card = 1 ∧ (A ∩ Bp).card ≤ 1 ∧ (D ∩ Bl).card ≤ 1) ∨
      (C.card = 1 ∧ A ⊆ C) := by
  by_cases hd : D.card ≤ 1
  · exact Or.inl hd
  right
  have hs := rectangle_small_side I noC4 (C ∪ (A ∩ Bp)) D (by
    intro p hp l hl
    exact inside (p,l) (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp,hl⟩)))
  have hs' : (C ∪ (A ∩ Bp)).card ≤ 1 := by omega
  have hcp : 0 < C.card := Finset.card_pos.mpr hc
  have hcc : C.card ≤ (C ∪ (A ∩ Bp)).card := Finset.card_le_card Finset.subset_union_left
  have hc1 : C.card = 1 := by omega
  have hab : (A ∩ Bp).card ≤ 1 :=
    (Finset.card_le_card Finset.subset_union_right).trans hs'
  by_cases ht : (D ∩ Bl).card ≤ 1
  · exact Or.inl ⟨hc1,hab,ht⟩
  right
  refine ⟨hc1,?_⟩
  obtain ⟨l,hl,l',hl',hll⟩ := Finset.one_lt_card.mp (by omega : 1 < (D ∩ Bl).card)
  obtain ⟨c,hcC⟩ := hc
  intro a ha
  by_contra hac
  have hca : c ≠ a := fun h => hac (h ▸ hcC)
  have hc_l : I c l := inside (c,l) (Finset.mem_union_left _
    (Finset.mem_product.mpr ⟨Finset.mem_union_left _ hcC,(Finset.mem_inter.mp hl).1⟩))
  have hc_l' : I c l' := inside (c,l') (Finset.mem_union_left _
    (Finset.mem_product.mpr ⟨Finset.mem_union_left _ hcC,(Finset.mem_inter.mp hl').1⟩))
  have ha_l : I a l := inside (a,l) (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ha,hl⟩))
  have ha_l' : I a l' := inside (a,l') (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ha,hl'⟩))
  exact noC4 c a l l' hca hll ⟨hc_l,hc_l',ha_l,ha_l'⟩

end PEqualNP.Outside.L_meta_2583_aux.BlockGeometry
