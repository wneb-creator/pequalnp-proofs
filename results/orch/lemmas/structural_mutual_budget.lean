import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.MutualKill

open PEqualNP.TopForm

lemma rectangle_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n))
    (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ K : Finset (Fin n), K ⊆ A ∪ B ∧
      (∀ a ∈ A, ∀ b ∈ B, a ∈ K ∨ b ∈ K) ∧
      A.card * B.card + K.card ≤ A.card + B.card := by
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · have side_small : A.card ≤ 1 ∨ B.card ≤ 1 := by
        by_cases hA : A.card ≤ 1
        · exact Or.inl hA
        · right
          obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
          have hsub : B ⊆ Finset.univ.filter (fun b => G.Adj a b ∧ G.Adj a' b) := by
            intro b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hab a ha b hb, hab a' ha' b hb⟩
          exact (Finset.card_le_card hsub).trans (h4 a a' haa')
      rcases side_small with hA | hB
      · have hc : A.card = 1 := by have := ha.card_pos; omega
        refine ⟨A, Finset.subset_union_left, ?_, ?_⟩
        · intro a ha b hb; exact Or.inl ha
        · rw [hc]; omega
      · have hc : B.card = 1 := by have := hb.card_pos; omega
        refine ⟨B, Finset.subset_union_right, ?_, ?_⟩
        · intro a ha b hb; exact Or.inr hb
        · rw [hc]; omega
    · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      subst B
      refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp
      · simp
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    subst A
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simp
    · simp

lemma two_rectangles_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n)) (hCD : Disjoint C D)
    (hfirst : ∀ a ∈ A ∩ C, ∀ b ∈ B ∩ D, G.Adj a b)
    (hsecond : ∀ a ∈ A ∩ D, ∀ b ∈ B ∩ C, G.Adj a b) :
    ∃ K : Finset (Fin n), K ⊆ A ∪ B ∧
      (∀ e ∈ ((A ∩ C) ×ˢ (B ∩ D)) ∪ ((A ∩ D) ×ˢ (B ∩ C)), e.1 ∈ K ∨ e.2 ∈ K) ∧
      (((A ∩ C) ×ˢ (B ∩ D)) ∪ ((A ∩ D) ×ˢ (B ∩ C))).card + K.card ≤ A.card + B.card := by
  obtain ⟨K1, hK1, hc1, hb1⟩ := rectangle_cover_budget G h4 (A ∩ C) (B ∩ D) hfirst
  obtain ⟨K2, hK2, hc2, hb2⟩ := rectangle_cover_budget G h4 (A ∩ D) (B ∩ C) hsecond
  refine ⟨K1 ∪ K2, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp (hK1 hx) with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
      · exact Finset.mem_union_right _ (Finset.mem_inter.mp hx).1
    · rcases Finset.mem_union.mp (hK2 hx) with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
      · exact Finset.mem_union_right _ (Finset.mem_inter.mp hx).1
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨ha, hb⟩ := Finset.mem_product.mp he
      exact (hc1 e.1 ha e.2 hb).imp (Finset.mem_union_left K2) (Finset.mem_union_left K2)
    · obtain ⟨ha, hb⟩ := Finset.mem_product.mp he
      exact (hc2 e.1 ha e.2 hb).imp (Finset.mem_union_right K1) (Finset.mem_union_right K1)
  · have hAd : Disjoint (A ∩ C) (A ∩ D) := hCD.mono Finset.inter_subset_right Finset.inter_subset_right
    have hBd : Disjoint (B ∩ D) (B ∩ C) := hCD.symm.mono Finset.inter_subset_right Finset.inter_subset_right
    have hAs : (A ∩ C) ∪ (A ∩ D) ⊆ A := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hBs : (B ∩ D) ∪ (B ∩ C) ⊆ B := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hAc := Finset.card_le_card hAs
    have hBc := Finset.card_le_card hBs
    rw [Finset.card_union_of_disjoint hAd] at hAc
    rw [Finset.card_union_of_disjoint hBd] at hBc
    have hEc := Finset.card_union_le ((A ∩ C) ×ˢ (B ∩ D)) ((A ∩ D) ×ˢ (B ∩ C))
    simp only [Finset.card_product] at hEc
    have hKc := Finset.card_union_le K1 K2
    omega

end PEqualNP.Outside.L_meta_5012.MutualKill
