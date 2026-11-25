import Mathlib

namespace PEqualNP.Outside.L_meta_4675

lemma common_neighbours_small {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (haa' : a ≠ a') (B : Finset (Fin l)) :
    (B.filter fun b => (a, b) ∈ E ∧ (a', b) ∈ E).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  simp only [Finset.mem_filter] at hb hb'
  by_contra hbb'
  exact h4 a a' b b' haa' hbb' ⟨hb.2.1, hb'.2.1, hb.2.2, hb'.2.2⟩

lemma two_rectangle_partners_small {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (ha : 2 ≤ A.card)
    {z z' : Fin p} (hzz' : z ≠ z')
    (hz : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z, b) ∈ E)
    (hz' : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z', b) ∈ E) :
    B.card ≤ 2 := by
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  let U := B.filter fun b => (z, b) ∈ E ∧ (z', b) ∈ E
  let V := B.filter fun b => (a, b) ∈ E ∧ (a', b) ∈ E
  have hu : U.card ≤ 1 := common_neighbours_small E h4 hzz' B
  have hv : V.card ≤ 1 := common_neighbours_small E h4 haa' B
  have hsub : B ⊆ U ∪ V := by
    intro b hb
    by_cases hzb : (z, b) ∈ E
    · by_cases hz'b : (z', b) ∈ E
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, hzb, hz'b⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hb, (hz' a ha b hb).resolve_right hz'b, (hz' a' ha' b hb).resolve_right hz'b⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hb, (hz a ha b hb).resolve_right hzb, (hz a' ha' b hb).resolve_right hzb⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  omega

lemma large_rectangle_partner_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (ha : 2 ≤ A.card) (hb : 3 ≤ B.card)
    {z z' : Fin p}
    (hz : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z, b) ∈ E)
    (hz' : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z', b) ∈ E) :
    z = z' := by
  by_contra hzz'
  have := two_rectangle_partners_small E h4 A B ha hzz' hz hz'
  omega

end PEqualNP.Outside.L_meta_4675
