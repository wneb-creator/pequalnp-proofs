import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Semantic

lemma triple_pair_core_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P Wp : Finset α) (L Wl : Finset β)
    (noRectangle : ∀ p ∈ P, ∀ p' ∈ P, ∀ l ∈ L, ∀ l' ∈ L,
      p ≠ p' → l ≠ l' →
      ¬ ((p ∈ Wp ∨ l ∈ Wl) ∧ (p ∈ Wp ∨ l' ∈ Wl) ∧
         (p' ∈ Wp ∨ l ∈ Wl) ∧ (p' ∈ Wp ∨ l' ∈ Wl))) :
    ∃ U : Finset α, ∃ V : Finset β,
      (∀ e ∈ ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl)), e.1 ∈ U ∨ e.2 ∈ V) ∧
      (((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))).card + U.card + V.card ≤
        P.card + L.card + Wp.card + Wl.card := by
  let E := ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))
  have subset : E ⊆ P ×ˢ L := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp (Finset.mem_product.mp h).1).1,
        (Finset.mem_product.mp h).2⟩
    · exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp h).1,
        (Finset.mem_inter.mp (Finset.mem_product.mp h).2).1⟩
  have card : E.card ≤ P.card * L.card := by
    simpa using Finset.card_le_card subset
  by_cases hp : P.card ≤ 1
  · refine ⟨P, ∅, ?_, ?_⟩
    · intro e he
      exact Or.inl (Finset.mem_product.mp (subset he)).1
    · have hm : P.card * L.card ≤ L.card := by
        simpa using Nat.mul_le_mul_right L.card hp
      change E.card + P.card + 0 ≤ _
      omega
  by_cases hl : L.card ≤ 1
  · refine ⟨∅, L, ?_, ?_⟩
    · intro e he
      exact Or.inr (Finset.mem_product.mp (subset he)).2
    · have hm : P.card * L.card ≤ P.card := by
        simpa using Nat.mul_le_mul_left P.card hl
      change E.card + 0 + L.card ≤ _
      omega
  have aSmall : (P ∩ Wp).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hpa p' hpa'
    by_contra hne
    obtain ⟨l, hlL, l', hlL', hll'⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
    exact noRectangle p (Finset.mem_inter.mp hpa).1 p' (Finset.mem_inter.mp hpa').1
      l hlL l' hlL' hne hll'
      ⟨Or.inl (Finset.mem_inter.mp hpa).2, Or.inl (Finset.mem_inter.mp hpa).2,
        Or.inl (Finset.mem_inter.mp hpa').2, Or.inl (Finset.mem_inter.mp hpa').2⟩
  have bSmall : (L ∩ Wl).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hlb l' hlb'
    by_contra hne
    obtain ⟨p, hpP, p', hpP', hpp'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    exact noRectangle p hpP p' hpP' l (Finset.mem_inter.mp hlb).1
      l' (Finset.mem_inter.mp hlb').1 hpp' hne
      ⟨Or.inr (Finset.mem_inter.mp hlb).2, Or.inr (Finset.mem_inter.mp hlb').2,
        Or.inr (Finset.mem_inter.mp hlb).2, Or.inr (Finset.mem_inter.mp hlb').2⟩
  refine ⟨P ∩ Wp, L ∩ Wl, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact Or.inl (Finset.mem_product.mp h).1
    · exact Or.inr (Finset.mem_product.mp h).2
  · have he : E.card ≤ (P ∩ Wp).card * L.card + P.card * (L ∩ Wl).card := by
      simpa [E] using Finset.card_union_le ((P ∩ Wp) ×ˢ L) (P ×ˢ (L ∩ Wl))
    have hm1 : (P ∩ Wp).card * L.card ≤ L.card := by
      simpa using Nat.mul_le_mul_right L.card aSmall
    have hm2 : P.card * (L ∩ Wl).card ≤ P.card := by
      simpa using Nat.mul_le_mul_left P.card bSmall
    have hwa : (P ∩ Wp).card ≤ Wp.card := Finset.card_le_card Finset.inter_subset_right
    have hwb : (L ∩ Wl).card ≤ Wl.card := Finset.card_le_card Finset.inter_subset_right
    change E.card + (P ∩ Wp).card + (L ∩ Wl).card ≤ _
    omega

end PEqualNP.Outside.L_meta_2583.Semantic
