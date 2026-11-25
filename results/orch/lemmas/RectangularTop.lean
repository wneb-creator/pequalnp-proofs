import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.RectangularTop

open PEqualNP.TopForm

lemma intersection_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (z a : Fin n) (haz : a ≠ z) (J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (ha : ∀ b ∈ J ∩ B, G.Adj a b) :
    (J ∩ B).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (hG a z haz)
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha b hb,
    hz b (Finset.mem_inter.mp hb).2⟩

lemma rectangle_star_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (z : Fin n) (I J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (hrect : ∀ a ∈ I, ∀ b ∈ J ∩ B, G.Adj a b) :
    I ⊆ {z} ∨ ∃ b : Fin n, J ∩ B ⊆ {b} := by
  classical
  by_cases hI : I ⊆ {z}
  · exact Or.inl hI
  · right
    obtain ⟨a, ha, haz⟩ := Finset.not_subset.mp hI
    have hcard := intersection_card_le_one G hG z a
      (by simpa only [Finset.mem_singleton] using haz) J B hz (hrect a ha)
    by_cases hne : (J ∩ B).Nonempty
    · obtain ⟨b, hb⟩ := hne
      refine ⟨b, ?_⟩
      intro c hc
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard) c hc b hb)
    · exact ⟨z, by simpa only [Finset.not_nonempty_iff_eq_empty.mp hne]
        using (Finset.empty_subset ({z} : Finset (Fin n)))⟩

end PEqualNP.Outside.L_meta_9811.RectangularTop
