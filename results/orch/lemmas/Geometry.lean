import Mathlib

namespace PEqualNP.Outside.Geometry

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma four_points : ∀ s : Finset (Fin 13), s.card = 4 →
    (Finset.univ.filter fun l : Fin 13 =>
      ∀ p ∈ s, p + l ∉ ({0, 1, 3, 9} : Finset (Fin 13))).card ≤ 3 := by
  decide +kernel

lemma rectangles
    (small : ∀ s : Finset (Fin 13), s.card = 4 →
      (Finset.univ.filter fun l : Fin 13 =>
        ∀ p ∈ s, p + l ∉ ({0, 1, 3, 9} : Finset (Fin 13))).card ≤ 3) :
    ∀ s t : Finset (Fin 13),
      (∀ p ∈ s, ∀ l ∈ t, p + l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) →
      s.card ≤ 3 ∨ t.card ≤ 3 := by
  intro s t independent
  by_cases hs : s.card ≤ 3
  · exact Or.inl hs
  · obtain ⟨u, hus, hu⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    apply Or.inr
    apply le_trans (Finset.card_le_card (s := t) (t :=
      Finset.univ.filter fun l : Fin 13 =>
        ∀ p ∈ u, p + l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) ?_) (small u hu)
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => independent p (hus hp) l hl⟩

end PEqualNP.Outside.Geometry
