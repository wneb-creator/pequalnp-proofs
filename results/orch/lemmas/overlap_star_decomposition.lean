import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.OverlapStars

lemma guarded_pair_double_star {n : ℕ} (P Q W : Finset (Fin n)) (r t : Fin n)
    (hI : P ∩ Q = {r}) (hWP : W ∩ P = {t}) (hWQ : W ∩ Q = ∅)
    (u v : Fin n) :
    ((u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ W ∨ v ∈ W)) ↔
      (u = r ∧ v ∈ W) ∨ (v = r ∧ u ∈ W) ∨
      (u = t ∧ v ∈ Q) ∨ (v = t ∧ u ∈ Q) := by
  classical
  have hr : r ∈ P ∧ r ∈ Q := Finset.mem_inter.mp (by simp [hI])
  have ht : t ∈ W ∧ t ∈ P := Finset.mem_inter.mp (by simp [hWP])
  have hnot (a : Fin n) (ha : a ∈ W) : a ∉ Q := by
    intro haq
    have ha' : a ∈ W ∩ Q := Finset.mem_inter.mpr ⟨ha, haq⟩
    simpa [hWQ] using ha'
  have hforward (a b : Fin n) (hP : a ∈ P ∨ b ∈ P)
      (hQ : a ∈ Q ∨ b ∈ Q) (ha : a ∈ W) :
      (b = r ∧ a ∈ W) ∨ (a = t ∧ b ∈ Q) := by
    have hbQ : b ∈ Q := hQ.resolve_left (hnot a ha)
    rcases hP with haP | hbP
    · right
      have ha' : a ∈ W ∩ P := Finset.mem_inter.mpr ⟨ha, haP⟩
      exact ⟨by simpa [hWP] using ha', hbQ⟩
    · left
      have hb : b ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hbP, hbQ⟩
      exact ⟨by simpa [hI] using hb, ha⟩
  constructor
  · rintro ⟨hp, hq, hu | hv⟩
    · rcases hforward u v hp hq hu with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases hforward v u hp.symm hq.symm hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩ | ⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · exact ⟨Or.inl hr.1, Or.inl hr.2, Or.inr hv⟩
    · exact ⟨Or.inr hr.1, Or.inr hr.2, Or.inl hu⟩
    · exact ⟨Or.inl ht.2, Or.inr hv, Or.inl ht.1⟩
    · exact ⟨Or.inr ht.2, Or.inl hu, Or.inr ht.1⟩

end PEqualNP.Outside.L_meta_5012.OverlapStars
