import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1462 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  classical
  intro n m S X B r f hr hf
  have hrow : ∀ (i j : Fin m) (p : Fin n), p ∉ S j →
      ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty →
      p ∉ X ∧ f i ∈ S j := by
    intro i j p hp hne
    obtain ⟨z, hz⟩ := hne
    rw [Finset.mem_inter] at hz
    obtain ⟨hz1, hz2⟩ := hz
    by_cases hpX : p ∈ X
    · rw [if_pos hpX, Finset.mem_singleton] at hz1
      subst hz1; exact absurd hz2 hp
    · rw [if_neg hpX, Finset.mem_insert, Finset.mem_singleton] at hz1
      rcases hz1 with rfl | rfl
      · exact absurd hz2 hp
      · exact ⟨hpX, hz2⟩
  constructor
  · intro i p hp
    by_cases hpX : p ∈ X
    · rw [if_pos hpX]
      ext z; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, hp⟩
    · rw [if_neg hpX]
      have hnot : ¬ S i ⊆ X := fun h => hpX (h hp)
      have hfi := (hf i hnot).2.1
      ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, hz⟩
        · exact h
        · subst h; exact absurd hz hfi
      · rintro rfl; exact ⟨Or.inl rfl, hp⟩
  · rintro i j hij ⟨⟨p, hp, hpn⟩, ⟨s, hs, hsn⟩⟩
    rw [Finset.mem_sdiff] at hp hs
    obtain ⟨hpX, hfij⟩ := hrow i j p hp.2 hpn
    obtain ⟨hsX, hfji⟩ := hrow j i s hs.2 hsn
    have hi := hf i (fun h => hpX (h hp.1))
    have hj := hf j (fun h => hsX (h hs.1))
    have r1 := hi.2.2 (f j) (Finset.mem_inter.2 ⟨hfji, hj.1⟩)
    have r2 := hj.2.2 (f i) (Finset.mem_inter.2 ⟨hfij, hi.1⟩)
    exact hr _ _ r1 r2
