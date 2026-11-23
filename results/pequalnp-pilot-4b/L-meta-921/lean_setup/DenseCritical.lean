import PEqualNP.Defs

namespace DenseCriticalAudit

theorem dense_determined_by_layer {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (F : Finset α → Prop) (hmono : Monotone F)
    (hmax : ¬ F (Finset.univ \ S))
    (hlayer : ∀ A : Finset α, A.card = 8 → (F A ↔ (A ∩ S).Nonempty)) :
    ∀ A : Finset α, 8 ≤ A.card → (F A ↔ (A ∩ S).Nonempty) := by
  intro A hA
  constructor
  · intro hFA
    by_contra hn
    have hs : A ⊆ Finset.univ \ S := by
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro haS
      exact hn ⟨a, Finset.mem_inter.mpr ⟨ha, haS⟩⟩
    exact hmax (hmono hs hFA)
  · rintro ⟨p, hp⟩
    obtain ⟨hpA, hpS⟩ := Finset.mem_inter.mp hp
    have hseven : 7 ≤ (A.erase p).card := by
      rw [Finset.card_erase_of_mem hpA]
      omega
    obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq hseven
    have hpB : p ∉ B := by
      intro hpB
      exact (Finset.mem_erase.mp (hBA hpB)).1 rfl
    have hs : insert p B ⊆ A := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haB
      · exact hpA
      · exact (Finset.mem_erase.mp (hBA haB)).2
    have hcard : (insert p B).card = 8 := by simp [hpB, hB]
    apply hmono hs
    apply (hlayer _ hcard).mpr
    exact ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hpS⟩⟩

end DenseCriticalAudit
