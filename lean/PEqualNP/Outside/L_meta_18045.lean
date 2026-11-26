import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18045 : ∀ (x1 x2 : Finset (Finset ℕ)), (∀ x3 ∈ x1 \ x2, ∃ x5 ∈ x1, ∃ x6 ∈ x1, x5 ⊂ x3 ∧ x6 ⊂ x3 ∧ x3 = x5 ∪ x6) → ∀ x4 ∈ x1, {x6 ∈ x1 ∩ x2 | x6 ⊆ x4}.biUnion id = x4 := by
  intro A B h s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    apply Finset.Subset.antisymm
    · exact Finset.biUnion_subset.2 (fun v hv => (Finset.mem_filter.1 hv).2)
    · by_cases hB : s ∈ B
      · intro x hx
        exact Finset.mem_biUnion.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hs, hB⟩, Finset.Subset.refl _⟩, hx⟩
      · obtain ⟨t, ht, u, hu, hts, hus, heq⟩ := h s (Finset.mem_sdiff.2 ⟨hs, hB⟩)
        have key : ∀ w, w ⊂ s → w ∈ A → w ⊆ ({x6 ∈ A ∩ B | x6 ⊆ s}.biUnion id) := by
          intro w hws hw x hx
          rw [← ih w hws hw] at hx
          obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.1 hx
          exact Finset.mem_biUnion.2 ⟨v, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1, (Finset.mem_filter.1 hv).2.trans hws.subset⟩, hxv⟩
        intro x hx
        rw [heq] at hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact key t hts ht hx
        · exact key u hus hu hx
