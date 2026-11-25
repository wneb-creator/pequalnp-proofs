import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.BoundaryGeometry

lemma safe_or_one_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (I T : Finset (Fin n)) (w v : Fin n)
    (hI : ∀ x ∈ I, G.Adj x w) (hT : ∀ x ∈ T, G.Adj x v) :
    (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hwv : w = v
  · subst v
    exact Or.inl hT
  · right
    have hs : T ∩ I ⊆ Finset.univ.filter (fun x => G.Adj w x ∧ G.Adj v x) := by
      intro x hx
      obtain ⟨hxT, hxI⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (hI x hxI).symm, (hT x hxT).symm⟩
    exact (Finset.card_le_card hs).trans (h4 w v hwv)

lemma safe_boundary_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (I T : Finset (Fin n)) (w : Fin n)
    (hI : ∀ x ∈ I, G.Adj x w)
    (hT : (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1) :
    ∃ P : Finset (Fin n), P ⊆ T ∧ T ∩ I ⊆ P ∧
      (∀ x ∈ P, G.Adj x w) ∧ (P = T ∨ P.card ≤ 1) := by
  classical
  rcases hT with hT | hT
  · exact ⟨T, Finset.Subset.refl T, Finset.inter_subset_left,
      hT, Or.inl rfl⟩
  · refine ⟨T ∩ I, Finset.inter_subset_left, Finset.Subset.refl _, ?_, Or.inr hT⟩
    intro x hx
    exact hI x (Finset.mem_inter.mp hx).2

lemma clean_raw_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (I T V : Finset (Fin n)) (w : Fin n) (hV : V.Nonempty)
    (hI : ∀ x ∈ I, G.Adj x w)
    (hclean : ∀ x : Fin n → Bool,
      (∃ t ∈ T, x t = true) → (∃ v ∈ V, x v = true) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1 := by
  classical
  obtain ⟨v, hv⟩ := hV
  apply safe_or_one_overlap G h4 I T w v hI
  intro t ht
  let x : Fin n → Bool := fun a => decide (a = t ∨ a = v)
  have hx := hclean x ⟨t, ht, by simp [x]⟩ ⟨v, hv, by simp [x]⟩
  have he : ∃ a b, G.Adj a b ∧ (a = t ∨ a = v) ∧ (b = t ∨ b = v) := by
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, x] using hx
  obtain ⟨a, b, hab, ha, hb⟩ := he
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp at hab
  · exact hab
  · exact hab.symm
  · simp at hab

end PEqualNP.Outside.L_meta_5012.BoundaryGeometry
