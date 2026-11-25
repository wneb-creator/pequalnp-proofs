theorem equality_m9_normal_coordinates {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (three : (residualUnits 14 D b).card = 3) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      (equality_coordinate_set (D := D) a 7 = {0} ∨
        equality_coordinate_set (D := D) a 7 = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact three)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have injective : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro member
      exact ⟨e ⟨u,member⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have proper := equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto 0
  change equality_coordinate_set (D := D) a 7 ≠ Finset.univ at proper
  have small := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨Finset.subset_univ (equality_coordinate_set (D := D) a 7),proper⟩)
  have card := equality_coordinate_card a injective onto 7
  have positive := equality_m9_positive h hD b hb pos hpos hI 0
  change 0 < (ru D b 7).card at positive
  simp only [Finset.card_univ,Fintype.card_fin] at small
  obtain ⟨a',inj',onto',first⟩ := equality_residual_coordinates three (by omega)
  exact ⟨a',inj',onto',first⟩
