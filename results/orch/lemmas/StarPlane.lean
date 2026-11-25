import Mathlib

namespace PEqualNP.Outside.L_gct_231_star

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def star (x : Fin 2 → ℂ) : Fin 4 × Fin 4 → ℂ := fun p =>
  (![![0, x 0, x 1, -x 0 - x 1], ![x 0, 0, 0, 0],
    ![x 1, 0, 0, 0], ![-x 0 - x 1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

def starMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun := star
  map_add' := by
    intro x y
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [star] <;> ring
  map_smul' := by
    intro a x
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [star] <;> ring

lemma starMap_injective : Function.Injective starMap := by
  intro x y h
  have h₀ := congrFun h (0, 1)
  have h₁ := congrFun h (0, 2)
  funext i
  fin_cases i
  · simpa [starMap, star] using h₀
  · simpa [starMap, star] using h₁

lemma star_symmetric (x : Fin 2 → ℂ) (i j : Fin 4) :
    star x (i, j) = star x (j, i) := by
  fin_cases i <;> fin_cases j <;> simp [star]

lemma star_permanent (x : Fin 2 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + star x (i, j)) = 24 := by
  rw [perm4]
  simp [Matrix.of_apply, star]
  ring

lemma two_dimensional_level_space :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 2 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨starMap.range, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj starMap_injective]
    simp
  · rintro t ⟨x, rfl⟩ i j
    exact star_symmetric x i j
  · rintro t ⟨x, rfl⟩
    exact star_permanent x

end PEqualNP.Outside.L_gct_231_star
