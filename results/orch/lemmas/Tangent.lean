import Mathlib

namespace PEqualNP.Outside.L_gct_231_aux.Tangent

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


lemma sum_entries_zero (t : Fin 4 × Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + z * t (i, j)) = 24) :
    (∑ i : Fin 4, ∑ j : Fin 4, t (i, j)) = 0 := by
  have h₁ := h 1
  have hm1 := h (-1)
  have h₂ := h 2
  have hm2 := h (-2)
  simp only [perm4, Matrix.of_apply] at h₁ hm1 h₂ hm2
  simp only [Fin.sum_univ_four]
  linear_combination (1 / 9 : ℂ) * h₁ - (1 / 9 : ℂ) * hm1 -
    (1 / 72 : ℂ) * h₂ + (1 / 72 : ℂ) * hm2

lemma quadratic_general (t : Fin 4 × Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + z * t (i, j)) = 24) :
    (∑ i : Fin 4, ∑ j : Fin 4, t (i, j)) ^ 2 -
      (∑ i : Fin 4, (∑ j : Fin 4, t (i, j)) ^ 2) -
      (∑ j : Fin 4, (∑ i : Fin 4, t (i, j)) ^ 2) +
      (∑ i : Fin 4, ∑ j : Fin 4, t (i, j) ^ 2) = 0 := by
  have h₁ := h 1
  have hm1 := h (-1)
  have h₂ := h 2
  have hm2 := h (-2)
  simp only [perm4, Matrix.of_apply] at h₁ hm1 h₂ hm2
  simp only [Fin.sum_univ_four]
  linear_combination (2 / 3 : ℂ) * h₁ + (2 / 3 : ℂ) * hm1 -
    (1 / 24 : ℂ) * h₂ - (1 / 24 : ℂ) * hm2

lemma quadratic_symmetric (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, t (i, j) = t (j, i))
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + z * t (i, j)) = 24) :
    (∑ i : Fin 4, ∑ j : Fin 4, t (i, j) ^ 2) -
      2 * (∑ i : Fin 4, (∑ j : Fin 4, t (i, j)) ^ 2) = 0 := by
  have hc (j : Fin 4) : (∑ i : Fin 4, t (i, j)) = ∑ i : Fin 4, t (j, i) :=
    Finset.sum_congr rfl (fun i _ => hs i j)
  have hq := quadratic_general t h
  rw [sum_entries_zero t h] at hq
  simp_rw [hc] at hq
  linear_combination hq

end PEqualNP.Outside.L_gct_231_aux.Tangent
