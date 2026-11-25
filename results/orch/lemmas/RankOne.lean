import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_gct_231_aux.RankOne

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


lemma vector_zero (u : Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + z * u i * u j) = 24) : u = 0 := by
  let e1 := u 0 + u 1 + u 2 + u 3
  let e2 := u 0 * u 1 + u 0 * u 2 + u 0 * u 3 +
    u 1 * u 2 + u 1 * u 3 + u 2 * u 3
  let e3 := u 0 * u 1 * u 2 + u 0 * u 1 * u 3 +
    u 0 * u 2 * u 3 + u 1 * u 2 * u 3
  let e4 := u 0 * u 1 * u 2 * u 3
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [perm4, Matrix.of_apply] at h1 hm1 h2 hm2
  have he1sq : e1 ^ 2 = 0 := by
    dsimp [e1]
    linear_combination (1 / 9 : ℂ) * h1 - (1 / 9 : ℂ) * hm1 -
      (1 / 72 : ℂ) * h2 + (1 / 72 : ℂ) * hm2
  have he2sq : e2 ^ 2 = 0 := by
    dsimp [e2]
    linear_combination (1 / 6 : ℂ) * h1 + (1 / 6 : ℂ) * hm1 -
      (1 / 96 : ℂ) * h2 - (1 / 96 : ℂ) * hm2
  have he3sq : e3 ^ 2 = 0 := by
    dsimp [e3]
    linear_combination -(1 / 36 : ℂ) * h1 + (1 / 36 : ℂ) * hm1 +
      (1 / 72 : ℂ) * h2 - (1 / 72 : ℂ) * hm2
  have he4sq : e4 ^ 2 = 0 := by
    dsimp [e4]
    linear_combination -(1 / 144 : ℂ) * h1 - (1 / 144 : ℂ) * hm1 +
      (1 / 576 : ℂ) * h2 + (1 / 576 : ℂ) * hm2
  have he1 : e1 = 0 := eq_zero_of_pow_eq_zero he1sq
  have he2 : e2 = 0 := eq_zero_of_pow_eq_zero he2sq
  have he3 : e3 = 0 := eq_zero_of_pow_eq_zero he3sq
  have he4 : e4 = 0 := eq_zero_of_pow_eq_zero he4sq
  dsimp [e1, e2, e3, e4] at he1 he2 he3 he4
  funext i
  change u i = 0
  apply eq_zero_of_pow_eq_zero (n := 4)
  fin_cases i
  · change u 0 ^ 4 = 0
    linear_combination (u 0 ^ 3) * he1 - (u 0 ^ 2) * he2 + (u 0) * he3 - he4
  · change u 1 ^ 4 = 0
    linear_combination (u 1 ^ 3) * he1 - (u 1 ^ 2) * he2 + (u 1) * he3 - he4
  · change u 2 ^ 4 = 0
    linear_combination (u 2 ^ 3) * he1 - (u 2 ^ 2) * he2 + (u 2) * he3 - he4
  · change u 3 ^ 4 = 0
    linear_combination (u 3 ^ 3) * he1 - (u 3 ^ 2) * he2 + (u 3) * he3 - he4

end PEqualNP.Outside.L_gct_231_aux.RankOne
