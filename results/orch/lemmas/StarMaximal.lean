import Mathlib

namespace PEqualNP.Outside.L_gct_231_aux.StarMaximal

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


def star (x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, x, y, -x - y], ![x, 0, 0, 0],
    ![y, 0, 0, 0], ![-x - y, 0, 0, 0]]

def symMatrix (a b c d e f g h i j : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a, b, c, d], ![b, e, f, g], ![c, f, h, i], ![d, g, i, j]]

lemma first_order (a b c d e f g h i j : ℂ)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * symMatrix a b c d e f g h i j r s) = 24) (x y : ℂ) :
    6 * a + 12 * b + 12 * c + 12 * d + e * x ^ 2 - 4 * e * x + 6 * e + 2 * f * x * y - 4 * f * x - 4 * f * y + 12 * f - 2 * g * x ^ 2 - 2 * g * x * y + 4 * g * y + 12 * g + h * y ^ 2 - 4 * h * y + 6 * h - 2 * i * x * y + 4 * i * x - 2 * i * y ^ 2 + 12 * i + j * x ^ 2 + 2 * j * x * y + 4 * j * x + j * y ^ 2 + 4 * j * y + 6 * j = 0 := by
  have h1 := hp x y 1
  have hm1 := hp x y (-1)
  have h2 := hp x y 2
  have hm2 := hp x y (-2)
  simp [perm4, Matrix.of_apply, star, symMatrix] at h1 hm1 h2 hm2
  linear_combination (2 / 3 : ℂ) * h1 - (2 / 3 : ℂ) * hm1 -
    (1 / 12 : ℂ) * h2 + (1 / 12 : ℂ) * hm2

lemma maximal_coordinates (a b c d e f g h i j : ℂ)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * symMatrix a b c d e f g h i j r s) = 24) :
    a = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 0 ∧ j = 0 ∧ d = -b - c := by
  have v0 := first_order a b c d e f g h i j hp 0 0
  have v1 := first_order a b c d e f g h i j hp 1 0
  have v2 := first_order a b c d e f g h i j hp (-1) 0
  have v3 := first_order a b c d e f g h i j hp 0 1
  have v4 := first_order a b c d e f g h i j hp 0 (-1)
  have v5 := first_order a b c d e f g h i j hp 1 1
  have he : e = j := by
    linear_combination (-2/3 : ℂ) * v0 + (5/12 : ℂ) * v1 + (1/4 : ℂ) * v2 + (1/3 : ℂ) * v3 + (-1/3 : ℂ) * v5
  have hf : f = j := by
    linear_combination (5/6 : ℂ) * v0 + (-3/8 : ℂ) * v1 + (-1/8 : ℂ) * v2 + (-3/8 : ℂ) * v3 + (-1/8 : ℂ) * v4 + (1/6 : ℂ) * v5
  have hg : g = j := by
    linear_combination (1/6 : ℂ) * v0 + (-1/24 : ℂ) * v1 + (-1/8 : ℂ) * v2 + (1/6 : ℂ) * v3 + (-1/6 : ℂ) * v5
  have hh : h = j := by
    linear_combination (-2/3 : ℂ) * v0 + (1/3 : ℂ) * v1 + (5/12 : ℂ) * v3 + (1/4 : ℂ) * v4 + (-1/3 : ℂ) * v5
  have hi : i = j := by
    linear_combination (1/6 : ℂ) * v0 + (1/6 : ℂ) * v1 + (-1/24 : ℂ) * v3 + (-1/8 : ℂ) * v4 + (-1/6 : ℂ) * v5
  have ha : a + 2 * (b + c + d) + 9 * j = 0 := by
    linear_combination (-5/6 : ℂ) * v0 + (-1/4 : ℂ) * v1 + (1/4 : ℂ) * v2 + (-1/4 : ℂ) * v3 + (1/4 : ℂ) * v4 + (1 : ℂ) * v5
  have hae : a = -2 * (b + c + d) - 9 * j := by
    linear_combination ha
  have h1 := hp 0 0 1
  have hm1 := hp 0 0 (-1)
  have h2 := hp 0 0 2
  have hm2 := hp 0 0 (-2)
  rw [he, hf, hg, hh, hi, hae] at h1 hm1 h2 hm2
  simp [perm4, Matrix.of_apply, star, symMatrix] at h1 hm1 h2 hm2
  have hq : 2 * ((b + c + d) ^ 2 - 6 * (b + c + d) * j - 63 * j ^ 2) = 0 := by
    linear_combination (2 / 3 : ℂ) * h1 + (2 / 3 : ℂ) * hm1 -
      (1 / 24 : ℂ) * h2 - (1 / 24 : ℂ) * hm2
  have hc : 4 * j * ((b + c + d) ^ 2 - 6 * (b + c + d) * j - 39 * j ^ 2) = 0 := by
    linear_combination (1 / 12 : ℂ) * h2 - (1 / 12 : ℂ) * hm2 -
      (1 / 6 : ℂ) * h1 + (1 / 6 : ℂ) * hm1
  have hj3 : j ^ 3 = 0 := by
    linear_combination (1 / 96 : ℂ) * hc - (j / 48) * hq
  have hj : j = 0 := eq_zero_of_pow_eq_zero hj3
  rw [hj] at hq
  have hp2 : (b + c + d) ^ 2 = 0 := by
    linear_combination (1 / 2 : ℂ) * hq
  have hp0 : b + c + d = 0 := eq_zero_of_pow_eq_zero hp2
  have hd : d = -b - c := by
    linear_combination hp0
  refine ⟨?_, he.trans hj, hf.trans hj, hg.trans hj, hh.trans hj, hi.trans hj, hj, hd⟩
  linear_combination ha - 2 * hp0 - 9 * hj

lemma star_plane_maximal (T : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, T r s = T s r)
    (hp : ∀ x y z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + star x y r s + z * T r s) = 24) :
    T = star (T 0 1) (T 0 2) := by
  have hT : T = symMatrix (T 0 0) (T 0 1) (T 0 2) (T 0 3)
      (T 1 1) (T 1 2) (T 1 3) (T 2 2) (T 2 3) (T 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [symMatrix]
    all_goals exact hs _ _
  have hc := maximal_coordinates (T 0 0) (T 0 1) (T 0 2) (T 0 3)
    (T 1 1) (T 1 2) (T 1 3) (T 2 2) (T 2 3) (T 3 3)
    (by simpa only [← hT] using hp)
  rcases hc with ⟨ha, he, hf, hg, hh, hi, hj, hd⟩
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [star, ha, he, hf, hg, hh, hi, hj, hd,
      hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]

end PEqualNP.Outside.L_gct_231_aux.StarMaximal
