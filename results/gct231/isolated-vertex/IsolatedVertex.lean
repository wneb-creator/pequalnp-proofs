import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_gct_231_aux.IsolatedVertex

lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


lemma four_coefficients_zero (L Q C F : ℂ)
    (h : ∀ z : ℂ, 24 + L*z + Q*z^2 + C*z^3 + F*z^4 = 24) :
    L = 0 ∧ Q = 0 ∧ C = 0 ∧ F = 0 := by
  have h1 := h 1
  have hn1 := h (-1)
  have h2 := h 2
  have hn2 := h (-2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (2/3 : ℂ) * h1 - (2/3 : ℂ) * hn1 -
      (1/12 : ℂ) * h2 + (1/12 : ℂ) * hn2
  · linear_combination (2/3 : ℂ) * h1 + (2/3 : ℂ) * hn1 -
      (1/24 : ℂ) * h2 - (1/24 : ℂ) * hn2
  · linear_combination -(1/6 : ℂ) * h1 + (1/6 : ℂ) * hn1 +
      (1/12 : ℂ) * h2 - (1/12 : ℂ) * hn2
  · linear_combination -(1/6 : ℂ) * h1 - (1/6 : ℂ) * hn1 +
      (1/24 : ℂ) * h2 + (1/24 : ℂ) * hn2

def blockSum (a b c e f g : ℂ) : ℂ := a + e + g + 2*b + 2*c + 2*f

def blockRookTwo (a b c e f g : ℂ) : ℂ :=
  a*e + a*g + e*g + b^2 + c^2 + f^2 + 2*(a*f + b*c + b*f + c*e + b*g + c*f)

def blockPermanent (a b c e f g : ℂ) : ℂ :=
  a*e*g + 2*b*c*f + a*f^2 + e*c^2 + g*b^2

def isolatedMatrix (d a b c e f g : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![d,0,0,0; 0,a,b,c; 0,b,e,f; 0,c,f,g]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
lemma isolated_permanent_expansion (d a b c e f g z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * isolatedMatrix d a b c e f g i j) =
    24 + (6*(blockSum a b c e f g+d))*z +
      (2*(blockRookTwo a b c e f g + blockSum a b c e f g*d))*z^2 +
      (blockPermanent a b c e f g + d*blockRookTwo a b c e f g)*z^3 +
      (d*blockPermanent a b c e f g)*z^4 := by
  rw [perm4]
  simp +decide [isolatedMatrix, Matrix.of_apply, blockSum, blockRookTwo, blockPermanent]
  ring

theorem isolated_matrix_diagonal_zero (d a b c e f g : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1 + z * isolatedMatrix d a b c e f g i j) = 24) : d = 0 := by
  obtain ⟨hL,hQ,hC,hF⟩ := four_coefficients_zero
    (6*(blockSum a b c e f g+d))
    (2*(blockRookTwo a b c e f g + blockSum a b c e f g*d))
    (blockPermanent a b c e f g + d*blockRookTwo a b c e f g)
    (d*blockPermanent a b c e f g)
    (fun z => (isolated_permanent_expansion d a b c e f g z).symm.trans (h z))
  have hd4 : d^4 = 0 := by
    linear_combination (d^3/6)*hL - (d^2/2)*hQ + d*hC - hF
  exact eq_zero_of_pow_eq_zero hd4

theorem isolated_vertex_zero_diagonal
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) = 24) : M 0 0 = 0 := by
  have h10 : M 1 0 = 0 := (hsym.apply 0 1).trans h01
  have h20 : M 2 0 = 0 := (hsym.apply 0 2).trans h02
  have h30 : M 3 0 = 0 := (hsym.apply 0 3).trans h03
  have h21 : M 2 1 = M 1 2 := hsym.apply 1 2
  have h31 : M 3 1 = M 1 3 := hsym.apply 1 3
  have h32 : M 3 2 = M 2 3 := hsym.apply 2 3
  have hm : M = isolatedMatrix (M 0 0) (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [isolatedMatrix, h01, h02, h03, h10, h20, h30, h21, h31, h32]
  apply isolated_matrix_diagonal_zero (M 0 0) (M 1 1) (M 1 2) (M 1 3) (M 2 2) (M 2 3) (M 3 3)
  intro z
  simpa only [← hm] using h z

theorem isolated_vertex_diagonal_zero
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm) (v : Fin 4)
    (hoff : ∀ j : Fin 4, j ≠ v → M v j = 0)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) = 24) : M v v = 0 := by
  let p : Equiv.Perm (Fin 4) := Equiv.swap 0 v
  let N : Matrix (Fin 4) (Fin 4) ℂ := fun i j => M (p i) (p j)
  have hp0 : p 0 = v := by simp [p]
  have hsymN : N.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hsym.apply (p i) (p j)
  have hoffN : ∀ j : Fin 4, j ≠ 0 → N 0 j = 0 := by
    intro j hj
    have hpj : p j ≠ v := by
      intro heq
      exact hj (p.injective (heq.trans hp0.symm))
    change M (p 0) (p j) = 0
    rw [hp0]
    exact hoff (p j) hpj
  have hN : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * N i j) = 24 := by
    intro z
    change Matrix.permanent (((Matrix.of fun (i j : Fin 4) => 1 + z * M i j).submatrix p id).submatrix id p) = 24
    rw [Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
    exact h z
  have hz := isolated_vertex_zero_diagonal N hsymN
    (hoffN 1 (by decide)) (hoffN 2 (by decide)) (hoffN 3 (by decide)) hN
  simpa only [N, hp0] using hz

end PEqualNP.Outside.L_gct_231_aux.IsolatedVertex
