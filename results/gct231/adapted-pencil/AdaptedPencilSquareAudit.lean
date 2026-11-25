import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_gct_231_aux

open Matrix

theorem block_zero_det_square {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) :
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).det = B.det ^ 2 := by
  have hs : Equiv.Perm.sign (Equiv.sumComm (Fin 2) (Fin 2)) = 1 := by decide
  have hm :
      (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).submatrix
          (Equiv.sumComm (Fin 2) (Fin 2)) id =
        Matrix.fromBlocks Bᵀ D (0 : Matrix (Fin 2) (Fin 2) R) B := by
    ext i j
    cases i <;> cases j <;> rfl
  have hd := Matrix.det_permute (Equiv.sumComm (Fin 2) (Fin 2))
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D)
  simpa [hm, hs, Matrix.det_fromBlocks_zero₂₁, pow_two] using hd.symm

theorem block_zero_det_congruence {R : Type*} [CommRing R]
    (M P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (B D : Matrix (Fin 2) (Fin 2) R)
    (h : Pᵀ * M * P = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D) :
    P.det ^ 2 * M.det = B.det ^ 2 := by
  simpa [Matrix.det_mul, block_zero_det_square, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using congrArg Matrix.det h

open Polynomial

theorem polynomial_det_square_of_constant_congruence
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X])
    (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (B D : Matrix (Fin 2) (Fin 2) ℂ[X]) (hp : P.det ≠ 0)
    (h : (P.map C)ᵀ * M * P.map C =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ[X]) B Bᵀ D) :
    ∃ p : ℂ[X], M.det = p ^ 2 := by
  have hd : (P.map C).det = C P.det := (C.map_det P).symm
  have hs := block_zero_det_congruence M (P.map C) B D h
  rw [hd] at hs
  have hi : C (P.det)⁻¹ * C P.det = (1 : ℂ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hp, map_one]
  refine ⟨C (P.det)⁻¹ * B.det, ?_⟩
  calc
    M.det = (C (P.det)⁻¹ * C P.det) ^ 2 * M.det := by rw [hi]; simp
    _ = C (P.det)⁻¹ ^ 2 * (C P.det ^ 2 * M.det) := by ring
    _ = (C (P.det)⁻¹ * B.det) ^ 2 := by rw [hs]; ring

theorem symmetric_zero_block {R : Type*} [CommRing R]
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (hm : M.IsSymm)
    (hz : ∀ i j : Fin 2, M (Sum.inl i) (Sum.inl j) = 0) :
    M = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R)
      (fun i j => M (Sum.inl i) (Sum.inr j))
      (fun i j => M (Sum.inl i) (Sum.inr j))ᵀ
      (fun i j => M (Sum.inr i) (Sum.inr j)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact hz i j
  · rfl
  · exact (hm.apply (Sum.inr i) (Sum.inl j)).symm
  · rfl

theorem symmetric_congruence {R : Type*} [CommRing R]
    {n : Type*} [Fintype n]
    (M P : Matrix n n R) (hm : M.IsSymm) : (Pᵀ * M * P).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hm.eq,
    Matrix.mul_assoc]

theorem determinant_pencil_square_of_adapted
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (hm0 : ∀ i j : Fin 2, (Pᵀ * M * P) (Sum.inl i) (Sum.inl j) = 0)
    (hn0 : ∀ i j : Fin 2, (Pᵀ * N * P) (Sum.inl i) (Sum.inl j) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  let L : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X] :=
    N.map C - (X : ℂ[X]) • M.map C
  have hi : (P.map C)ᵀ * L * P.map C =
      (Pᵀ * N * P).map C - (X : ℂ[X]) • (Pᵀ * M * P).map C := by
    simp only [L, Matrix.map_mul, Matrix.transpose_map, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j : Fin 2, ((P.map C)ᵀ * L * P.map C) (Sum.inl i) (Sum.inl j) = 0 := by
    intro i j
    rw [hi]
    change C ((Pᵀ * N * P) (Sum.inl i) (Sum.inl j)) -
      X * C ((Pᵀ * M * P) (Sum.inl i) (Sum.inl j)) = 0
    rw [hn0, hm0, map_zero, mul_zero, sub_zero]
  have hl : L.IsSymm := (hn.map C).sub ((hm.map C).smul X)
  exact polynomial_det_square_of_constant_congruence L P _ _ hp
    (symmetric_zero_block _ (symmetric_congruence L (P.map C) hl) hz)

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.polynomial_det_square_of_constant_congruence
#print axioms PEqualNP.Outside.L_gct_231_aux.determinant_pencil_square_of_adapted
