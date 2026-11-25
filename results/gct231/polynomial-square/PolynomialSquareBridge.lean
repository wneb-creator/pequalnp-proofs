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

end PEqualNP.Outside.L_gct_231_aux
