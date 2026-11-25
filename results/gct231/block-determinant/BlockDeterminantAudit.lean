import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.block_zero_det_square
#print axioms PEqualNP.Outside.L_gct_231_aux.block_zero_det_congruence
