import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

noncomputable def parametricEntry
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ) (i j : Fin 4) :
    MvPolynomial (Fin 3) ℂ :=
  1 + ∑ k : Fin 3, MvPolynomial.C (A k (i,j)) * MvPolynomial.X k

theorem eval_parametricEntry
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ) (v : Fin 3 → ℂ) (i j : Fin 4) :
    MvPolynomial.eval v (parametricEntry A i j) =
      1 + ∑ k : Fin 3, A k (i,j) * v k := by
  simp [parametricEntry]

theorem polynomial_permanent_identity
    (A : Fin 3 → Fin 4 × Fin 4 → ℂ)
    (hp : ∀ v : Fin 3 → ℂ, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => 1 + ∑ k : Fin 3, A k (i,j) * v k) = 24) :
    Matrix.permanent (Matrix.of (parametricEntry A)) =
      (24 : MvPolynomial (Fin 3) ℂ) := by
  apply MvPolynomial.funext
  intro v
  simpa [Matrix.permanent, Matrix.of_apply, parametricEntry] using hp v

theorem linear_map_coordinate_expansion
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) (v : Fin 3 → ℂ) :
    F v = ∑ k : Fin 3, v k • F (Pi.single k 1) := by
  have hv : v = ∑ k : Fin 3, v k • Pi.single k 1 := by
    funext j
    simp [Pi.single_apply]
  calc
    F v = F (∑ k : Fin 3, v k • Pi.single k 1) := congrArg F hv
    _ = ∑ k : Fin 3, v k • F (Pi.single k 1) := by simp

theorem linear_map_polynomial_permanent_identity
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ v : Fin 3 → ℂ, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => 1 + F v (i,j)) = 24) :
    Matrix.permanent (Matrix.of (parametricEntry (fun k => F (Pi.single k 1)))) =
      (24 : MvPolynomial (Fin 3) ℂ) := by
  apply polynomial_permanent_identity
  intro v
  convert hp v using 1
  congr 1
  ext i j
  rw [linear_map_coordinate_expansion F v]
  simp [Finset.sum_apply, smul_eq_mul, mul_comm]

end PEqualNP.Outside.L_gct_231_aux
