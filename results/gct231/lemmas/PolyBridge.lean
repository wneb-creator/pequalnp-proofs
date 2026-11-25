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

end PEqualNP.Outside.L_gct_231_aux
