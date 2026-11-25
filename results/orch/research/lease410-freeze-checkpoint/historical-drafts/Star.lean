import Mathlib.Tactic.FinCases
import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def starMatrix {R : Type*} [CommRing R] (a b : R) : Fin 4 × Fin 4 → R :=
  fun p => (!![0, a, b, -a-b;
              a, 0, 0, 0;
              b, 0, 0, 0;
              -a-b, 0, 0, 0] : Matrix (Fin 4) (Fin 4) R) p.1 p.2

lemma starMatrix_symmetric {R : Type*} [CommRing R] (a b : R) (i j : Fin 4) :
    starMatrix a b (i, j) = starMatrix a b (j, i) := by
  fin_cases i <;> fin_cases j <;> simp [starMatrix]

lemma starMatrix_permanent {R : Type*} [CommRing R] (a b : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i, j)) = 24 := by
  rw [permanent_four]
  simp [starMatrix]
  ring

def starMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v := starMatrix (v 0) (v 1)
  map_add' v w := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix] <;> ring
  map_smul' c v := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [starMatrix, smul_eq_mul] <;> ring

lemma starMap_injective : Function.Injective starMap := by
  intro v w h
  funext i
  fin_cases i
  · simpa [starMap, starMatrix] using congrFun h (0, 1)
  · simpa [starMap, starMatrix] using congrFun h (0, 2)

lemma starMap_finrank : Module.finrank ℂ (LinearMap.range starMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj starMap_injective]
  simp

lemma star_two_dimensional :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
      Module.finrank ℂ L = 2 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range starMap, starMap_finrank, ?_, ?_⟩
  · rintro t ⟨v, rfl⟩ i j
    exact starMatrix_symmetric (v 0) (v 1) i j
  · rintro t ⟨v, rfl⟩
    exact starMatrix_permanent (v 0) (v 1)

end PEqualNP.Outside.L_gct_231
