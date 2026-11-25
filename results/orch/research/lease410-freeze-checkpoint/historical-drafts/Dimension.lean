import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Complex.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231

def threeParameterMap (A B C : Fin 4 × Fin 4 → ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun v := v 0 • A + v 1 • B + v 2 • C
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

lemma range_finrank_three
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hf : Function.Injective f) :
    Module.finrank ℂ (LinearMap.range f) = 3 := by
  rw [LinearMap.finrank_range_of_inj hf]
  simp

lemma range_coordinates
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (t : Fin 4 × Fin 4 → ℂ) :
    t ∈ LinearMap.range f ↔ ∃ v : Fin 3 → ℂ, f v = t := by
  rfl

lemma injective_of_coordinate_recovery
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (p : Fin 3 → Fin 4 × Fin 4)
    (hp : ∀ v i, f v (p i) = v i) :
    Function.Injective f := by
  intro v w h
  funext i
  simpa only [hp] using congrArg (fun t => t (p i)) h

lemma range_level_space
    (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hf : Function.Injective f)
    (hs : ∀ v i j, f v (i, j) = f v (j, i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + f v (i, j)) = 24) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
      Module.finrank ℂ L = 3 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range f, range_finrank_three f hf, ?_, ?_⟩
  · rintro t ⟨v, rfl⟩ i j
    exact hs v i j
  · rintro t ⟨v, rfl⟩
    exact hp v

end PEqualNP.Outside.L_gct_231
