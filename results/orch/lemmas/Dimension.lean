import Mathlib

namespace PEqualNP.Outside.L_gct_231_aux

lemma range_finrank_three
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hF : Function.Injective F) :
    Module.finrank ℂ F.range = 3 := by
  rw [LinearMap.finrank_range_of_inj hF]
  simp

lemma level_space_of_linearMap
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hF : Function.Injective F)
    (hS : ∀ x (i j : Fin 4), F x (i, j) = F x (j, i))
    (hP : ∀ x, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (1 : ℂ) + F x (i, j)) = 24) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 3 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨F.range, range_finrank_three F hF, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩ i j
    exact hS x i j
  · rintro t ⟨x, rfl⟩
    exact hP x

def threeSpanMap (A B C : Fin 4 × Fin 4 → ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun := fun x p => x 0 * A p + x 1 * B p + x 2 * C p
  map_add' := by
    intro x y
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro a x
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma permanent_four (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.permanent A =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 +
      A 0 0 * A 1 1 * A 3 2 * A 2 3 +
      A 0 0 * A 2 1 * A 1 2 * A 3 3 +
      A 0 0 * A 2 1 * A 3 2 * A 1 3 +
      A 0 0 * A 3 1 * A 1 2 * A 2 3 +
      A 0 0 * A 3 1 * A 2 2 * A 1 3 +
      A 1 0 * A 0 1 * A 2 2 * A 3 3 +
      A 1 0 * A 0 1 * A 3 2 * A 2 3 +
      A 1 0 * A 2 1 * A 0 2 * A 3 3 +
      A 1 0 * A 2 1 * A 3 2 * A 0 3 +
      A 1 0 * A 3 1 * A 0 2 * A 2 3 +
      A 1 0 * A 3 1 * A 2 2 * A 0 3 +
      A 2 0 * A 0 1 * A 1 2 * A 3 3 +
      A 2 0 * A 0 1 * A 3 2 * A 1 3 +
      A 2 0 * A 1 1 * A 0 2 * A 3 3 +
      A 2 0 * A 1 1 * A 3 2 * A 0 3 +
      A 2 0 * A 3 1 * A 0 2 * A 1 3 +
      A 2 0 * A 3 1 * A 1 2 * A 0 3 +
      A 3 0 * A 0 1 * A 1 2 * A 2 3 +
      A 3 0 * A 0 1 * A 2 2 * A 1 3 +
      A 3 0 * A 1 1 * A 0 2 * A 2 3 +
      A 3 0 * A 1 1 * A 2 2 * A 0 3 +
      A 3 0 * A 2 1 * A 0 2 * A 1 3 +
      A 3 0 * A 2 1 * A 1 2 * A 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring

end PEqualNP.Outside.L_gct_231_aux
