import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

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


theorem range_witness
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hi : Function.Injective F)
    (hs : ∀ v, ∀ i j : Fin 4, F v (i, j) = F v (j, i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + F v (i, j)) = 24) :
    ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 3 ∧
      (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧
      ∀ t ∈ L, Matrix.permanent
        (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  refine ⟨LinearMap.range F, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hi]
    simp
  · rintro t ⟨v, rfl⟩ i j
    exact hs v i j
  · rintro t ⟨v, rfl⟩
    exact hp v

theorem injective_of_coordinates
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (p : Fin 3 → Fin 4 × Fin 4)
    (h : ∀ v k, F v (p k) = v k) : Function.Injective F := by
  intro v w hvw
  funext k
  have he := congrFun hvw (p k)
  simpa only [h] using he

theorem symmetric_permanent
    (a b c d e f g h i j : ℂ) :
    Matrix.permanent (!![a, e, f, g; e, b, h, i; f, h, c, j; g, i, j, d]) =
      a*b*c*d + a*b*j^2 + a*c*i^2 + a*d*h^2 + b*c*g^2 + b*d*f^2 + c*d*e^2 +
      2*a*h*i*j + 2*b*f*g*j + 2*c*e*g*i + 2*d*e*f*h +
      e^2*j^2 + f^2*i^2 + g^2*h^2 + 2*e*f*i*j + 2*e*g*h*j + 2*f*g*h*i := by
  rw [perm4]
  simp +decide [Matrix.of_apply]
  ring


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem total_entry_sum_zero (t : Fin 4 × Fin 4 → ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + z * t (i,j)) = 24) :
    ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0 := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  rw [perm4] at h1 hm1 h2 hm2
  simp only [Matrix.of_apply] at h1 hm1 h2 hm2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  linear_combination (1/9 : ℂ)*h1 - (1/9 : ℂ)*hm1 - (1/72 : ℂ)*h2 + (1/72 : ℂ)*hm2

theorem submodule_total_entry_sum_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hp : ∀ t ∈ L, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) = 24)
    (t : Fin 4 × Fin 4 → ℂ) (ht : t ∈ L) :
    ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0 := by
  apply total_entry_sum_zero
  intro z
  simpa only [Pi.smul_apply, smul_eq_mul] using hp (z • t) (L.smul_mem z ht)


theorem diagonal33_of_total_entry_sum_zero
    (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, t (i,j) = t (j,i))
    (hsum : ∑ i : Fin 4, ∑ j : Fin 4, t (i,j) = 0) :
    t (3,3) = -(t (0,0) + t (1,1) + t (2,2) +
      2 * (t (0,1) + t (0,2) + t (0,3) + t (1,2) + t (1,3) + t (2,3))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at hsum
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2] at hsum
  linear_combination hsum

end PEqualNP.Outside.L_gct_231_aux
