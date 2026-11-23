import Mathlib

namespace PEqualNP.Outside.FingerprintBudget

lemma nonzero_kernel_of_small_card (F : Type*) [AddCommGroup F] [Module (ZMod 2) F]
    [Fintype F] (d : ℕ) (hcard : Fintype.card F ≤ 2 ^ d)
    (f : (Fin (d + 1) → ZMod 2) →ₗ[ZMod 2] F) :
    ∃ c : Fin (d + 1) → ZMod 2, c ≠ 0 ∧ f c = 0 := by
  have hnot : ¬ Function.Injective f := by
    intro hi
    have hc := Fintype.card_le_of_injective f hi
    have hexp : 2 ^ (d + 1) ≤ 2 ^ d := by
      simpa using hc.trans hcard
    have hpos : 0 < 2 ^ d := by positivity
    rw [pow_succ] at hexp
    omega
  rw [Function.Injective] at hnot
  push Not at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  simp [hab]

noncomputable def evaluation (F : Type*) [Field F] [Algebra (ZMod 2) F]
    (d : ℕ) (r : F) : (Fin (d + 1) → ZMod 2) →ₗ[ZMod 2] F where
  toFun c := ∑ i, algebraMap (ZMod 2) F (c i) * r ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [mul_assoc, Finset.mul_sum, Algebra.smul_def]

lemma adaptive_collision (F : Type*) [Field F] [Algebra (ZMod 2) F]
    [Fintype F] (d : ℕ) (hcard : Fintype.card F ≤ 2 ^ d) :
    ∀ r : F, ∃ c : Fin (d + 1) → ZMod 2,
      c ≠ 0 ∧ ∑ i, algebraMap (ZMod 2) F (c i) * r ^ (i : ℕ) = 0 := by
  intro r
  exact nonzero_kernel_of_small_card F d hcard (evaluation F d r)

end PEqualNP.Outside.FingerprintBudget
