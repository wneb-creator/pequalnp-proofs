import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace PEqualNP.Outside.L_gct_231_aux

theorem resultant_zero_of_common_root {K : Type*} [Field K]
    (f g : Polynomial K) (z : K) (m n : ℕ)
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n) (hpos : 0 < m)
    (hf : f.eval z = 0) (hg : g.eval z = 0) :
    Polynomial.resultant f g m n = 0 := by
  classical
  by_cases hne : f ≠ 0 ∨ g ≠ 0
  · have hbase : Polynomial.resultant f g = 0 := by
      apply Polynomial.resultant_eq_zero_iff.mpr
      refine ⟨hne, ?_⟩
      rintro ⟨a, b, hab⟩
      have he := congrArg (Polynomial.eval z) hab
      simp [Polynomial.eval_add, Polynomial.eval_mul, hf, hg] at he
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hn
    rw [hk, hl]
    rw [Polynomial.resultant_add_left_deg f g f.natDegree
      (g.natDegree + l) k (le_refl _)]
    rw [Polynomial.resultant_add_right_deg f g f.natDegree g.natDegree l (le_refl _)]
    rw [hbase]
    simp
  · have hf0 : f = 0 := by
      by_contra h
      exact hne (Or.inl h)
    have hg0 : g = 0 := by
      by_contra h
      exact hne (Or.inr h)
    have hsum : m + n ≠ 0 := by omega
    rw [hf0, hg0, Polynomial.resultant_zero_zero]
    exact zero_pow hsum

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.resultant_zero_of_common_root
