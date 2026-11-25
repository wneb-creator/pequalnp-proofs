import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Field.ZMod

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


set_option maxHeartbeats 800000 in
theorem no_common_complex_zero_of_modular_coprime
    (f g : Polynomial ℤ) (p m n : ℕ) [Fact p.Prime]
    (hfdeg : f.natDegree ≤ m) (hgdeg : g.natDegree ≤ n) (hmpos : 0 < m)
    (hfmod : (f.map (Int.castRingHom (ZMod p))).natDegree = m)
    (hgmod : (g.map (Int.castRingHom (ZMod p))).natDegree = n)
    (hcoprime : IsCoprime (f.map (Int.castRingHom (ZMod p)))
      (g.map (Int.castRingHom (ZMod p))))
    (z : ℂ)
    (hf : (f.map (Int.castRingHom ℂ)).eval z = 0)
    (hg : (g.map (Int.castRingHom ℂ)).eval z = 0) : False := by
  have hc : Polynomial.resultant (f.map (Int.castRingHom ℂ))
      (g.map (Int.castRingHom ℂ)) m n = 0 :=
    resultant_zero_of_common_root _ _ z m n
      (Polynomial.natDegree_map_le.trans hfdeg)
      (Polynomial.natDegree_map_le.trans hgdeg) hmpos hf hg
  have hz : Polynomial.resultant f g m n = 0 := by
    have hcast : ((Polynomial.resultant f g m n : ℤ) : ℂ) = 0 := by
      simpa only [Polynomial.resultant_map_map, Int.coe_castRingHom] using hc
    exact Int.cast_eq_zero.mp hcast
  have hp : Polynomial.resultant (f.map (Int.castRingHom (ZMod p)))
      (g.map (Int.castRingHom (ZMod p))) m n = 0 := by
    rw [Polynomial.resultant_map_map, hz, map_zero]
  rw [← hfmod, ← hgmod] at hp
  exact Polynomial.resultant_ne_zero _ _ hcoprime hp

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.no_common_complex_zero_of_modular_coprime
