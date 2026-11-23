import Mathlib

namespace PriorRoutes

theorem inverse_from_constant_one {R : Type} [CommRing R] (x g : R)
    (relation : 1 + x * g = 0) : IsUnit x := by
  refine ⟨⟨x, -g, ?_, ?_⟩, rfl⟩
  · linear_combination -relation
  · linear_combination -relation

theorem rejecting_minimal_polynomial {F : Type} [Field F]
    [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (error : Polynomial (ZMod 2)) (r : F) (hr : r ≠ 0)
    (rejects : Polynomial.aeval r error ≠ 0) :
    ∃ modulus : Polynomial (ZMod 2), modulus.Monic ∧
      0 < modulus.natDegree ∧
      modulus.natDegree ≤ Module.finrank (ZMod 2) F ∧
      modulus.coeff 0 = 1 ∧ ¬ modulus ∣ error := by
  have integral : IsIntegral (ZMod 2) r := Algebra.IsIntegral.isIntegral r
  refine ⟨minpoly (ZMod 2) r, minpoly.monic integral, ?_, minpoly.natDegree_le r, ?_, ?_⟩
  · exact minpoly.natDegree_pos integral
  · have h := minpoly.coeff_zero_ne_zero integral hr
    have cases : (minpoly (ZMod 2) r).coeff 0 = 0 ∨
        (minpoly (ZMod 2) r).coeff 0 = 1 := by
      have all_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact all_cases _
    exact cases.resolve_left h
  · intro divides
    apply rejects
    exact minpoly.dvd_iff.mp divides

end PriorRoutes
