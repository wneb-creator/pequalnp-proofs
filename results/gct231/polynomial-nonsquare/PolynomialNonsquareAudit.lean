import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal

namespace PEqualNP.Outside.L_gct_231_aux

open Polynomial

theorem polynomial_not_square_of_coefficients {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q : R[X]) (h0 : q.coeff 0 = 0) (h2 : q.coeff 2 = 0) (h3 : q.coeff 3 ≠ 0) :
    ¬ ∃ p : R[X], q = p ^ 2 := by
  rintro ⟨p, hp⟩
  have hp0 : p.coeff 0 = 0 := by
    have hz : p.coeff 0 * p.coeff 0 = 0 := by simpa [hp, pow_two] using h0
    exact (mul_eq_zero.mp hz).elim id id
  have hp1 : p.coeff 1 = 0 := by
    have hz : p.coeff 1 * p.coeff 1 = 0 := by
      simpa [hp, pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, hp0] using h2
    exact (mul_eq_zero.mp hz).elim id id
  apply h3
  simp [hp, pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1]

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.polynomial_not_square_of_coefficients
