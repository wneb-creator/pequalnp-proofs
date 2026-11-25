import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_gct_231_aux

open Polynomial

theorem quartic_square_coefficient_identities {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q p : R[X]) (hdeg : q.natDegree ≤ 4) (hsq : q = p ^ 2) :
    8 * q.coeff 4 ^ 2 * q.coeff 1 -
        4 * q.coeff 4 * q.coeff 3 * q.coeff 2 + q.coeff 3 ^ 3 = 0 ∧
      (4 * q.coeff 4 * q.coeff 2 - q.coeff 3 ^ 2) ^ 2 -
        64 * q.coeff 4 ^ 3 * q.coeff 0 = 0 := by
  have hroot : p.natDegree ≤ 2 := by
    rw [hsq, Polynomial.natDegree_pow] at hdeg
    omega
  have hp3 : p.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hp4 : p.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h4 : q.coeff 4 = p.coeff 2 ^ 2 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3, hp4]
  have h3 : q.coeff 3 = 2 * p.coeff 2 * p.coeff 1 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3]
    ring
  have h2 : q.coeff 2 = p.coeff 1 ^ 2 + 2 * p.coeff 2 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h1 : q.coeff 1 = 2 * p.coeff 1 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h0 : q.coeff 0 = p.coeff 0 ^ 2 := by simp [hsq, pow_two]
  constructor
  · rw [h4, h3, h2, h1]
    ring
  · rw [h4, h3, h2, h0]
    ring

end PEqualNP.Outside.L_gct_231_aux
