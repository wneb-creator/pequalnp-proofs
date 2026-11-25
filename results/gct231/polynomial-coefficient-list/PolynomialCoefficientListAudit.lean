import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace PEqualNP.Outside.L_gct_231_aux

noncomputable def polynomialOfCoeffs {R : Type*} [Semiring R] : List R → Polynomial R
  | [] => 0
  | a :: cs => Polynomial.C a + Polynomial.X * polynomialOfCoeffs cs

theorem polynomialOfCoeffs_coeff {R : Type*} [Semiring R] (cs : List R) (n : ℕ) :
    (polynomialOfCoeffs cs).coeff n = (cs[n]?).getD 0 := by
  induction cs generalizing n with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih =>
    cases n <;> simp [polynomialOfCoeffs, Polynomial.coeff_X_mul, ih]

theorem polynomialOfCoeffs_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (cs : List R) :
    (polynomialOfCoeffs cs).map f = polynomialOfCoeffs (cs.map f) := by
  induction cs with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih =>
    simp [polynomialOfCoeffs, Polynomial.map_add, Polynomial.map_mul, ih]

theorem polynomialOfCoeffs_eval {R : Type*} [CommSemiring R]
    (cs : List R) (z : R) :
    (polynomialOfCoeffs cs).eval z = cs.foldr (fun a v => a + z*v) 0 := by
  induction cs with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih => simp [polynomialOfCoeffs, ih]

theorem polynomialOfCoeffs_degree_le {R : Type*} [Semiring R] (cs : List R) :
    (polynomialOfCoeffs cs).natDegree ≤ cs.length - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomialOfCoeffs_coeff]
  have hlen : cs.length ≤ n := by omega
  have hz : cs[n]? = none := by simp only [List.getElem?_eq_none_iff]; exact hlen
  simp [hz]

theorem polynomialOfCoeffs_degree_eq {R : Type*} [Semiring R]
    (cs : List R) (n : ℕ) (hlen : cs.length = n + 1)
    (hlast : (cs[n]?).getD 0 ≠ 0) :
    (polynomialOfCoeffs cs).natDegree = n := by
  apply le_antisymm
  · simpa [hlen] using polynomialOfCoeffs_degree_le cs
  · apply Polynomial.le_natDegree_of_ne_zero
    simpa [polynomialOfCoeffs_coeff] using hlast

end PEqualNP.Outside.L_gct_231_aux

#print axioms PEqualNP.Outside.L_gct_231_aux.polynomialOfCoeffs_coeff
#print axioms PEqualNP.Outside.L_gct_231_aux.polynomialOfCoeffs_map
#print axioms PEqualNP.Outside.L_gct_231_aux.polynomialOfCoeffs_eval
#print axioms PEqualNP.Outside.L_gct_231_aux.polynomialOfCoeffs_degree_le
#print axioms PEqualNP.Outside.L_gct_231_aux.polynomialOfCoeffs_degree_eq
