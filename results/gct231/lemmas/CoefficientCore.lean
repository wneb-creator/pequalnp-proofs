import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux.Coeff

noncomputable def affine3 (a b c : ℂ) : MvPolynomial (Fin 3) ℂ :=
  1 + MvPolynomial.C a * MvPolynomial.X 0 +
    MvPolynomial.C b * MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 2

noncomputable def mixed (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))

theorem coeff_xy_via_deriv (p : MvPolynomial (Fin 3) ℂ) :
    p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) = mixed p := by
  simp [mixed, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv]

theorem mixed_add (p q : MvPolynomial (Fin 3) ℂ) : mixed (p+q) = mixed p + mixed q := by
  simp [mixed]

theorem mixed_nat (n : ℕ) : mixed (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [mixed]

theorem mixed_four_affine
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    mixed (affine3 a0 a1 a2 * affine3 b0 b1 b2 *
      affine3 c0 c1 c2 * affine3 d0 d1 d2) =
      a0*b1 + a1*b0 + a0*c1 + a1*c0 + a0*d1 + a1*d0 +
      b0*c1 + b1*c0 + b0*d1 + b1*d0 + c0*d1 + c1*d0 := by
  simp [mixed, affine3, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_one, Pi.single_apply]
  ring

end PEqualNP.Outside.L_gct_231_aux.Coeff
