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
  simp [mixed, affine3]
  ring

lemma sum_perm_succ_poly {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → (MvPolynomial (Fin 3) ℂ)) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4_poly (M : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ)) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ_poly]
  simp only [sum_perm_succ_poly (n := 2), sum_perm_succ_poly (n := 1), sum_perm_succ_poly (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


noncomputable def fullStarMatrix (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  !![affine3 d0 d1 d2, affine3 1 0 0, affine3 0 1 0, affine3 0 0 1;
    affine3 1 0 0, affine3 d3 d4 d5, affine3 o0 o1 o2, affine3 o3 o4 o5;
    affine3 0 1 0, affine3 o0 o1 o2, affine3 d6 d7 d8, affine3 o6 o7 o8;
    affine3 0 0 1, affine3 o3 o4 o5, affine3 o6 o7 o8, affine3 (-(d0+d3+d6+2*(1+o0+o3+o6)))
      (-(d1+d4+d7+2*(1+o1+o4+o7)))
      (-(d2+d5+d8+2*(1+o2+o5+o8)))]

set_option maxHeartbeats 4000000 in
theorem full_star_xy_coefficient (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1) =
      -2*(2*d0*d1 + d0*d4 + d0*d7 + 2*d0*o1 + 4*d0 + d1*d3 + d1*d6 + 2*d1*o0 + 4*d1 + 2*d3*d4 + d3*d7 + 4*d3*o1 + 2*d3*o4 + 2*d3 + d4*d6 + 4*d4*o0 + 2*d4*o3 + 4*d4 + 2*d6*d7 + 4*d6*o1 + 2*d6*o7 + 4*d6 + 4*d7*o0 + 2*d7*o6 + 2*d7 + 6*o0*o1 + 2*o0*o4 + 2*o0*o7 + 6*o0 + 2*o1*o3 + 2*o1*o6 + 6*o1 - 2*o3*o4 - 2*o3*o7 - 2*o4*o6 + 2*o4 - 2*o6*o7 + 2*o6 + 6) := by
  rw [coeff_xy_via_deriv, perm4_poly]
  simp [fullStarMatrix, mixed_add, mixed_four_affine]
  ring

theorem full_star_xy_zero (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    -2*(2*d0*d1 + d0*d4 + d0*d7 + 2*d0*o1 + 4*d0 + d1*d3 + d1*d6 + 2*d1*o0 + 4*d1 + 2*d3*d4 + d3*d7 + 4*d3*o1 + 2*d3*o4 + 2*d3 + d4*d6 + 4*d4*o0 + 2*d4*o3 + 4*d4 + 2*d6*d7 + 4*d6*o1 + 2*d6*o7 + 4*d6 + 4*d7*o0 + 2*d7*o6 + 2*d7 + 6*o0*o1 + 2*o0*o4 + 2*o0*o7 + 6*o0 + 2*o1*o3 + 2*o1*o6 + 6*o1 - 2*o3*o4 - 2*o3*o7 - 2*o4*o6 + 2*o4 - 2*o6*o7 + 2*o6 + 6) = 0 := by
  rw [← full_star_xy_coefficient d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8, h, coeff_xy_via_deriv]
  exact mixed_nat 24


noncomputable def triple (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))

noncomputable def quartic (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0
      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem coeff_xyz_via_deriv (p : MvPolynomial (Fin 3) ℂ) :
    p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) =
      triple p := by
  simp [triple, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv]

theorem quartic_eq_two_coeff (p : MvPolynomial (Fin 3) ℂ) :
    quartic p = 2 * p.coeff
      (Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 2 1) := by
  have he : Finsupp.single (0 : Fin 3) 1 + Finsupp.single 0 1 =
      Finsupp.single 0 2 := by rw [← Finsupp.single_add]
  simp [quartic, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv, he, mul_comm]
  norm_num

theorem triple_add (p q : MvPolynomial (Fin 3) ℂ) :
    triple (p+q) = triple p + triple q := by simp [triple]

theorem quartic_add (p q : MvPolynomial (Fin 3) ℂ) :
    quartic (p+q) = quartic p + quartic q := by simp [quartic]

theorem triple_nat (n : ℕ) : triple (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [triple]

theorem quartic_nat (n : ℕ) : quartic (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [quartic]

theorem triple_four_affine (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    triple (affine3 a0 a1 a2 * affine3 b0 b1 b2 *
      affine3 c0 c1 c2 * affine3 d0 d1 d2) =
      a0*b1*c2 + a0*b1*d2 + a0*c1*b2 + a0*c1*d2 + a0*d1*b2 + a0*d1*c2 + b0*a1*c2 + b0*a1*d2 + b0*c1*a2 + b0*c1*d2 + b0*d1*a2 + b0*d1*c2 + c0*a1*b2 + c0*a1*d2 + c0*b1*a2 + c0*b1*d2 + c0*d1*a2 + c0*d1*b2 + d0*a1*b2 + d0*a1*c2 + d0*b1*a2 + d0*b1*c2 + d0*c1*a2 + d0*c1*b2 := by
  simp [triple, affine3]
  ring

theorem quartic_four_affine (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    quartic (affine3 a0 a1 a2 * affine3 b0 b1 b2 *
      affine3 c0 c1 c2 * affine3 d0 d1 d2) =
      2 * (a0*b0*c1*d2 + a0*b0*c2*d1 + a0*b1*c0*d2 + a0*b1*c2*d0 + a0*b2*c0*d1 + a0*b2*c1*d0 + a1*b0*c0*d2 + a1*b0*c2*d0 + a1*b2*c0*d0 + a2*b0*c0*d1 + a2*b0*c1*d0 + a2*b1*c0*d0) := by
  simp [quartic, affine3]
  ring

set_option maxHeartbeats 4000000 in
theorem full_star_xyz_coefficient (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) =
      -2*(d0*d1*d5 + d0*d1*d8 + 2*d0*d1*o2 + d0*d2*d4 + d0*d2*d7 + 2*d0*d2*o1 + d0*d4*d5 + d0*d4*d8 + 2*d0*d4*o2 + d0*d4*o5 + d0*d4 + d0*d5*d7 + 2*d0*d5*o1 + d0*d5*o4 + 2*d0*d5 + d0*d7*d8 + 2*d0*d7*o2 + d0*d7*o8 + d0*d7 + 2*d0*d8*o1 + d0*d8*o7 + d0*d8 + 4*d0*o1*o2 + d0*o1*o5 + d0*o1*o8 + 2*d0*o1 + d0*o2*o4 + d0*o2*o7 + 3*d0*o2 - d0*o4*o5 - d0*o4*o8 - d0*o5*o7 - d0*o7*o8 + d1*d2*d3 + d1*d2*d6 + 2*d1*d2*o0 + d1*d3*d5 + d1*d3*d8 + 2*d1*d3*o2 + d1*d3*o5 + d1*d3 + d1*d5*d6 + 2*d1*d5*o0 + d1*d5*o3 + d1*d5 + d1*d6*d8 + 2*d1*d6*o2 + d1*d6*o8 + d1*d6 + 2*d1*d8*o0 + d1*d8*o6 + 2*d1*d8 + 4*d1*o0*o2 + d1*o0*o5 + d1*o0*o8 + 2*d1*o0 + d1*o2*o3 + d1*o2*o6 + 3*d1*o2 - d1*o3*o5 - d1*o3*o8 - d1*o5*o6 - d1*o6*o8 + d2*d3*d4 + d2*d3*d7 + 2*d2*d3*o1 + d2*d3*o4 + 2*d2*d3 + d2*d4*d6 + 2*d2*d4*o0 + d2*d4*o3 + d2*d4 + d2*d6*d7 + 2*d2*d6*o1 + d2*d6*o7 + d2*d6 + 2*d2*d7*o0 + d2*d7*o6 + 2*d2*d7 + 4*d2*o0*o1 + d2*o0*o4 + d2*o0*o7 + 3*d2*o0 + d2*o1*o3 + d2*o1*o6 + 3*d2*o1 - d2*o3*o4 - d2*o3*o7 - d2*o4*o6 - d2*o6*o7 + d2 + d3*d4*d8 + d3*d5*d7 + 2*d3*d5 + d3*d7*d8 + d3*d7*o2 + d3*d7*o5 + d3*d7*o8 + d3*d8*o1 + d3*d8*o4 + d3*d8*o7 + 2*d3*d8 + d3*o1*o2 + 3*d3*o2 + 2*d3*o5 - d3*o7*o8 - d3*o7 + d3*o8 + d3 + d4*d5*d6 + d4*d6*d8 + d4*d6*o2 + d4*d6*o5 + d4*d6*o8 + d4*d8*o0 + d4*d8*o3 + d4*d8*o6 + 2*d4*d8 + d4*o0*o2 + d4*o2 - d4*o6*o8 - d4*o6 + d5*d6*d7 + d5*d6*o1 + d5*d6*o4 + d5*d6*o7 + 2*d5*d6 + d5*d7*o0 + d5*d7*o3 + d5*d7*o6 + 2*d5*d7 + d5*o0*o1 + 3*d5*o0 + d5*o1 + 2*d5*o3 - d5*o6*o7 + d5*o6 + 3*d5 + d6*o1*o2 + d6*o2 - d6*o4*o5 - d6*o4 + 2*d7*d8 + d7*o0*o2 + 3*d7*o2 - d7*o3*o5 - d7*o3 + d7*o5 + 2*d7*o8 + d7 + d8*o0*o1 + d8*o0 + 3*d8*o1 - d8*o3*o4 + d8*o4 + 2*d8*o7 + 3*d8 + 6*o0*o1*o2 + 2*o0*o1*o5 + 2*o0*o1*o8 + 2*o0*o2*o4 + 2*o0*o2*o7 + 6*o0*o2 - o0*o4*o8 - o0*o4 - o0*o5*o7 + o0*o5 - o0*o7 + 2*o0*o8 + o0 + 2*o1*o2*o3 + 2*o1*o2*o6 + 6*o1*o2 - o1*o3*o8 - o1*o3 - o1*o5*o6 + 2*o1*o5 - o1*o6 + o1*o8 + o1 - o2*o3*o7 + o2*o3 - o2*o4*o6 + 2*o2*o4 + 2*o2*o6 + o2*o7 + 5*o2 - 2*o3*o5 - o3*o8 - o3 - o4*o8 - o4 - o5*o6 - o5*o7 + o5 - o6 - 2*o7*o8 - o7 + o8 + 2) := by
  rw [coeff_xyz_via_deriv, perm4_poly]
  simp [fullStarMatrix, triple_add, triple_four_affine]
  ring

set_option maxHeartbeats 4000000 in
theorem full_star_xxyz_coefficient (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 2 1) =
      -d0^2*d4*d8 - d0^2*d5*d7 - 2*d0^2*o1*o2 - 2*d0*d1*d3*d8 - 2*d0*d1*d5*d6 - 4*d0*d1*o0*o2 - 2*d0*d2*d3*d7 - 2*d0*d2*d4*d6 - 4*d0*d2*o0*o1 - 2*d0*d3*d4*d8 - 2*d0*d3*d5*d7 - 2*d0*d3*d7*d8 - 2*d0*d3*d7*o2 - 2*d0*d3*d7*o5 - 2*d0*d3*d7*o8 - 2*d0*d3*d7 - 2*d0*d3*d8*o1 - 2*d0*d3*d8*o4 - 2*d0*d3*d8*o7 - 2*d0*d3*d8 - 2*d0*d3*o1*o2 + 2*d0*d3*o7*o8 - 2*d0*d4*d5*d6 - 2*d0*d4*d6*d8 - 2*d0*d4*d6*o2 - 2*d0*d4*d6*o5 - 2*d0*d4*d6*o8 - 2*d0*d4*d6 - 2*d0*d4*d8*o0 - 2*d0*d4*d8*o3 - 2*d0*d4*d8*o6 - 2*d0*d4*d8 - 2*d0*d4*o0*o2 + 2*d0*d4*o6*o8 - 2*d0*d5*d6*d7 - 2*d0*d5*d6*o1 - 2*d0*d5*d6*o4 - 2*d0*d5*d6*o7 - 2*d0*d5*d6 - 2*d0*d5*d7*o0 - 2*d0*d5*d7*o3 - 2*d0*d5*d7*o6 - 2*d0*d5*d7 - 2*d0*d5*o0*o1 + 2*d0*d5*o6*o7 - 2*d0*d6*o1*o2 + 2*d0*d6*o4*o5 - 2*d0*d7*o0*o2 + 2*d0*d7*o3*o5 - 2*d0*d8*o0*o1 + 2*d0*d8*o3*o4 - 12*d0*o0*o1*o2 - 4*d0*o0*o1*o5 - 4*d0*o0*o1*o8 - 4*d0*o0*o1 - 4*d0*o0*o2*o4 - 4*d0*o0*o2*o7 - 4*d0*o0*o2 + 2*d0*o0*o4*o8 + 2*d0*o0*o5*o7 - 4*d0*o1*o2*o3 - 4*d0*o1*o2*o6 - 4*d0*o1*o2 + 2*d0*o1*o3*o8 + 2*d0*o1*o5*o6 + 2*d0*o2*o3*o7 + 2*d0*o2*o4*o6 - 2*d0*o2 - 2*d1*d2*d3*d6 - 2*d1*d2*o0^2 - d1*d3^2*d8 - 2*d1*d3*d5*d6 - 2*d1*d3*d6*d8 - 2*d1*d3*d6*o2 - 2*d1*d3*d6*o5 - 2*d1*d3*d6*o8 - 2*d1*d3*d6 - 2*d1*d3*d8*o0 - 2*d1*d3*d8*o3 - 2*d1*d3*d8*o6 - 2*d1*d3*d8 - 2*d1*d3*o0*o2 + 2*d1*d3*o6*o8 - d1*d5*d6^2 - 2*d1*d5*d6*o0 - 2*d1*d5*d6*o3 - 2*d1*d5*d6*o6 - 2*d1*d5*d6 - d1*d5*o0^2 + d1*d5*o6^2 - 2*d1*d6*o0*o2 + 2*d1*d6*o3*o5 - d1*d8*o0^2 + d1*d8*o3^2 - d1*d8 - 6*d1*o0^2*o2 - 2*d1*o0^2*o5 - 2*d1*o0^2*o8 - 2*d1*o0^2 - 4*d1*o0*o2*o3 - 4*d1*o0*o2*o6 - 4*d1*o0*o2 + 2*d1*o0*o3*o8 + 2*d1*o0*o5*o6 + 2*d1*o2*o3*o6 - d2*d3^2*d7 - 2*d2*d3*d4*d6 - 2*d2*d3*d6*d7 - 2*d2*d3*d6*o1 - 2*d2*d3*d6*o4 - 2*d2*d3*d6*o7 - 2*d2*d3*d6 - 2*d2*d3*d7*o0 - 2*d2*d3*d7*o3 - 2*d2*d3*d7*o6 - 2*d2*d3*d7 - 2*d2*d3*o0*o1 + 2*d2*d3*o6*o7 - d2*d4*d6^2 - 2*d2*d4*d6*o0 - 2*d2*d4*d6*o3 - 2*d2*d4*d6*o6 - 2*d2*d4*d6 - d2*d4*o0^2 + d2*d4*o6^2 - 2*d2*d6*o0*o1 + 2*d2*d6*o3*o4 - d2*d7*o0^2 + d2*d7*o3^2 - d2*d7 - 6*d2*o0^2*o1 - 2*d2*o0^2*o4 - 2*d2*o0^2*o7 - 2*d2*o0^2 - 4*d2*o0*o1*o3 - 4*d2*o0*o1*o6 - 4*d2*o0*o1 + 2*d2*o0*o3*o7 + 2*d2*o0*o4*o6 - 2*d2*o0 + 2*d2*o1*o3*o6 - 2*d3*o2 + 2*d3*o6 - d4*d8 - d5*d7 - 2*d5*o0 - 2*d6*o2 + 2*d6*o4 - 2*d7*d8 - 2*d7*o2 + 2*d7*o3 - 2*d7*o5 - 2*d7*o8 - 2*d7 - 2*d8*o0 - 2*d8*o1 - 2*d8*o4 - 2*d8*o7 - 2*d8 - 8*o0*o2 + 2*o0*o3 - 4*o0*o5 + 2*o0*o7 - 4*o0*o8 - 4*o0 + 2*o1*o6 - 4*o2*o3 - 4*o2*o6 - 4*o2 + 2*o3*o8 + 2*o5*o6 + 2*o7*o8 := by
  have hq : quartic (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) =
      2 * (-d0^2*d4*d8 - d0^2*d5*d7 - 2*d0^2*o1*o2 - 2*d0*d1*d3*d8 - 2*d0*d1*d5*d6 - 4*d0*d1*o0*o2 - 2*d0*d2*d3*d7 - 2*d0*d2*d4*d6 - 4*d0*d2*o0*o1 - 2*d0*d3*d4*d8 - 2*d0*d3*d5*d7 - 2*d0*d3*d7*d8 - 2*d0*d3*d7*o2 - 2*d0*d3*d7*o5 - 2*d0*d3*d7*o8 - 2*d0*d3*d7 - 2*d0*d3*d8*o1 - 2*d0*d3*d8*o4 - 2*d0*d3*d8*o7 - 2*d0*d3*d8 - 2*d0*d3*o1*o2 + 2*d0*d3*o7*o8 - 2*d0*d4*d5*d6 - 2*d0*d4*d6*d8 - 2*d0*d4*d6*o2 - 2*d0*d4*d6*o5 - 2*d0*d4*d6*o8 - 2*d0*d4*d6 - 2*d0*d4*d8*o0 - 2*d0*d4*d8*o3 - 2*d0*d4*d8*o6 - 2*d0*d4*d8 - 2*d0*d4*o0*o2 + 2*d0*d4*o6*o8 - 2*d0*d5*d6*d7 - 2*d0*d5*d6*o1 - 2*d0*d5*d6*o4 - 2*d0*d5*d6*o7 - 2*d0*d5*d6 - 2*d0*d5*d7*o0 - 2*d0*d5*d7*o3 - 2*d0*d5*d7*o6 - 2*d0*d5*d7 - 2*d0*d5*o0*o1 + 2*d0*d5*o6*o7 - 2*d0*d6*o1*o2 + 2*d0*d6*o4*o5 - 2*d0*d7*o0*o2 + 2*d0*d7*o3*o5 - 2*d0*d8*o0*o1 + 2*d0*d8*o3*o4 - 12*d0*o0*o1*o2 - 4*d0*o0*o1*o5 - 4*d0*o0*o1*o8 - 4*d0*o0*o1 - 4*d0*o0*o2*o4 - 4*d0*o0*o2*o7 - 4*d0*o0*o2 + 2*d0*o0*o4*o8 + 2*d0*o0*o5*o7 - 4*d0*o1*o2*o3 - 4*d0*o1*o2*o6 - 4*d0*o1*o2 + 2*d0*o1*o3*o8 + 2*d0*o1*o5*o6 + 2*d0*o2*o3*o7 + 2*d0*o2*o4*o6 - 2*d0*o2 - 2*d1*d2*d3*d6 - 2*d1*d2*o0^2 - d1*d3^2*d8 - 2*d1*d3*d5*d6 - 2*d1*d3*d6*d8 - 2*d1*d3*d6*o2 - 2*d1*d3*d6*o5 - 2*d1*d3*d6*o8 - 2*d1*d3*d6 - 2*d1*d3*d8*o0 - 2*d1*d3*d8*o3 - 2*d1*d3*d8*o6 - 2*d1*d3*d8 - 2*d1*d3*o0*o2 + 2*d1*d3*o6*o8 - d1*d5*d6^2 - 2*d1*d5*d6*o0 - 2*d1*d5*d6*o3 - 2*d1*d5*d6*o6 - 2*d1*d5*d6 - d1*d5*o0^2 + d1*d5*o6^2 - 2*d1*d6*o0*o2 + 2*d1*d6*o3*o5 - d1*d8*o0^2 + d1*d8*o3^2 - d1*d8 - 6*d1*o0^2*o2 - 2*d1*o0^2*o5 - 2*d1*o0^2*o8 - 2*d1*o0^2 - 4*d1*o0*o2*o3 - 4*d1*o0*o2*o6 - 4*d1*o0*o2 + 2*d1*o0*o3*o8 + 2*d1*o0*o5*o6 + 2*d1*o2*o3*o6 - d2*d3^2*d7 - 2*d2*d3*d4*d6 - 2*d2*d3*d6*d7 - 2*d2*d3*d6*o1 - 2*d2*d3*d6*o4 - 2*d2*d3*d6*o7 - 2*d2*d3*d6 - 2*d2*d3*d7*o0 - 2*d2*d3*d7*o3 - 2*d2*d3*d7*o6 - 2*d2*d3*d7 - 2*d2*d3*o0*o1 + 2*d2*d3*o6*o7 - d2*d4*d6^2 - 2*d2*d4*d6*o0 - 2*d2*d4*d6*o3 - 2*d2*d4*d6*o6 - 2*d2*d4*d6 - d2*d4*o0^2 + d2*d4*o6^2 - 2*d2*d6*o0*o1 + 2*d2*d6*o3*o4 - d2*d7*o0^2 + d2*d7*o3^2 - d2*d7 - 6*d2*o0^2*o1 - 2*d2*o0^2*o4 - 2*d2*o0^2*o7 - 2*d2*o0^2 - 4*d2*o0*o1*o3 - 4*d2*o0*o1*o6 - 4*d2*o0*o1 + 2*d2*o0*o3*o7 + 2*d2*o0*o4*o6 - 2*d2*o0 + 2*d2*o1*o3*o6 - 2*d3*o2 + 2*d3*o6 - d4*d8 - d5*d7 - 2*d5*o0 - 2*d6*o2 + 2*d6*o4 - 2*d7*d8 - 2*d7*o2 + 2*d7*o3 - 2*d7*o5 - 2*d7*o8 - 2*d7 - 2*d8*o0 - 2*d8*o1 - 2*d8*o4 - 2*d8*o7 - 2*d8 - 8*o0*o2 + 2*o0*o3 - 4*o0*o5 + 2*o0*o7 - 4*o0*o8 - 4*o0 + 2*o1*o6 - 4*o2*o3 - 4*o2*o6 - 4*o2 + 2*o3*o8 + 2*o5*o6 + 2*o7*o8) := by
    rw [perm4_poly]
    simp [fullStarMatrix, quartic_add, quartic_four_affine]
    ring
  rw [quartic_eq_two_coeff] at hq
  linear_combination (1/2 : ℂ) * hq

theorem full_star_xyz_zero (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    -2*(d0*d1*d5 + d0*d1*d8 + 2*d0*d1*o2 + d0*d2*d4 + d0*d2*d7 + 2*d0*d2*o1 + d0*d4*d5 + d0*d4*d8 + 2*d0*d4*o2 + d0*d4*o5 + d0*d4 + d0*d5*d7 + 2*d0*d5*o1 + d0*d5*o4 + 2*d0*d5 + d0*d7*d8 + 2*d0*d7*o2 + d0*d7*o8 + d0*d7 + 2*d0*d8*o1 + d0*d8*o7 + d0*d8 + 4*d0*o1*o2 + d0*o1*o5 + d0*o1*o8 + 2*d0*o1 + d0*o2*o4 + d0*o2*o7 + 3*d0*o2 - d0*o4*o5 - d0*o4*o8 - d0*o5*o7 - d0*o7*o8 + d1*d2*d3 + d1*d2*d6 + 2*d1*d2*o0 + d1*d3*d5 + d1*d3*d8 + 2*d1*d3*o2 + d1*d3*o5 + d1*d3 + d1*d5*d6 + 2*d1*d5*o0 + d1*d5*o3 + d1*d5 + d1*d6*d8 + 2*d1*d6*o2 + d1*d6*o8 + d1*d6 + 2*d1*d8*o0 + d1*d8*o6 + 2*d1*d8 + 4*d1*o0*o2 + d1*o0*o5 + d1*o0*o8 + 2*d1*o0 + d1*o2*o3 + d1*o2*o6 + 3*d1*o2 - d1*o3*o5 - d1*o3*o8 - d1*o5*o6 - d1*o6*o8 + d2*d3*d4 + d2*d3*d7 + 2*d2*d3*o1 + d2*d3*o4 + 2*d2*d3 + d2*d4*d6 + 2*d2*d4*o0 + d2*d4*o3 + d2*d4 + d2*d6*d7 + 2*d2*d6*o1 + d2*d6*o7 + d2*d6 + 2*d2*d7*o0 + d2*d7*o6 + 2*d2*d7 + 4*d2*o0*o1 + d2*o0*o4 + d2*o0*o7 + 3*d2*o0 + d2*o1*o3 + d2*o1*o6 + 3*d2*o1 - d2*o3*o4 - d2*o3*o7 - d2*o4*o6 - d2*o6*o7 + d2 + d3*d4*d8 + d3*d5*d7 + 2*d3*d5 + d3*d7*d8 + d3*d7*o2 + d3*d7*o5 + d3*d7*o8 + d3*d8*o1 + d3*d8*o4 + d3*d8*o7 + 2*d3*d8 + d3*o1*o2 + 3*d3*o2 + 2*d3*o5 - d3*o7*o8 - d3*o7 + d3*o8 + d3 + d4*d5*d6 + d4*d6*d8 + d4*d6*o2 + d4*d6*o5 + d4*d6*o8 + d4*d8*o0 + d4*d8*o3 + d4*d8*o6 + 2*d4*d8 + d4*o0*o2 + d4*o2 - d4*o6*o8 - d4*o6 + d5*d6*d7 + d5*d6*o1 + d5*d6*o4 + d5*d6*o7 + 2*d5*d6 + d5*d7*o0 + d5*d7*o3 + d5*d7*o6 + 2*d5*d7 + d5*o0*o1 + 3*d5*o0 + d5*o1 + 2*d5*o3 - d5*o6*o7 + d5*o6 + 3*d5 + d6*o1*o2 + d6*o2 - d6*o4*o5 - d6*o4 + 2*d7*d8 + d7*o0*o2 + 3*d7*o2 - d7*o3*o5 - d7*o3 + d7*o5 + 2*d7*o8 + d7 + d8*o0*o1 + d8*o0 + 3*d8*o1 - d8*o3*o4 + d8*o4 + 2*d8*o7 + 3*d8 + 6*o0*o1*o2 + 2*o0*o1*o5 + 2*o0*o1*o8 + 2*o0*o2*o4 + 2*o0*o2*o7 + 6*o0*o2 - o0*o4*o8 - o0*o4 - o0*o5*o7 + o0*o5 - o0*o7 + 2*o0*o8 + o0 + 2*o1*o2*o3 + 2*o1*o2*o6 + 6*o1*o2 - o1*o3*o8 - o1*o3 - o1*o5*o6 + 2*o1*o5 - o1*o6 + o1*o8 + o1 - o2*o3*o7 + o2*o3 - o2*o4*o6 + 2*o2*o4 + 2*o2*o6 + o2*o7 + 5*o2 - 2*o3*o5 - o3*o8 - o3 - o4*o8 - o4 - o5*o6 - o5*o7 + o5 - o6 - 2*o7*o8 - o7 + o8 + 2) = 0 := by
  rw [← full_star_xyz_coefficient d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8, h, coeff_xyz_via_deriv]
  exact triple_nat 24

theorem full_star_xxyz_zero (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    -d0^2*d4*d8 - d0^2*d5*d7 - 2*d0^2*o1*o2 - 2*d0*d1*d3*d8 - 2*d0*d1*d5*d6 - 4*d0*d1*o0*o2 - 2*d0*d2*d3*d7 - 2*d0*d2*d4*d6 - 4*d0*d2*o0*o1 - 2*d0*d3*d4*d8 - 2*d0*d3*d5*d7 - 2*d0*d3*d7*d8 - 2*d0*d3*d7*o2 - 2*d0*d3*d7*o5 - 2*d0*d3*d7*o8 - 2*d0*d3*d7 - 2*d0*d3*d8*o1 - 2*d0*d3*d8*o4 - 2*d0*d3*d8*o7 - 2*d0*d3*d8 - 2*d0*d3*o1*o2 + 2*d0*d3*o7*o8 - 2*d0*d4*d5*d6 - 2*d0*d4*d6*d8 - 2*d0*d4*d6*o2 - 2*d0*d4*d6*o5 - 2*d0*d4*d6*o8 - 2*d0*d4*d6 - 2*d0*d4*d8*o0 - 2*d0*d4*d8*o3 - 2*d0*d4*d8*o6 - 2*d0*d4*d8 - 2*d0*d4*o0*o2 + 2*d0*d4*o6*o8 - 2*d0*d5*d6*d7 - 2*d0*d5*d6*o1 - 2*d0*d5*d6*o4 - 2*d0*d5*d6*o7 - 2*d0*d5*d6 - 2*d0*d5*d7*o0 - 2*d0*d5*d7*o3 - 2*d0*d5*d7*o6 - 2*d0*d5*d7 - 2*d0*d5*o0*o1 + 2*d0*d5*o6*o7 - 2*d0*d6*o1*o2 + 2*d0*d6*o4*o5 - 2*d0*d7*o0*o2 + 2*d0*d7*o3*o5 - 2*d0*d8*o0*o1 + 2*d0*d8*o3*o4 - 12*d0*o0*o1*o2 - 4*d0*o0*o1*o5 - 4*d0*o0*o1*o8 - 4*d0*o0*o1 - 4*d0*o0*o2*o4 - 4*d0*o0*o2*o7 - 4*d0*o0*o2 + 2*d0*o0*o4*o8 + 2*d0*o0*o5*o7 - 4*d0*o1*o2*o3 - 4*d0*o1*o2*o6 - 4*d0*o1*o2 + 2*d0*o1*o3*o8 + 2*d0*o1*o5*o6 + 2*d0*o2*o3*o7 + 2*d0*o2*o4*o6 - 2*d0*o2 - 2*d1*d2*d3*d6 - 2*d1*d2*o0^2 - d1*d3^2*d8 - 2*d1*d3*d5*d6 - 2*d1*d3*d6*d8 - 2*d1*d3*d6*o2 - 2*d1*d3*d6*o5 - 2*d1*d3*d6*o8 - 2*d1*d3*d6 - 2*d1*d3*d8*o0 - 2*d1*d3*d8*o3 - 2*d1*d3*d8*o6 - 2*d1*d3*d8 - 2*d1*d3*o0*o2 + 2*d1*d3*o6*o8 - d1*d5*d6^2 - 2*d1*d5*d6*o0 - 2*d1*d5*d6*o3 - 2*d1*d5*d6*o6 - 2*d1*d5*d6 - d1*d5*o0^2 + d1*d5*o6^2 - 2*d1*d6*o0*o2 + 2*d1*d6*o3*o5 - d1*d8*o0^2 + d1*d8*o3^2 - d1*d8 - 6*d1*o0^2*o2 - 2*d1*o0^2*o5 - 2*d1*o0^2*o8 - 2*d1*o0^2 - 4*d1*o0*o2*o3 - 4*d1*o0*o2*o6 - 4*d1*o0*o2 + 2*d1*o0*o3*o8 + 2*d1*o0*o5*o6 + 2*d1*o2*o3*o6 - d2*d3^2*d7 - 2*d2*d3*d4*d6 - 2*d2*d3*d6*d7 - 2*d2*d3*d6*o1 - 2*d2*d3*d6*o4 - 2*d2*d3*d6*o7 - 2*d2*d3*d6 - 2*d2*d3*d7*o0 - 2*d2*d3*d7*o3 - 2*d2*d3*d7*o6 - 2*d2*d3*d7 - 2*d2*d3*o0*o1 + 2*d2*d3*o6*o7 - d2*d4*d6^2 - 2*d2*d4*d6*o0 - 2*d2*d4*d6*o3 - 2*d2*d4*d6*o6 - 2*d2*d4*d6 - d2*d4*o0^2 + d2*d4*o6^2 - 2*d2*d6*o0*o1 + 2*d2*d6*o3*o4 - d2*d7*o0^2 + d2*d7*o3^2 - d2*d7 - 6*d2*o0^2*o1 - 2*d2*o0^2*o4 - 2*d2*o0^2*o7 - 2*d2*o0^2 - 4*d2*o0*o1*o3 - 4*d2*o0*o1*o6 - 4*d2*o0*o1 + 2*d2*o0*o3*o7 + 2*d2*o0*o4*o6 - 2*d2*o0 + 2*d2*o1*o3*o6 - 2*d3*o2 + 2*d3*o6 - d4*d8 - d5*d7 - 2*d5*o0 - 2*d6*o2 + 2*d6*o4 - 2*d7*d8 - 2*d7*o2 + 2*d7*o3 - 2*d7*o5 - 2*d7*o8 - 2*d7 - 2*d8*o0 - 2*d8*o1 - 2*d8*o4 - 2*d8*o7 - 2*d8 - 8*o0*o2 + 2*o0*o3 - 4*o0*o5 + 2*o0*o7 - 4*o0*o8 - 4*o0 + 2*o1*o6 - 4*o2*o3 - 4*o2*o6 - 4*o2 + 2*o3*o8 + 2*o5*o6 + 2*o7*o8 = 0 := by
  have hq := quartic_eq_two_coeff (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8))
  rw [full_star_xxyz_coefficient, h] at hq
  have hz := quartic_nat 24
  linear_combination (1/2 : ℂ) * hz - (1/2 : ℂ) * hq

end PEqualNP.Outside.L_gct_231_aux.Coeff
